import Miri.Verification.CheckedBodyVCGen
import MiriTests.ControlFlow.Transitions
import Init.Internal.Order.While

namespace MiriTests.Verification.WholeBodyWP

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.MIR Miri.Memory
open Miri.TreeBorrows Miri.Verification Miri.Verification.WholeBodyWP Std.WP

set_option autoImplicit false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-! Exercise both the named CFG nodes and whole-body transfer. The fixture
driver below offers a looping branch and a failing protected write. -/

private def branchingBody : Body :=
  { ControlTests.fixtureBody with basicBlocks :=
    #[ControlTests.block #[] ControlTests.switch.kind,
      ControlTests.block #[⟨ControlTests.source, .Nop⟩] (.Goto 1 #[])] }

private def cfg := BodyCFG.compile branchingBody

example : (cfg.equations.map fun equation => (equation.pc, equation.targets)) =
    #[(⟨0, 0⟩, #[⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩]),
      (⟨1, 0⟩, #[⟨1, 1⟩]), (⟨1, 1⟩, #[⟨1, 0⟩])] := by cbv

/-- The forward edge and statement suffix decrease the rank. The back edge
does not, so it stays recursive. -/
example : cfg.rankAt ⟨1, 0⟩ < cfg.rankAt ⟨0, 0⟩ ∧
    cfg.rankAt ⟨1, 1⟩ < cfg.rankAt ⟨1, 0⟩ := by cbv

/-- The out-of-range block is absent, while an excessive statement index
selects the terminator just as it does in the driver. -/
example : cfg.lookup ⟨7, 0⟩ = none ∧ cfg.equationAt ⟨1, 9⟩ = none ∧
    cfg.lookup ⟨1, 9⟩ =
      some (.terminator ⟨ControlTests.source, .Goto 1 #[]⟩) := by cbv

private def child : BorTag := ⟨2, by decide⟩
private def size := Size.ofBytes 1
private def initialTree := BorrowTree.new BorTag.one size
private def permissions := DedupRangeMap.new size (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
private def protectors := ({} : ProtectedTags).insert child .StrongProtector
private def protectedTree := (initialTree.newChild Size.ZERO
  (.concrete BorTag.one) child permissions .Frozen true).tree
private def failedWrite := protectedTree.performBorrowAccessRange (.concrete BorTag.one)
  Size.ZERO size .Write protectors .VisitChildrenOfAccessed
private def writeError := PlaceMachine.treeError true failedWrite.status

private inductive Phase where
  | start | ready | written (tree : BorrowTree)

private def writeStep (tryWrite : Bool) : Phase → StepResult Phase Bool
  | .start => (.ready, .ok true)
  | .ready => if tryWrite then (.written failedWrite.tree, .error writeError)
      else (.ready, .ok true)
  | .written tree => (.written tree, .ok false)

private def writeRule : Rule writeStep where
  pre choice post failure state := InstructionWP.resultPre post failure (writeStep choice state)
  exact _ _ _ _ := Iff.rfl

private def depth (_ : Phase) : Nat := 1
private def permitted (_ : Phase) (_ : Bool) : Prop := True
private def noExit (_ : Exit) (_ : Phase) : Prop := False
private def noError (_ : StepError) (_ : Phase) : Prop := False

set_option maxRecDepth 65536 in
set_option cbv.maxSteps 1000000 in
private theorem failedWrite_status : failedWrite.status =
    .AccessFailure ⟨0, 1⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen)) := by
  cbv

private def retainedWriteError (error : StepError) : Phase → Prop
  | .written tree => error = PlaceMachine.treeError true
        (.AccessFailure ⟨0, 1⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen))) ∧
      tree = failedWrite.tree
  | _ => False

/-- The same symbolic loop condition admits the diverging choice and passes
the failing choice's exact tree and typed error to the client. -/
example : solve writeRule depth permitted 1 noExit retainedWriteError .start := by
  let inLoop : Phase → Prop
    | .start | .ready => True
    | .written _ => False
  apply solve_of_closed writeRule depth permitted 1 noExit retainedWriteError inLoop _ .start trivial
  intro state valid
  cases state with
  | start =>
    exact fun _ _ => trivial
  | ready =>
    intro choice _
    cases choice
    · trivial
    · exact ⟨congrArg (PlaceMachine.treeError true) failedWrite_status, rfl⟩
  | written _ =>
    exact valid.elim

/-- Rejecting errors fails because there is a permitted failing execution
after the first step, even though a different choice can loop forever. -/
example : ¬ solve writeRule depth permitted 1 noExit noError .start := by
  intro checked
  have outcomes := (solve_iff writeRule depth permitted 1 noExit noError .start).mp checked
  have finished : Finishes writeStep depth permitted 1 .start (.written failedWrite.tree)
      (.error writeError) :=
    .next (choice := false) (by decide) trivial rfl (.failed (choice := true) (by decide) trivial rfl)
  exact outcomes _ _ finished

/-- Disallowing the failed write leaves only the back edge. Partial
correctness requires no fabricated exit or finite unroll bound. -/
example : solve writeRule depth (fun _ choice => choice = false) 1 noExit noError .start := by
  let inLoop : Phase → Prop
    | .start | .ready => True
    | .written _ => False
  apply solve_of_closed writeRule depth (fun _ choice => choice = false) 1 noExit noError
    inLoop _ .start trivial
  intro state valid
  cases state with
  | start =>
    exact fun _ _ => trivial
  | ready =>
    rintro _ rfl
    trivial
  | written _ =>
    exact valid.elim

/-- A scope exit takes precedence over another interpreter iteration.
The same state can instead take the driver's stopped branch at depth zero. -/
example : solve writeRule (fun _ => 0) permitted 1
      (fun exit _ => exit = .scopeExit) noError (.written failedWrite.tree) ∧
    solve writeRule (fun _ => 0) permitted 0
      (fun exit _ => exit = .stopped) noError (.written failedWrite.tree) := by
  constructor
  · apply (solve_unfold ..).mpr
    exact rfl
  · apply (solve_unfold ..).mpr
    exact fun _ _ => rfl

section Production

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host

/-- An instruction that replaces the current frame at the same depth can
expose an error in the entered body. The scope test must follow the actual
driver successor until the original depth is left. -/
example (config : Config) (limits : ExecutionMachine.Limits) (body : Body)
    (before entered failed : State) (error : StepError)
    (sameDepth : before.stack.frames.size = entered.stack.frames.size)
    (enter : Step.step (ExecutionMachine.stepHooks config limits) () before =
      (entered, .ok true))
    (fail : Step.step (ExecutionMachine.stepHooks config limits) () entered =
      (failed, .error error))
    (post : Exit → State → Prop) (onError : StepError → State → Prop)
    (checked : wp (BodyVCGen.run config limits body (fun _ _ => True)) post onError before) :
    onError error failed := by
  have complete := (bodyPre_iff config limits body (fun _ _ => True) post onError before).mp checked
  exact complete.2 failed (.error error)
    (.next (choice := ()) (Nat.le_refl _) trivial enter
      (.failed (choice := ()) (Nat.le_of_eq sameDepth) trivial fail))

end Production

set_option experimental.vcgen true in
/-- Choice-specific metadata can fail before an inner step. The generated
failure VC receives the unmodified outer state for that permitted choice. -/
example {K U O X Host : Type} [DecidableEq K]
    (configs : Bool → Except StepError
      (ExecutionMachine.Config K (ExecutionStateTransport.Inner U) Bool O X Host))
    (limits : ExecutionMachine.Limits) (program : BodyVCGen.LoadedProgram)
    (before : MachineHooks.State K (ExecutionStateTransport.Outer U))
    (error : StepError) (failed : configs true = .error error)
    (entered : CheckedBodyVCGen.entryMatches program before) :
    Triple (CheckedBodyVCGen.run configs limits program (fun _ choice => choice = true))
      (· = before) (fun _ _ => False) (fun e state => e = error ∧ state = before) := by
  vcgen
  rename_i state same
  subst state
  refine ⟨entered, ?_⟩
  rw [CheckedBodyVCGen.controlPre_unfold]
  simp only [Nat.le_refl, ↓reduceIte]
  intro choice selected
  subst choice
  simp [CheckedBodyVCGen.choicePre, failed]

end MiriTests.Verification.WholeBodyWP

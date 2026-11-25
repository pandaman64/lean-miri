import Generated
import Miri.Verification.CalleeSummaryWP

/-! The exported call to `update` and its post-cleanup caller continuation. -/
namespace CalleeSummaryExample

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification
open Miri.Verification.WholeBodyWP GeneratedBodySafety

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "State" => MachineHooks.State K U
local notation "Limits" => ExecutionMachine.Limits

private def noFailure (_ : StepError) (_ : State) := False
private def success (exit : Exit) (_ : State) : Prop := exit = .scopeExit
private def graph (program : BodyVCGen.LoadedProgram) := BodyCFG.compileProgram program.bodies

private def storedByte (state : State) (allocation : AllocId) (value : UInt8) : Prop :=
  ∃ live, state.machine.memory.live[allocation]? = some live ∧
    live.allocation.readScalar ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 1)) false =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 value))

/-- The caller storage contains the callee's write and the distinct return
value. The callee's argument protector is no longer registered. -/
def returned (caller : LocalsIdentity) (allocation : AllocId) (tag : BorTag)
    (after : State) : Prop :=
  CalleeSummaryWP.resumedAt caller 1 after ∧
  (∃ frame slot root, after.stack.currentFrame? = some frame ∧
    (frame.getLocalOperand 3).toOption = some (.indirect slot) ∧
    slot.ptr.provenance = some (.concrete allocation root) ∧ storedByte after allocation 42 ∧
    ((frame.getLocalOperand 4).toOption = some (.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 7)))) ∨
      ∃ place dest destTag, (frame.getLocalOperand 4).toOption = some (.indirect place) ∧
        place.ptr.provenance = some (.concrete dest destTag) ∧ storedByte after dest 7)) ∧
  (∃ tracker, after.machine.borrowTracker = some tracker ∧
    tracker.global.protectedTags.get tag = none)

def argumentProtected (allocation : AllocId) (tag : BorTag) (state : State) : Prop :=
  (∃ frame borrow, state.stack.currentFrame? = some frame ∧
    frame.extra.borrowTracker = some borrow ∧ (allocation, tag) ∈ borrow.protectedTags) ∧
  (∃ tracker, state.machine.borrowTracker = some tracker ∧
    tracker.global.protectedTags.get tag = some .StrongProtector)

/-- Local domain for an emitted row. The active equation is checked before
using its reduced precondition. -/
def row (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (reduced : GeneratedBodyVC.ReducedNode config limits) (next : State → Prop)
    (before : State) : Prop :=
  ∃ identity cfg eq,
    (graph program).graphFor before = some (identity, cfg) ∧
    cfg.equationFor before = some eq ∧
    (transferTable config limits)[(identity.index, eq.pc.block, eq.pc.statementIndex)]? =
      some reduced ∧
    reduced.node = eq.node ∧
    reduced.pre () (fun more after => more = true ∧ next after) noFailure before

private theorem row_step (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (reduced : GeneratedBodyVC.ReducedNode config limits) (next : State → Prop)
    (before : State) (checked : row config limits program reduced next before) :
    ∃ after, ExecutionMachine.step config limits () before = (after, .ok true) ∧ next after := by
  obtain ⟨identity, cfg, eq, active, selected, found, same, obligation⟩ := checked
  rw [← GeneratedBodyVC.rule_pre_of_row config limits (graph program) (transferTable config limits)
    () (fun more after => more = true ∧ next after) noFailure before active selected found same] at obligation
  have result := ((GeneratedBodyVC.rule config limits (graph program)
    (transferTable config limits)).exact () _ _ _).mp obligation
  rcases ran : ExecutionMachine.step config limits () before with ⟨after, outcome⟩
  rw [ran] at result
  cases outcome with
  | error => exact False.elim result
  | ok more =>
    rcases result with ⟨rfl, observed⟩
    exact ⟨after, rfl, observed⟩

private theorem advance (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (depth : Nat) (post : Exit → State → Prop) (before after : State)
    (live : depth ≤ before.stack.frames.size)
    (ran : ExecutionMachine.step config limits () before = (after, .ok true))
    (continuation : catalogControlPre config limits (graph program) (fun _ _ => True)
      depth post noFailure after) :
    catalogControlPre config limits (graph program) (fun _ _ => True) depth post noFailure before := by
  rw [catalogControlPre_unfold, ite_eq_left live]
  intro choice _
  cases choice
  rw [BodyCFG.programTablePre_iff]
  rw [show Step.step (ExecutionMachine.stepHooks config limits) () _ = _ from ran]
  exact continuation

/-- The active call and the three callee rows are the local obligations.
The intermediate predicates can carry a caller's own frame and memory facts. -/
structure CallDomain (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (caller : LocalsIdentity) (allocation : AllocId) (tag : BorTag) (atCall : State) where
  readyForResult : State → Prop
  readyForReturn : State → Prop
  enter : row config limits program (transfer_0_bb0_7 config limits)
    (fun entered =>
      atCall.stack.frames.size + 1 ≤ entered.stack.frames.size ∧
      argumentProtected allocation tag entered ∧
      row config limits program (transfer_1_bb0_0 config limits) readyForResult entered) atCall
  assignResult : ∀ state, readyForResult state →
    atCall.stack.frames.size + 1 ≤ state.stack.frames.size ∧
    row config limits program (transfer_1_bb0_1 config limits) readyForReturn state
  finish : ∀ state, readyForReturn state →
    atCall.stack.frames.size + 1 ≤ state.stack.frames.size ∧
    row config limits program (transfer_1_bb0_2 config limits)
      (fun after => after.stack.frames.size < atCall.stack.frames.size + 1 ∧
        returned caller allocation tag after) state

/-- The call establishes the update contract on the actual resumed caller state. -/
theorem update_summary
    (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (caller : LocalsIdentity) (allocation : AllocId) (tag : BorTag) (atCall : State)
    (domain : CallDomain config limits program caller allocation tag atCall) :
    CalleeSummaryWP.callPre config limits (graph program) (fun _ _ => True)
      (fun exit => match exit with
        | .scopeExit => returned caller allocation tag
        | .stopped => success .stopped) noFailure atCall := by
  unfold CalleeSummaryWP.callPre
  intro choice _
  cases choice
  obtain ⟨entered, ran, depthEntry, _, write⟩ := row_step _ _ _ _ _ _ domain.enter
  rw [BodyCFG.programTablePre_iff]
  rw [show Step.step (ExecutionMachine.stepHooks config limits) () _ = _ from ran]
  change catalogControlPre config limits (graph program) (fun _ _ => True)
    (atCall.stack.frames.size + 1) _ noFailure entered
  obtain ⟨written, ranWrite, resultReady⟩ := row_step _ _ _ _ _ _ write
  refine advance _ _ _ _ _ _ _ depthEntry ranWrite ?_
  obtain ⟨depthWrite, saveResult⟩ := domain.assignResult written resultReady
  obtain ⟨withResult, ranResult, returnReady⟩ := row_step _ _ _ _ _ _ saveResult
  refine advance _ _ _ _ _ _ _ depthWrite ranResult ?_
  obtain ⟨depthResult, returnToCaller⟩ := domain.finish withResult returnReady
  obtain ⟨resumed, ranReturn, exited, observed⟩ := row_step _ _ _ _ _ _ returnToCaller
  refine advance _ _ _ _ _ _ _ depthResult ranReturn ?_
  rw [catalogControlPre_unfold, ite_eq_right (Nat.not_le_of_lt exited)]
  exact observed

/-- The caller proof reuses the update contract and takes its continuation
from the actual state after the callee's return. -/
theorem caller_from_summary (config : Config) (limits : Limits)
    (program : BodyVCGen.LoadedProgram) (atCall : State)
    (caller : LocalsIdentity) (allocation : AllocId) (tag : BorTag)
    (summary : CalleeSummaryWP.callPre config limits (graph program) (fun _ _ => True)
      (fun exit => match exit with
        | .scopeExit => returned caller allocation tag
        | .stopped => success .stopped) noFailure atCall)
    (resume : ∀ after, returned caller allocation tag after →
      GeneratedBodyVC.controlPre config limits (graph program) (transferTable config limits)
        (fun _ _ => True) atCall.stack.frames.size success noFailure after) :
    GeneratedBodyVC.controlPre config limits (graph program) (transferTable config limits)
      (fun _ _ => True) atCall.stack.frames.size success noFailure atCall := by
  rw [GeneratedBodyVC.controlPre_eq]
  refine CalleeSummaryWP.callerPre_of_summary config limits (graph program) _ _ _ _
    (returned caller allocation tag) atCall (Nat.le_refl _) ?_ ?_
  · exact summary
  · intro after observed
    simpa only [GeneratedBodyVC.controlPre_eq] using resume after observed

/-- Apply the composed proof to the generated caller VC at the actual
exported call site. The source program must load through the generated file. -/
theorem imported_call
    (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (origin : loaded = .ok program) (atCall : State)
    (caller : LocalsIdentity) (allocation : AllocId) (tag : BorTag)
    (domain : CallDomain config limits program caller allocation tag atCall)
    (resume : ∀ after, returned caller allocation tag after →
      GeneratedBodyVC.controlPre config limits (graph program) (transferTable config limits)
        (fun _ _ => True) atCall.stack.frames.size success noFailure after) :
    match loaded with
    | .error _ => False
    | .ok source => GeneratedBodyVC.controlPre config limits (graph source)
        (transferTable config limits) (fun _ _ => True) atCall.stack.frames.size success noFailure atCall := by
  rw [origin]
  exact caller_from_summary config limits program atCall caller allocation tag
    (update_summary config limits program caller allocation tag atCall domain) resume

open Lean Elab Command in
run_cmd do
  for name in #[``update_summary, ``caller_from_summary, ``imported_call] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms imported_call

end CalleeSummaryExample

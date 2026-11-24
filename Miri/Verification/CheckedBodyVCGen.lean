import Miri.Verification.BodyVCGen
import Miri.Input.EvalExecutable

/-! Whole-body VCs for the executable loop's fallible, choice-specific core
configurations. The scope is the prepared frame's core execution. -/
namespace Miri.Verification.CheckedBodyVCGen

open Miri.Interpreter Miri.Input Std.WP

variable {K U C O X Host : Type}
local notation "State" => MachineHooks.State K (ExecutionStateTransport.Outer U)
local notation "Config" => ExecutionMachine.Config K (ExecutionStateTransport.Inner U) C O X Host
local notation "Configs" => C → Except StepError Config
local notation "Post" => WholeBodyWP.Exit → State → Prop
local notation "Failure" => StepError → State → Prop

/-- Exact core-step boundary, including metadata failure before entering the
inner interpreter. The failed metadata lookup leaves the outer state intact. -/
def step [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (choice : C) (before : State) : StepResult State Bool :=
  match configs choice with
  | .error error => (before, .error error)
  | .ok config => ExecutionStateTransport.step config limits choice before

/-- Select the configuration only after the choice has been permitted. On
both inner outcomes transport the actual successor back to the outer state. -/
def choicePre [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (graph : BodyCFG.CompiledProgram) (choice : C)
    (post : Bool → State → Prop) (failure : Failure) (before : State) : Prop :=
  match configs choice with
  | .error error => failure error before
  | .ok config =>
    BodyCFG.programTablePre config limits graph choice
      (fun more after => post more (ExecutionStateTransport.outward after))
      (fun error after => failure error (ExecutionStateTransport.outward after))
      (ExecutionStateTransport.inward before)

theorem choicePre_iff [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (graph : BodyCFG.CompiledProgram) (choice : C)
    (post : Bool → State → Prop) (failure : Failure) (before : State) :
    choicePre configs limits graph choice post failure before ↔
      InstructionWP.resultPre post failure (step configs limits choice before) := by
  unfold choicePre step
  cases selected : configs choice with
  | error => rfl
  | ok config =>
    dsimp only
    rw [BodyCFG.programTablePre_iff]
    unfold ExecutionStateTransport.step ExecutionMachine.step
    rcases Step.step (ExecutionMachine.stepHooks config limits) choice
      (ExecutionStateTransport.inward before) with ⟨after, result⟩
    cases result <;> rfl

private def rule [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (graph : BodyCFG.CompiledProgram) : WholeBodyWP.Rule (step configs limits) where
  pre := choicePre configs limits graph
  exact := choicePre_iff configs limits graph

def entryMatches (program : BodyVCGen.LoadedProgram) (before : State) : Prop :=
  WholeBodyWP.entryMatchesLoaded program.root (ExecutionStateTransport.inward before)

def controlPre [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (graph : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Post) (failure : Failure) (before : State) : Prop :=
  WholeBodyWP.eliminate (rule configs limits graph) (fun state => state.stack.frames.size)
    allowed depth post failure (fun state => BodyCFG.programRank graph (ExecutionStateTransport.inward state))
    before

/-- Expose one continuing equation, keeping the scoped exact continuation
shared across all permitted configurations. -/
theorem controlPre_unfold [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (graph : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Post) (failure : Failure) (before : State) :
    controlPre configs limits graph allowed depth post failure before ↔
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          choicePre configs limits graph choice
            (fun more after => if more then controlPre configs limits graph allowed depth post failure after
              else post .stopped after) failure before
      else post .scopeExit before := by
  unfold controlPre
  simp only [WholeBodyWP.eliminate_iff]
  exact WholeBodyWP.solve_unfold _ _ _ _ _ _ _

def pre [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → C → Prop)
    (post : Post) (failure : Failure) (before : State) : Prop :=
  entryMatches program before ∧ controlPre configs limits (BodyCFG.compileProgram program.bodies)
    allowed before.stack.frames.size post failure before

theorem pre_iff [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → C → Prop)
    (post : Post) (failure : Failure) (before : State) :
    pre configs limits program allowed post failure before ↔
      entryMatches program before ∧
        ∀ after result, WholeBodyWP.Finishes (step configs limits)
          (fun state => state.stack.frames.size) allowed before.stack.frames.size before after result →
          InstructionWP.resultPre post failure (after, result) :=
  and_congr_right fun _ => (WholeBodyWP.eliminate_iff _ _ _ _ _ _ _ _).trans
    (WholeBodyWP.solve_iff _ _ _ _ _ _ _)

inductive Run (configs : Configs) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → C → Prop) where
  | root

def run (configs : Configs) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → C → Prop) :
    Run configs limits program allowed := .root

instance [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → C → Prop) :
    WP (Run configs limits program allowed) WholeBodyWP.Exit (State → Prop) Failure where
  wpTrans _ := ⟨pre configs limits program allowed⟩
  wp_trans_monotone := by
    intro _ post post' failure failure' errorMono postMono before checked
    apply (pre_iff configs limits program allowed post' failure' before).mpr
    obtain ⟨entered, outcomes⟩ := (pre_iff configs limits program allowed post failure before).mp checked
    refine ⟨entered, fun after result terminated => ?_⟩
    have actual := outcomes after result terminated
    cases result with
    | error error => exact errorMono error after actual
    | ok exit => exact postMono exit after actual

@[spec] theorem spec_run [DecidableEq K] (configs : Configs) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → C → Prop)
    (post : Post) (failure : Failure) :
    Triple (run configs limits program allowed)
      (pre configs limits program allowed post failure) post failure :=
  Triple.iff.mpr fun _ checked => checked

/-- Connect the adapter to the stock executable loop projection. Outer
scheduler steps and stack-empty callbacks belong to the enclosing loop. -/
theorem step_eq_loopChecked_coreStep {Os R P H D O Aff B Host C ClockHost : Type}
    (configs : C → Except StepError (EvalExecutable.Core Os R P H D O Aff B Host C ClockHost))
    (limits : ExecutionMachine.Limits)
    (main : MainMachine.Hooks (EvalExecutable.U Os R P H D O Aff B Host) C O Miri.ABI.ExternAbi
      (Miri.ABI.FnAbi Miri.MIR.TyId) (Miri.ABI.ArgAbi Miri.MIR.TyId) Aff P)
    (base : RunLoopHooks (EvalWorld.State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks Miri.Memory.MiriMemoryKind
      (EvalExecutable.U Os R P H D O Aff B Host)) :
    step configs limits = (EvalExecutable.loopChecked configs limits main base scheduler).coreStep := by
  funext choice state
  simp only [step, EvalExecutable.loopChecked]
  cases configs choice <;> rfl

end Miri.Verification.CheckedBodyVCGen

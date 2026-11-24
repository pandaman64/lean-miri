import Miri.Interpreter.ExecutionMachine
import Miri.Verification.StepWP
import Lean

namespace DuplicatePrefix.NestedGuardDriver

open Miri.Interpreter Miri.Memory

variable {K U Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U

private def nextClock : Clock.Monotonic Host → Clock.Monotonic Host
  | .host instant => .host instant
  | .virtual ticks => .virtual (BitVec.ofNat 128 (ticks.toNat + 5000))

private theorem tickUnchecked (clock : Clock.Monotonic Host) :
    clock.tick false = .ok (nextClock clock) := by
  cases clock <;> rfl

open Lean Elab Tactic in
elab "unfold_terminator_control" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".TerminatorMachine.updateControl" then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one terminator counter-update helper"

def nextTerminatorUser (hooks : TerminatorMachine.Hooks K U Host) (user : U) : U :=
  let initial := hooks.getControl user
  let counted := {initial with basicBlockCount := initial.basicBlockCount + 1}
  let aged := {counted with sinceGc := counted.sinceGc + 1}
  hooks.setControl {aged with monotonic := nextClock aged.monotonic}
    (hooks.setControl aged (hooks.setControl counted user))

/-- The actual driver prefix for fixed scheduling and disabled provenance
GC. It advances the source counters and clock, ignoring the choice callback.
Neither a successful terminator step nor a successful preemption is assumed. -/
theorem beforeTerminatorFixed
    (hooks : TerminatorMachine.Hooks K U Host) (choice : MachineHooks.M K U Bool)
    (before : State)
    (lens : ∀ control user, hooks.getControl (hooks.setControl control user) = control)
    (fixed : before.machine.threads.fixedScheduling = true)
    (unchecked : (hooks.getControl before.machine.user).checkedArithmetic = false)
    (noGc : (hooks.getControl before.machine.user).gcInterval = 0) :
    let user := nextTerminatorUser hooks before.machine.user
    TerminatorMachine.beforeTerminatorWithChoice hooks choice before =
      .ok () {before with machine := {before.machine with user}} := by
  unfold TerminatorMachine.beforeTerminatorWithChoice
  unfold_terminator_control
  simp [TerminatorMachine.maybePreemptWithChoice, nextTerminatorUser, tickUnchecked,
    lens, fixed, unchecked, noGc, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure]

variable {C O X : Type}

/-- At an actual MIR terminator, expose the source's fixed-scheduling driver
effect before the original terminator dispatch. This does not replace its
selected action, failure, or caller stack. -/
theorem stepFixedTerminator
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (before : State) (term : Miri.MIR.Terminator)
    (selected : Miri.Verification.StepWP.currentTerminator before = some term)
    (lens : ∀ control user, config.terminators.getControl
      (config.terminators.setControl control user) = control)
    (fixed : before.machine.threads.fixedScheduling = true)
    (unchecked : (config.terminators.getControl before.machine.user).checkedArithmetic = false)
    (noGc : (config.terminators.getControl before.machine.user).gcInterval = 0) :
    let user := nextTerminatorUser config.terminators before.machine.user
    let after := {before with machine := {before.machine with user}}
    let result := ControlFlow.evalTerminator (ExecutionMachine.terminatorHooks config limits)
      choice term after
    ExecutionMachine.step config limits choice before = (result.1, result.2.map fun _ => true) := by
  unfold ExecutionMachine.step
  rw [Miri.Verification.StepWP.step_eq_runTerminator selected]
  have tick := beforeTerminatorFixed config.terminators (config.preemptionChoice choice) before
    lens fixed unchecked noGc
  have sameControl : (ExecutionMachine.withValidation config limits).terminators =
      config.terminators := rfl
  have sameChoice : (ExecutionMachine.withValidation config limits).preemptionChoice =
      config.preemptionChoice := rfl
  simp only [Step.runTerminator, ExecutionMachine.stepHooks, MachineHooks.run, Call.run,
    sameControl, sameChoice, tick, Id.run, pure, Pure.pure]
  rfl

/-- The ordinary return stage after the fixed-scheduling source prefix. -/
theorem stepFixedReturn
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (before : State) (term : Miri.MIR.Terminator)
    (selected : Miri.Verification.StepWP.currentTerminator before = some term)
    (returnCode : term.kind = .Return)
    (lens : ∀ control user, config.terminators.getControl
      (config.terminators.setControl control user) = control)
    (fixed : before.machine.threads.fixedScheduling = true)
    (unchecked : (config.terminators.getControl before.machine.user).checkedArithmetic = false)
    (noGc : (config.terminators.getControl before.machine.user).gcInterval = 0) :
    let user := nextTerminatorUser config.terminators before.machine.user
    let after := {before with machine := {before.machine with user}}
    let result := ControlFlow.returnFromCurrentFrame
      (ExecutionMachine.terminatorHooks config limits).toControlHooks choice false after
    ExecutionMachine.step config limits choice before = (result.1, result.2.map fun _ => true) := by
  rw [stepFixedTerminator config limits choice before term selected lens fixed unchecked noGc]
  simp only [ControlFlow.evalTerminator, returnCode, Id.run, pure, Pure.pure]

/-- The stock driver executes the call under its actual before-terminator
control update. A non-tail call which pushed a frame advances the step. -/
theorem stepFixedCall
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (before after : State) (term : Miri.MIR.Terminator)
    (item : Miri.MIR.Operand) (args : Array Miri.MIR.SpannedOperand) (destination : Miri.MIR.Place)
    (target : Option Miri.MIR.BasicBlockId) (unwind : Miri.MIR.UnwindAction)
    (origin : Miri.MIR.CallSource) (span : Miri.MIR.SpanRef)
    (shape : term.kind = .Call item args destination target unwind origin span)
    (selected : Miri.Verification.StepWP.currentTerminator before = some term)
    (lens : ∀ control user, config.terminators.getControl
      (config.terminators.setControl control user) = control)
    (fixed : before.machine.threads.fixedScheduling = true)
    (unchecked : (config.terminators.getControl before.machine.user).checkedArithmetic = false)
    (noGc : (config.terminators.getControl before.machine.user).gcInterval = 0)
    (depth : after.stack.frames.size = before.stack.frames.size + 1) :
    let user := nextTerminatorUser config.terminators before.machine.user
    let entered := {before with machine := {before.machine with user}}
    Call.evalCallTerminator (ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits)
      choice limits.callDispatch term entered = .ok () after →
    ExecutionMachine.step config limits choice before = (after, .ok true) := by
  intro user entered called
  rw [stepFixedTerminator config limits choice before term selected lens fixed unchecked noGc]
  have nextDepth : after.stack.frames.size ≠ entered.stack.frames.size := by
    change after.stack.frames.size ≠ before.stack.frames.size
    omega
  have hook :
      (ExecutionMachine.terminatorHooks config limits).call choice term entered = (after, .ok ()) := by
    change MachineHooks.run (Call.evalCallTerminator
      (ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits)
      choice limits.callDispatch term) entered = _
    unfold MachineHooks.run Call.run
    rw [called]
  have run : ControlFlow.evalTerminator (ExecutionMachine.terminatorHooks config limits)
      choice term entered = (after, .ok ()) := by
    generalize (ExecutionMachine.terminatorHooks config limits) = hooks at hook ⊢
    simp [ControlFlow.evalTerminator, shape, ControlFlow.evalCall, hook, nextDepth]
  change ((ControlFlow.evalTerminator (ExecutionMachine.terminatorHooks config limits)
      choice term entered).1, (ControlFlow.evalTerminator (ExecutionMachine.terminatorHooks config limits)
      choice term entered).2.map (fun _ => true)) = _
  rw [run]
  rfl

end DuplicatePrefix.NestedGuardDriver

#print axioms DuplicatePrefix.NestedGuardDriver.beforeTerminatorFixed
#print axioms DuplicatePrefix.NestedGuardDriver.stepFixedTerminator

#print axioms DuplicatePrefix.NestedGuardDriver.stepFixedReturn

#print axioms DuplicatePrefix.NestedGuardDriver.stepFixedCall

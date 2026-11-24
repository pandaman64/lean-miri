import ZeroTail

namespace DuplicatePrefix.ZeroTail
open Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification Std.WP

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra
local notation "Config" => ExecutionMachine.Config K U C O X H

/-- At a selected Return, the source driver accounts for the terminator before
executing the canonical Return precondition. -/
theorem returnDriverPre (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (term : Terminator) (selected : StepWP.currentTerminator (atFrame older frame machine) = some term)
    (opcode : term.kind = .Return)
    (lens : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control)
    (fixed : machine.threads.fixedScheduling = true)
    (gc : (config.terminators.getControl machine.user).gcInterval = 0)
    (unchecked : (config.terminators.getControl machine.user).checkedArithmetic = false)
    (post : Bool → State → Prop) (failure : StepError → State → Prop) :
    InstructionWP.resultPre post failure (ExecutionMachine.step config limits choice (atFrame older frame machine)) ↔
      CanonicalStepWP.returnPre config limits choice false (post true) failure
        (atFrame older frame {machine with user := accounted config.terminators machine.user}) := by
  rw [ExecutionMachine.step, StepWP.step_eq_runTerminator selected]
  rw [← StepWP.terminatorStepPre_iff, ← CanonicalStepWP.terminatorPre_iff]
  have tick := beforeTerminator_fixed config.terminators
    ((ExecutionMachine.withValidation config limits).preemptionChoice choice)
    (atFrame older frame machine) lens fixed gc unchecked
  unfold CanonicalStepWP.terminatorPre
  change wp (TerminatorMachine.beforeTerminatorWithChoice config.terminators
    ((ExecutionMachine.withValidation config limits).preemptionChoice choice))
    (fun _ ready => CanonicalStepWP.selectedTerminatorPre config limits choice term (post true) failure ready)
    failure (atFrame older frame machine) ↔ _
  simp only [wp, WP.wpTrans]
  rw [tick]
  simp only [CanonicalStepWP.selectedTerminatorPre, InstructionWP.terminatorPreWithReturn, opcode]
  rfl

/-- A clean, empty Return block selects the precise terminator and location
used by the normal Return proof. -/
theorem selectZeroReturn
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (location : frame.location = .mir ⟨10, 0⟩)
    (code : (frame.body.basicBlocks[10]?).map
      (fun block => (block.statements.size, block.terminator.kind, block.cleanup)) =
        some (0, .Return, false)) :
    ∃ block, frame.body.basicBlocks[10]? = some block ∧ block.cleanup = false ∧
      block.terminator.kind = .Return ∧
      StepWP.currentTerminator (atFrame older frame machine) = some block.terminator := by
  obtain ⟨block, found, shape⟩ := Option.map_eq_some_iff.mp code
  have fields := Prod.mk.inj shape
  have rest := Prod.mk.inj fields.2
  have empty := fields.1
  have opcode := rest.1
  have clean := rest.2
  refine ⟨block, found, clean, opcode, ?_⟩
  have missing : block.statements[0]? = none := by
    simp [Array.getElem?_eq_none, empty]
  simp [StepWP.currentTerminator, atFrame, Stack.currentFrame?, location, found, missing]

#print axioms selectZeroReturn
#print axioms returnDriverPre
end DuplicatePrefix.ZeroTail

import Miri.Verification.CanonicalStepWP
import Miri.Interpreter.Unwind
import ZeroBoolean

namespace DuplicatePrefix.ZeroBoolean
set_option linter.unusedSectionVars false
open Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- Exact control composition for the normal Return, once the typed effects
have been discharged at their source. -/
theorem returnPreOfEffects (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (choice : C)
    (older : Array Frame) (caller callee updated : Frame)
    (machine popped : MachineHooks.MachineState K U) (value : OpTy Provenance)
    (block : BasicBlock) (pc : Location) (location : callee.location = .mir pc)
    (located : callee.body.basicBlocks[pc.block]? = some block) (normal : block.cleanup = false)
    (target : BasicBlockId) (action : UnwindAction)
    (continues : callee.returnContinuation = .goto (some target) action)
    (read : (ExecutionMachine.terminatorHooks config limits).returnOperand choice
      (atFrame (older.push caller) callee machine) = (atFrame (older.push caller) callee machine, .ok value))
    (copied : (ExecutionMachine.terminatorHooks config limits).copyReturn choice value callee.returnPlace
      (atFrame older caller popped) = (atFrame older updated popped, .ok ()))
    (cleaned : CallMachine.cleanup (ExecutionMachine.withValidation config limits).lifecycle choice false callee
      (atFrame older updated popped) = .ok .normal (atFrame older updated popped))
    (pop : ∀ finish failure,
      ProtectorReleaseWP.popRawPre
        (TypedMachineBindings.retagHooks (ExecutionMachine.withValidation config limits).access
          (ExecutionMachine.withValidation config limits).retag)
        finish failure (atFrame (older.push caller) callee machine) ↔
      finish callee (atFrame older caller popped))
    (post : State → Prop) (failure : StepError → State → Prop) :
    CanonicalStepWP.returnPre config limits choice false post failure (atFrame (older.push caller) callee machine) ↔
      post (atFrame older {updated with location := .mir ⟨target, 0⟩} popped) := by
  have current : (atFrame (older.push caller) callee machine).stack.currentFrame? = some callee := by
    simp [atFrame, Stack.currentFrame?]
  simp only [CanonicalStepWP.returnPre, InstructionWP.returnPreWithEffects, current, location,
    located, normal, show (false != false) = false from rfl, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  change InstructionWP.resultPre _ failure
    ((ExecutionMachine.terminatorHooks config limits).returnOperand choice (atFrame (older.push caller) callee machine)) ↔ _
  rw [read]
  simp only [InstructionWP.resultPre]
  rw [pop]
  change InstructionWP.resultPre (fun _ => CanonicalStepWP.cleanupFramePre
      (ExecutionMachine.withValidation config limits).lifecycle choice false callee
      (InstructionWP.finishReturnPre (ExecutionMachine.terminatorHooks config limits).toControlHooks
        choice false callee post failure) failure) failure
    ((ExecutionMachine.terminatorHooks config limits).copyReturn choice value callee.returnPlace
      (atFrame older caller popped)) ↔ _
  rw [copied]
  simp only [InstructionWP.resultPre]
  rw [CanonicalStepWP.cleanupFramePre_iff, RvalueWP.actionPre_ok cleaned]
  simp [InstructionWP.finishReturnPre, continues, InstructionWP.jumpPre,
    InstructionWP.locationPre, atFrame, Stack.currentFrame?, Array.set_push] <;> rfl

#print axioms returnPreOfEffects
end DuplicatePrefix.ZeroBoolean

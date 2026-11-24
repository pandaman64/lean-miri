import ZeroBoolean

namespace DuplicatePrefix.ZeroBoolean
open Miri.Input Miri.Memory Miri.MIR Miri.Interpreter

set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra
local notation "Config" => ExecutionMachine.Config K U C O X H

def trueOperand : ConstOperand := ⟨⟨26⟩, none, .Val (.Scalar (.Int 1 1)) 0⟩

/-- Execute the emitted zero-branch Boolean assignment and advance the live
callee to the first cleanup statement. The slice and caller stack may carry
arbitrary machine histories within the stated Boolean-local profile. -/
theorem zeroAssign (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (layout : LocalLayout)
    (runtime : RuntimeMetadata)
    (externStatic : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError)
    (constant : config.operands.constant choice trueOperand (some layout) =
      ConstantMachine.evalOperandWithLayout runtime config.functions config.arithmetic externStatic classify
        trueOperand (some layout) none)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (profile : BooleanLocalProfile config limits choice layout machine)
    (resolve : (profilePlace config limits).resolveLayout choice 0 (atFrame older frame machine) =
      .ok layout (atFrame older frame machine))
    (node : ((frame.body.basicBlocks[1]?).bind fun block =>
      (block.statements[1]?).map Statement.kind) =
      some (.Assign ⟨0, #[]⟩ (.Use (.Constant trueOperand) .Yes))) (location : frame.location = .mir ⟨1, 1⟩)
    (bound : 0 < frame.locals.size) (uncached : frame.locals[0].layout = none)
    (old : Immediate Provenance) (live : frame.locals[0].value = .live (.immediate old))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default) :
    let cached := cacheBool frame layout bound
    let valid : 0 < cached.locals.size := by simpa [cached, cacheBool] using bound
    ExecutionMachine.step config limits choice (atFrame older frame machine) =
      (atFrame older {setTrue cached valid with location := .mir ⟨1, 2⟩} machine, .ok true) := by
  obtain ⟨block, atBlock, op⟩ := Option.bind_eq_some_iff.mp node
  obtain ⟨stmt, atStmt, opcode⟩ := Option.map_eq_some_iff.mp op
  let cached := cacheBool frame layout bound
  have valid : 0 < cached.locals.size := by simpa [cached, cacheBool] using bound
  have effect := evalAssignTrue config limits choice ⟨26⟩ layout runtime externStatic classify
    constant older frame machine profile resolve bound uncached old live noClocks tracker tracked defaultMode
  have kept : (setTrue cached valid).location = .mir ⟨1, 1⟩ := location
  simp only [ExecutionMachine.step, Step.step, Id.run, Pure.pure, pure, atFrame,
    Stack.currentFrame?, Array.back?_push, location, atBlock, atStmt, Step.evalStatement, opcode,
    ExecutionMachine.stepHooks]
  have assigned : evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits) choice
      (.Use (.Constant trueOperand) .Yes) ⟨0, #[]⟩
      (⟨⟨older.push frame⟩, machine⟩ : State) =
      .ok () ⟨⟨older.push (setTrue cached valid)⟩, machine⟩ := effect
  unfold MachineHooks.run Call.run
  simp only [assigned]
  simp [Step.finishStatement, Id.run, atFrame, Stack.currentFrame?, kept, Array.set_push] <;> rfl

#print axioms zeroAssign
end DuplicatePrefix.ZeroBoolean

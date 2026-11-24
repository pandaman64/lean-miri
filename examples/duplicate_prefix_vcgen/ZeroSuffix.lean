import ZeroNodes

namespace DuplicatePrefix.ZeroTail
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
open Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open ZeroBoolean (BooleanLocalProfile cacheBool setTrue profilePlace trueOperand)

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra
local notation "Config" => ExecutionMachine.Config K U C O X H

def afterFive (frame : Frame) (bound : 5 < frame.locals.size) : Frame :=
  retired frame 5 bound ⟨1, 1⟩

def assigned (frame : Frame) (layout : LocalLayout) (bound : 0 < frame.locals.size) : Frame :=
  let cached := cacheBool frame layout bound
  {setTrue cached (by simpa [cached, cacheBool] using bound) with location := .mir ⟨1, 2⟩}

@[simp] private theorem retired_size (frame : Frame) (id : Miri.MIR.LocalId) (bound : id < frame.locals.size)
    (next : Location) : (retired frame id bound next).locals.size = frame.locals.size :=
  Array.size_set bound

@[simp] private theorem assigned_size (frame : Frame) (layout : LocalLayout) (bound : 0 < frame.locals.size) :
    (assigned frame layout bound).locals.size = frame.locals.size := by
  simp [assigned, setTrue, cacheBool]

private def armAssigned (frame : Frame) (layout : LocalLayout) (bound : 5 < frame.locals.size) : Frame := by
  have firstSize : (afterFive frame bound).locals.size = frame.locals.size := Array.size_set bound
  exact assigned (afterFive frame bound) layout (by rw [firstSize]; omega)

private theorem armAssigned_size (frame : Frame) (layout : LocalLayout)
    (bound : 5 < frame.locals.size) : (armAssigned frame layout bound).locals.size = frame.locals.size := by
  unfold armAssigned
  rw [assigned_size]
  exact Array.size_set bound

private def armThird (frame : Frame) (layout : LocalLayout) (bound : 5 < frame.locals.size) : Frame :=
  retired (armAssigned frame layout bound) 4 (by rw [armAssigned_size]; exact Nat.lt_trans (by decide : (4 : Nat) < 5) bound) ⟨1, 3⟩

private def armFourth (frame : Frame) (layout : LocalLayout) (bound : 5 < frame.locals.size) : Frame :=
  retired (armThird frame layout bound) 3 (by rw [armThird, retired_size, armAssigned_size]; exact Nat.lt_trans (by decide : (3 : Nat) < 5) bound) ⟨1, 4⟩

/-- Canonical execution of the zero arm from its first instruction to the
selected return block. The source model supplies each exact intermediate
frame, preserving the assigned Boolean and the caller stack. -/
theorem zeroSuffixToReturn (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (layout : LocalLayout) (runtime : RuntimeMetadata)
    (externStatic : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError)
    (constant : config.operands.constant choice trueOperand (some layout) =
      ConstantMachine.evalOperandWithLayout runtime config.functions config.arithmetic externStatic classify
        trueOperand (some layout) none)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (profile : BooleanLocalProfile config limits choice layout machine)
    (body : frame.body = program.root.body) (location : frame.location = .mir ⟨1, 0⟩)
    (bound : 5 < frame.locals.size)
    (value5 value4 value3 old : Immediate Provenance)
    (slot5 : frame.locals[5].value = .live (.immediate value5))
    (slot4 : (frame.locals[4]'(by omega)).value = .live (.immediate value4))
    (slot3 : (frame.locals[3]'(by omega)).value = .live (.immediate value3))
    (slot0 : (frame.locals[0]'(by omega)).value = .live (.immediate old))
    (uncached : (frame.locals[0]'(by omega)).layout = none)
    (resolve : (profilePlace config limits).resolveLayout choice 0
        (atFrame older (afterFive frame bound) machine) =
      .ok layout (atFrame older (afterFive frame bound) machine))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (lens : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control)
    (fixed : machine.threads.fixedScheduling = true)
    (gc : (config.terminators.getControl machine.user).gcInterval = 0)
    (unchecked : (config.terminators.getControl machine.user).checkedArithmetic = false) :
    let first := afterFive frame bound
    let second := armAssigned frame layout bound
    let third := armThird frame layout bound
    let fourth := armFourth frame layout bound
    let returned := {fourth with location := .mir ⟨10, 0⟩}
    let state (fr : Frame) := atFrame older fr machine
    ExecutionMachine.step config limits choice (state frame) = (state first, .ok true) ∧
    ExecutionMachine.step config limits choice (state first) = (state second, .ok true) ∧
    ExecutionMachine.step config limits choice (state second) = (state third, .ok true) ∧
    ExecutionMachine.step config limits choice (state third) = (state fourth, .ok true) ∧
    ExecutionMachine.step config limits choice (state fourth) =
      (atFrame older returned {machine with user := accounted config.terminators machine.user}, .ok true) := by
  dsimp only
  let first := afterFive frame bound
  have firstSize : first.locals.size = frame.locals.size := Array.size_set bound
  have first0 : 0 < first.locals.size := by omega
  have firstSlot (i : Nat) (inFrame : i < frame.locals.size) (different : 5 ≠ i) :
      (first.locals[i]'(by omega)) = frame.locals[i] := by
    exact Array.getElem_set_ne bound inFrame different
  let second := assigned first layout first0
  have secondSize : second.locals.size = frame.locals.size := by
    simp [second, assigned, setTrue, cacheBool, firstSize]
  have secondSlot (i : Nat) (inFrame : i < frame.locals.size) (notZero : 0 ≠ i) (notFive : 5 ≠ i) :
      (second.locals[i]'(by omega)) = frame.locals[i] := by
    simpa [second, assigned, setTrue, cacheBool, Array.getElem_set_ne first0 (by omega : i < first.locals.size) notZero,
      Array.getElem_set_ne (by simpa [cacheBool] using first0) (by simpa [cacheBool] using (show i < first.locals.size by omega)) notZero]
      using firstSlot i inFrame notFive
  have second4 : 4 < second.locals.size := by omega
  let third := retired second 4 second4 ⟨1, 3⟩
  have thirdSize : third.locals.size = second.locals.size := Array.size_set second4
  have third3 : 3 < third.locals.size := by omega
  let fourth := retired third 3 third3 ⟨1, 4⟩
  change ExecutionMachine.step config limits choice (atFrame older frame machine) = _ ∧
    ExecutionMachine.step config limits choice (atFrame older first machine) = (atFrame older second machine, .ok true) ∧
    ExecutionMachine.step config limits choice (atFrame older second machine) = (atFrame older third machine, .ok true) ∧
    ExecutionMachine.step config limits choice (atFrame older third machine) = (atFrame older fourth machine, .ok true) ∧
    ExecutionMachine.step config limits choice (atFrame older fourth machine) = _
  refine ⟨zeroStorageDead config limits choice older frame machine ⟨1, 0⟩ 5 bound (.inl rfl)
    value5 slot5 body location, ?_, ?_, ?_, zeroGoto config limits choice older fourth machine body rfl lens fixed gc unchecked⟩
  · apply ZeroBoolean.zeroAssign config limits choice layout runtime externStatic classify constant older first machine profile resolve
      (by simpa only [show first.body = frame.body from rfl, body] using zeroNodes.1) rfl first0
      (by rw [firstSlot 0 (by omega) (by decide), uncached]) old
      (by rw [firstSlot 0 (by omega) (by decide), slot0]) noClocks tracker tracked defaultMode
  · exact zeroStorageDead config limits choice older second machine ⟨1, 2⟩ 4 second4 (.inr (.inl rfl)) value4
      (by rw [secondSlot 4 (by omega) (by decide) (by decide), slot4]) body rfl
  · exact zeroStorageDead config limits choice older third machine ⟨1, 3⟩ 3 third3 (.inr (.inr rfl)) value3
      (by rw [show third.locals[3] = second.locals[3]'(by omega) from
          Array.getElem_set_ne second4 (by omega) (by decide),
        secondSlot 3 (by omega) (by decide) (by decide), slot3]) body rfl

#print axioms zeroSuffixToReturn
end DuplicatePrefix.ZeroTail

import Miri.Verification.NondivergingIntrinsicWP

/-! Exercise assertion failure and copy-size checks with arbitrary continuations. -/
namespace MiriTests.Verification.NondivergingIntrinsicWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- A false assumption reports UB in the state left by the immediate read. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before evaluated ready : State) (frame : Frame) (loc : Location)
    (block : BasicBlock) (stmt : Statement) (operand : Operand)
    (value : OpTy Provenance) (layout : LocalLayout)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .Intrinsic (.Assume operand))
    (operandEval : OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () operand none before = .ok value evaluated)
    (read : PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access value evaluated =
      .ok ⟨.scalar (.fromBool false), layout⟩ ready)
    (accept : onError (.undefinedBehavior "assume called with false") ready) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [CanonicalStepWP.choicePre, StepWP.driverChoicePreWith,
    current, position, selected, statement, kind]
  miri_nondiverging_intrinsic_wp
  simp only [RvalueWP.actionPre, operandEval, read, RvalueWP.scalarCheckPre]
  exact accept

/-- A size overflow calls the error continuation after layout lookup and
before either pointer is read. -/
example (hooks : MemoryIntrinsicHooks Provenance State Unit)
    (before countRead typeRead layoutRead : State) (source dest count : OpTy Provenance)
    (countValue : RvalueImmTy Provenance) (countScalar : Scalar Provenance)
    (length : UInt64) (ty : TyId) (layout : TyAndLayout TyId)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (read : hooks.readImmediate () count before = .ok countValue countRead)
    (scalar : countValue.imm.toScalar = .ok countScalar)
    (lengthOk : countScalar.toTargetUsize (Size.fromBits hooks.target.pointerWidth.bits) = .ok length)
    (pointee : hooks.pointeeType () source.layout.ty countRead = .ok ty typeRead)
    (layoutOk : hooks.layoutOf () ty typeRead = .ok layout layoutRead)
    (tooLarge : IntegerOps.computeSizeInBytes layout.layout.size length hooks.maxSizeOfVal = none)
    (accept : onError (.undefinedBehavior "overflow computing total size of copy") layoutRead) :
    wp (Intrinsics.copyWith hooks () source dest count true) post onError before := by
  miri_nondiverging_intrinsic_wp
  simpa only [RvalueWP.actionPre, read, RvalueWP.scalarCheckPre, scalar, lengthOk, Except.mapError,
    pointee, layoutOk, tooLarge] using accept

end MiriTests.Verification.NondivergingIntrinsicWP

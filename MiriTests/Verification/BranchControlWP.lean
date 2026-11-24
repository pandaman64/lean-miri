import Miri.Verification.CanonicalStepWP

/-! Exercise canonical terminator selection through the production step spec. -/
namespace MiriTests.Verification.BranchControlWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- The i8 bit pattern 255 matches the first case as -1. A later case has an
out-of-range constant, so passing this check depends on stopping at the match. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before ready readState : State) (frame : Frame) (loc : Location) (block : BasicBlock)
    (operand : Operand) (layout : LocalLayout)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (noStatement : block.statements[loc.statementIndex]? = none)
    (kind : block.terminator.kind = .SwitchInt operand ⟨#[.Case 255 2, .Case 256 3], 4⟩)
    (prepared : TerminatorMachine.beforeTerminatorWithChoice
      (ExecutionMachine.withValidation config limits).terminators
      ((ExecutionMachine.withValidation config limits).preemptionChoice ()) before = .ok () ready)
    (operandRead : BranchControlWP.readOperand config limits () operand ready =
      .ok ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt8 255)), layout⟩ readState)
    (width : layout.layout.size = Size.ofBytes 1)
    (classify : config.scalar.classify () layout.ty = pure (.integer .i8))
    (complete : RvalueWP.actionPre (config.scalar.boolLayout ())
      (fun _ => InstructionWP.jumpPre 2 (fun after => True ∧ post () after) onError)
      onError readState) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  let raw := ScalarInt.ofUInt8 255
  let value : RvalueImmTy Provenance := ⟨.scalar (.fromScalarInt raw), layout⟩
  let integer : IntegerValue := ⟨raw, ⟨Size.ofBytes 1, .i8⟩⟩
  have caseOk : Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 255) layout.layout.size =
      .ok (.fromScalarInt raw) := by rw [width]; rfl
  have checked : RvalueWP.integerOperand value .i8 = .ok integer := by
    simp only [value, RvalueWP.integerOperand, width]
    rfl
  have decoded : IntegerOps.decode integer = .ok (-1) := by cbv
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, noStatement, kind,
    CanonicalStepWP.terminatorPre, CanonicalStepWP.selectedTerminatorPre, wp, WP.wpTrans, prepared,
    BranchControlWP.switchPre]
  unfold RvalueWP.actionPre
  rw [operandRead]
  let jump (target : BasicBlockId) :=
    InstructionWP.jumpPre target (fun after => True ∧ post () after) onError
  let finish (passed : Bool) (after : State) :=
    if passed then jump 2 after
    else BranchControlWP.switchCasesPre config limits () value 4 jump onError [.Case 256 3] after
  change RvalueWP.actionPre (BranchControlWP.compareCase config limits () value 255) finish onError readState
  have compared := BranchControlWP.compareCase_integerPre config limits () value 255
    (.fromScalarInt raw) .i8 integer integer (-1) (-1) caseOk classify checked checked rfl
    decoded decoded finish onError
  rw [compared]
  exact complete

/-- Boolean conversion rejects the invalid representation before an assertion
can compare the value or enter its panic continuation. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before ready readState : State) (frame : Frame) (loc : Location) (block : BasicBlock)
    (operand : Operand) (layout : LocalLayout) (expected : Bool) (message : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (noStatement : block.statements[loc.statementIndex]? = none)
    (kind : block.terminator.kind = .Assert operand expected message target unwind)
    (prepared : TerminatorMachine.beforeTerminatorWithChoice
      (ExecutionMachine.withValidation config limits).terminators
      ((ExecutionMachine.withValidation config limits).preemptionChoice ()) before = .ok () ready)
    (letRead : BranchControlWP.readOperand config limits () operand ready =
      .ok ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt8 2)), layout⟩ readState)
    (acceptError : onError (ScalarOps.scalarIntError (.invalidBool 2)) readState) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, noStatement,
    CanonicalStepWP.terminatorPre, wp, WP.wpTrans, prepared]
  simp only [CanonicalStepWP.selectedTerminatorPre, kind, CanonicalStepWP.canonical_assertConditionPre]
  unfold RvalueWP.actionPre
  rw [letRead]
  exact acceptError

end MiriTests.Verification.BranchControlWP

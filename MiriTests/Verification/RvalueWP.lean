import Miri.Verification.ExactWP
import Init.Internal.Order.While

/-! Verify the canonical driver selects the symbolic assignment continuation
and routes its remaining effect to the actual typed copy. -/
namespace MiriTests.Verification.RvalueWP

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Verification
open Miri.TreeBorrows.RetagPolicy Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

theorem use_vcgen (config : Config) (limits : ExecutionMachine.Limits)
    (place : Place) (rhs : Operand) (before projected copying : State)
    (frame : Frame) (loc : Location) (block : BasicBlock) (stmt : Statement)
    (destination : RuntimePlace Provenance) (source : OpTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .Assign place (.Use rhs .No))
    (placeOk : PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
      () place true before = .ok destination projected)
    (operandOk : OperandMachine.evalOperand (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () rhs (some destination.layout) projected = .ok source copying)
    (copyChecked : RvalueWP.retagModePre .None
      (copyRuntimePlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
        (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits).copy () source destination false)
      (fun _ => InstructionWP.finishStatementResultPre
        (before.stack.frames.size - 1) (fun actual after => actual = true ∧ post () after)
        onError) onError copying) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind]
  have prepared : PlaceDynamic.evalPlace
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () place true before = .ok destination projected := placeOk
  rw [RvalueWP.actionPre_ok prepared, RvalueWP.actionPre_ok operandOk]
  exact copyChecked

/-- A padded, indirect source follows the physical copy path. Its arbitrary
success and error continuations are passed to the production typed copy. -/
theorem indirect_copy (config : Config) (limits : ExecutionMachine.Limits)
    (destination : RuntimePlace Provenance) (source : OpTy Provenance)
    (memorySource : MemPlace Provenance) (memoryDest : MPlaceTy Provenance)
    (before allocated : State) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (compatible : (ExecutionMachine.withValidation config limits).copy.compatible
      source.layout destination.layout = .ok true)
    (padding : (ExecutionMachine.withValidation config limits).copy.hasPadding source.layout = .ok true)
    (sourceMemory : source.op = .indirect memorySource)
    (destMemory : forceAllocation (ExecutionMachine.projectionHooks config).place () destination
      before = .ok memoryDest allocated) :
    RvalueWP.actionPre
      (copyRuntimePlaceNoValidate (ExecutionMachine.projectionHooks config).place
        (ExecutionMachine.withValidation config limits).copy () source destination false)
      post onError before =
      wp (GlobalMemoryCopyMachine.typedCopy config.access config.addresses config.arithmetic
        config.projection.dynamic config.projection.dynamicFuel config.compiler.debugAssertions
        () ⟨memorySource, source.layout⟩ memoryDest) post onError allocated := by
  simp only [copyRuntimePlaceNoValidate, compatible, padding, placeLift_ok,
    RvalueWP.actionPre_bind, RvalueWP.actionPre_pure, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    sourceMemory]
  rw [RvalueWP.actionPre_ok destMemory, RvalueWP.canonical_memoryCopy, RvalueWP.actionPre_eq_wp]

/-- The canonical driver passes the byte 2 to boolean decoding after the read.
The UB continuation receives the resulting state, before any destination write. -/
theorem invalid_boolean_unary (config : Config) (limits : ExecutionMachine.Limits)
    (place : Place) (operand : Operand) (before projected reading readState classified : State)
    (frame : Frame) (loc : Location) (block : BasicBlock) (stmt : Statement)
    (destination : RuntimePlace Provenance) (source : OpTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .Assign place (.UnaryOp .Not operand))
    (placeOk : PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks
      (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () place true before = .ok destination projected)
    (operandOk : OperandMachine.evalOperand (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () operand (some destination.layout) projected = .ok source reading)
    (readOk : PlaceMachine.readImmediate config.access source reading =
      .ok ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt8 2)), source.layout⟩ readState)
    (classifiedAsBool : config.scalar.classify () source.layout.ty readState =
      .ok .boolean classified)
    (acceptError : onError (ScalarOps.scalarIntError (.invalidBool 2)) classified) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  have classifiedOk : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (ExecutionMachine.withValidation config limits) limits)).classify () source.layout.ty readState =
        .ok .boolean classified := classifiedAsBool
  have invalid : (Scalar.fromScalarInt (Prov := Provenance) (ScalarInt.ofUInt8 2)).toBool =
      .error (.scalarInt (.invalidBool 2)) := by cbv
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind]
  rw [RvalueWP.actionPre_ok placeOk]
  simp only [UnOp.homogeneous, ↓reduceIte]
  rw [RvalueWP.actionPre_ok operandOk]
  change RvalueWP.actionPre (PlaceMachine.readImmediate config.access source) _ onError reading
  rw [RvalueWP.actionPre_ok readOk, RvalueWP.actionPre_ok classifiedOk]
  simpa only [RvalueWP.scalarCheckPre, Immediate.toScalar, Except.mapError, invalid,
    ScalarOps.scalarError] using acceptError

private def byteImm (layout : LocalLayout) (value : UInt8) : RvalueImmTy Provenance :=
  ⟨.scalar (.fromScalarInt (ScalarInt.ofUInt8 value)), layout⟩

private def byteInt (value : UInt8) : IntegerValue :=
  ⟨ScalarInt.ofUInt8 value, ⟨Size.ofBytes 1, .u8⟩⟩

/-- The canonical binary hook exposes the unchecked overflow and division
errors directly. The with-overflow operation runs its layout query and returns
the wrapped byte together with the overflow bit. -/
theorem binary_byte_arithmetic (config : Config) (limits : ExecutionMachine.Limits)
    (layout overflowLayout : LocalLayout) (before leftState rightState done : State)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop)
    (width : layout.layout.size = Size.ofBytes 1)
    (leftClass : config.scalar.classify () layout.ty before = .ok (.integer .u8) leftState)
    (rightClass : config.scalar.classify () layout.ty leftState = .ok (.integer .u8) rightState)
    (overflowOk : config.scalar.overflowLayout () layout rightState = .ok overflowLayout done) :
    RvalueWP.actionPre ((ExecutionMachine.rvalueHooks config limits).binaryOp ()
      .Div (byteImm layout 255) (byteImm layout 0)) post onError before =
        onError (ScalarOps.integerError (.undefinedBehavior .divisionByZero)) rightState ∧
    RvalueWP.actionPre ((ExecutionMachine.rvalueHooks config limits).binaryOp ()
      .AddUnchecked (byteImm layout 255) (byteImm layout 1)) post onError before =
        onError (ScalarOps.integerError (.undefinedBehavior (.arithmeticOverflow .AddUnchecked)))
          rightState ∧
    RvalueWP.actionPre ((ExecutionMachine.rvalueHooks config limits).binaryOp ()
      .AddWithOverflow (byteImm layout 255) (byteImm layout 1)) post onError before =
        post ⟨.scalarPair (.fromScalarInt (ScalarInt.ofUInt8 0)) (.fromBool true), overflowLayout⟩ done := by
  let hooks := ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)
  have leftOk : hooks.classify () (byteImm layout 255).layout.ty before =
      .ok (.integer .u8) leftState := leftClass
  have rightOk (value : UInt8) : hooks.classify () (byteImm layout value).layout.ty leftState =
      .ok (.integer .u8) rightState := rightClass
  have layoutOk : hooks.overflowLayout () layout rightState = .ok overflowLayout done := overflowOk
  have decoded (value : UInt8) :
      RvalueWP.integerOperand (byteImm layout value) .u8 = .ok (byteInt value) := by
    simp only [RvalueWP.integerOperand, byteImm, byteInt, width] <;> rfl
  have pullback (op : BinOp) (value : UInt8) :
      RvalueWP.actionPre ((ExecutionMachine.rvalueHooks config limits).binaryOp ()
        op (byteImm layout 255) (byteImm layout value)) post onError before =
        RvalueWP.scalarCheckPre
          ((IntegerOps.binary op (byteInt 255) (byteInt value)).mapError ScalarOps.integerError)
          (RvalueWP.integerResultPre hooks () layout post onError) onError rightState := by
    rw [EffectSpecs.canonical_rvalue_binary,
      RvalueWP.actionPre_binary_integer hooks () op _ _ post onError before leftState .u8 leftOk,
      RvalueWP.actionPre_ok (rightOk value)]
    have same : ((byteImm layout 255).layout.ty != (byteImm layout value).layout.ty) = false := by
      exact bne_self_eq_false _
    simp only [decoded, RvalueWP.scalarCheckPre, same, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte] <;> rfl
  have division : IntegerOps.binary .Div (byteInt 255) (byteInt 0) =
      .error (.undefinedBehavior .divisionByZero) := by cbv
  have unchecked : IntegerOps.binary .AddUnchecked (byteInt 255) (byteInt 1) =
      .error (.undefinedBehavior (.arithmeticOverflow .AddUnchecked)) := by cbv
  have pair : IntegerOps.binary .AddWithOverflow (byteInt 255) (byteInt 1) =
      .ok (.withOverflow (ScalarInt.ofUInt8 0) true) := by cbv
  simp only [pullback, division, unchecked, pair, Except.mapError, RvalueWP.scalarCheckPre,
    RvalueWP.integerResultPre, RvalueWP.actionPre_ok layoutOk] <;> repeat' constructor

section AliasedRead

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def aliasTag : BorTag := ⟨2, by decide⟩
private def oneByte := Size.ofBytes 1

private def disabledChild : BorrowTree :=
  let root := BorrowTree.new BorTag.one oneByte
  let permissions := DedupRangeMap.new oneByte (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
  let inserted := root.newChild Size.ZERO (.concrete BorTag.one) aliasTag permissions .Frozen true
  (inserted.tree.performBorrowAccessRange (.concrete BorTag.one)
    Size.ZERO oneByte .Write {} .VisitChildrenOfAccessed).tree

private def failedRead := disabledChild.performBorrowAccessRange (.concrete aliasTag)
  Size.ZERO oneByte .Read {} .VisitChildrenOfAccessed

set_option maxRecDepth 65536 in
set_option cbv.maxSteps 1000000 in
private theorem failedReadStatus :
    failedRead.status =
      .AccessFailure ⟨0, 1⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)) := by
  cbv

/-- An earlier parent write disabled the alias used by the MIR operand.
The read fails before the unary operation or destination write. The error
continuation sees the actual failure and the state committed by the access. -/
theorem aliased_read (config : Config) (limits : ExecutionMachine.Limits)
    (place : Place) (operand : Operand) (before projected reading : State)
    (frame : Frame) (loc : Location) (block : BasicBlock) (stmt : Statement)
    (destination : RuntimePlace Provenance) (source : OpTy Provenance) (mplace : MemPlace Provenance)
    (primitive : BackendPrimitive) (validRange : WrappingRange)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .Assign place (.UnaryOp .Not operand))
    (placeOk : PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks config)
      () place true before = .ok destination projected)
    (operandOk : OperandMachine.evalOperand (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () operand (some destination.layout) projected = .ok source reading)
    (indirect : source.op = .indirect mplace)
    (backend : (localMemoryLayout source.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.access.runtime = .ok (localMemoryLayout source.layout).size)
    (checked : MemoryWP.CheckedPlaceAccess config.access false reading.machine.memory
      ⟨reading.machine, none⟩ ⟨mplace, localMemoryLayout source.layout⟩)
    (alias : checked.resolved.extra = .concrete aliasTag)
    (tree : checked.allocation.extra = disabledChild)
    (offset : checked.resolved.offset = Size.ZERO)
    (size : (localMemoryLayout source.layout).size = oneByte)
    (diagnosed raced : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (diagnostic : config.access.diagnostic false checked.resolved.allocId
      (allocRange Size.ZERO oneByte) checked.accessHooks.machine = .ok () diagnosed)
    (race : MachineHooks.memoryRaceAccess diagnosed checked.resolved.allocId
      (allocRange Size.ZERO oneByte) none .Read = (raced, .ok ()))
    (tracked : raced.borrowTracker = some tracker)
    (unprotected : tracker.global.protectedTags = {})
    (acceptError :
      let error := PlaceMachine.treeError false failedRead.status
      let ref : AllocationAccessRef Provenance BorrowTree :=
        ⟨checked.resolved.allocId, allocRange Size.ZERO oneByte, checked.allocation⟩
      let hook : AllocationExtraHookResult (PlaceMachine.AccessState K U) BorrowTree :=
        ⟨⟨raced, some error⟩, failedRead.tree, .error (reprStr error)⟩
      let result := AllocationAccess.finishCheckedAccess false checked.rawMemory ref hook
      onError error {reading with machine :=
        config.access.retainTouched {raced with memory := result.memory} result.touched}) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  have readChecked (afterRead : RvalueImmTy Provenance → State → Prop) :
      wp (PlaceMachine.readImmediate config.access source) afterRead onError reading := by
    rw [MemoryWP.readImmediate_iff,
      MemoryWP.scalarRead_resultPre_iff config.access source mplace primitive validRange
        afterRead onError reading checked indirect backend width]
    simp only [MemoryWP.CheckedPlaceAccess.pre, MemoryWP.memoryAccessPre, MemoryWP.policyPre,
      wp, WP.wpTrans, offset, size, diagnostic, race, Bool.false_eq_true, ↓reduceIte, tracked,
      tree, alias, unprotected, TreeBorrowsWP.accessPre_iff]
    simp only [allocRange]
    rw [← failedRead]
    simp only [failedReadStatus, MemoryWP.failurePre]
    -- A Tree Borrows error reaches the caller even if caching the tree failed.
    simp only [MemoryWP.resultPre, scalarReadAfterAccess, finishPlaceAccess,
      AllocationAccess.finishCheckedAccess, failedReadStatus] at acceptError ⊢
    generalize (if checked.rawMemory.live.contains checked.resolved.allocId then
      checked.rawMemory.setLiveAllocation checked.resolved.allocId
        (checked.allocation.setExtra failedRead.tree)
      else .ok checked.rawMemory) = cached at acceptError ⊢
    cases cached <;> exact acceptError
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind]
  have projectedOk : PlaceDynamic.evalPlace
      (ExecutionMachine.projectionHooks
        (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () place true before = .ok destination projected := placeOk
  rw [RvalueWP.actionPre_ok projectedOk]
  simp only [UnOp.homogeneous, ↓reduceIte]
  rw [RvalueWP.actionPre_ok operandOk]
  change RvalueWP.actionPre (PlaceMachine.readImmediate config.access source) _ onError reading
  rw [RvalueWP.actionPre_eq_wp]
  exact readChecked _

end AliasedRead

end MiriTests.Verification.RvalueWP

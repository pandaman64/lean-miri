import Representative
import Miri.Verification.FunctionBody
import Miri.Verification.StepWP
import Miri.Interpreter.CompilerExecutionProviders

/-!
The root block interfaces relate the generated equations to the arguments:

* At bb0, local 2 is the input count. The zero edge reaches bb1, with the
  slice allocation and its protector unchanged. bb1 sets true and joins
  the final return in bb10.
* At bb2, the count is positive. The shared reborrow for `len` preserves
  authority on the original slice and releases its own protector before
  resuming the caller. At bb4, local 9 is the input count, local 11 supplied
  the slice length and local 10 is half that length. bb5 sets false on
  rejection and joins bb10.
* At bb6, the guard bounds two disjoint in-allocation copy intervals. The
  mutable reborrow and pointer conversion bind the source address and
  provenance. At bb7 and bb8, the pointer and count imply the destination
  is exactly count bytes after the source, both retain live authority,
  and every active protector remains compatible with the copy.
* At bb9, the copy has finished and the result is true. The bb10 pop
  releases the root's owned protectors, writes the Boolean to the actual
  result place and follows the caller continuation.

These are proof interfaces. Each must be derived from independent facts
about the caller's input and the actual intervening effects.
-/
namespace DuplicatePrefix.PreparedArguments

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification

set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

private def atLocal (index : LocalId) : Place := ⟨index, #[]⟩

private def atStatement (body block index : Nat) : Option StatementKind := do
  let source ← GeneratedBodySafety.input.document.bodies[body]?
  let row ← source.mir.basicBlocks[block]?
  return (← row.statements[index]?).kind

private def atTerminator (body block : Nat) : Option TerminatorKind := do
  let source ← GeneratedBodySafety.input.document.bodies[body]?
  return (← source.mir.basicBlocks[block]?).terminator.kind

theorem entrySwitch :
    atTerminator 0 0 = some (.SwitchInt (.Move (atLocal 4)) ⟨#[.Case 0 2], 1⟩) := by
  rfl

theorem earlyReturnEdges :
    atTerminator 0 1 = some (.Goto 10 #[]) ∧
    atTerminator 0 5 = some (.Goto 10 #[]) ∧
    atTerminator 0 10 = some .Return := by
  exact ⟨rfl, rfl, rfl⟩

theorem boundsSwitch :
    atTerminator 0 4 = some (.SwitchInt (.Move (atLocal 8)) ⟨#[.Case 0 6], 5⟩) := by
  rfl

private def usizeConstant (value : Nat) (span : SpanRef) : ConstOperand :=
  ⟨span, none, .Val (.Scalar (.Int value 8)) 4⟩

/-- Link the symbolic scalar guard facts to the current imported assignments,
including the argument slot, exact unsigned width and division by two. -/
theorem guardAssignments :
    atStatement 0 0 3 = some (.Assign (atLocal 5) (.Use (.Copy (atLocal 2)) .Yes)) ∧
    atStatement 0 0 4 = some (.Assign (atLocal 4)
      (.BinaryOp .Eq (.Move (atLocal 5)) (.Constant (usizeConstant 0 ⟨25⟩)))) ∧
    atStatement 0 4 0 = some (.Assign (atLocal 10)
      (.BinaryOp .Div (.Move (atLocal 11)) (.Constant (usizeConstant 2 ⟨33⟩)))) ∧
    atStatement 0 4 2 = some (.Assign (atLocal 8)
      (.BinaryOp .Gt (.Move (atLocal 9)) (.Move (atLocal 10)))) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private def boolConstant (value : Nat) (span : SpanRef) : ConstOperand :=
  ⟨span, none, .Val (.Scalar (.Int value 1)) 0⟩

/-- The standalone export decides the language-UB guard in a resolved
callee whose only assignment negates the pinned `cfg!(miri)` value. -/
theorem languageCheckRuntimeCode :
    atStatement 19 0 0 = some (.Assign (atLocal 0)
      (.UnaryOp .Not (.Constant (boolConstant 1 ⟨350⟩)))) := by
  rfl

theorem languageCheckSwitch :
    atTerminator 9 1 = some (.SwitchInt (.Move (atLocal 1)) ⟨#[.Case 0 3], 2⟩) := by
  rfl

theorem languageCheckFalseArm :
    atStatement 9 3 0 = some (.Assign (atLocal 0)
      (.Use (.Constant (boolConstant 0 ⟨212⟩)) .Yes)) := by
  rfl

theorem languageCheckCallBinding :
    (do
      let source ← GeneratedBodySafety.input.document.bodies[9]?
      let evidence ← source.callEvidence[0]?.join
      evidence.instanceId) = some 21 ∧
    (GeneratedBodySafety.input.document.bodies[19]?.map (·.instanceId)) = some 21 := by
  exact ⟨rfl, rfl⟩

/-- Classification uses the imported type row, independently of target
allocation or current frame state. -/
theorem languageCheckRuntimeCompilerClass
    (facts : Miri.Input.CompilerFacts.Context)
    (source : facts.runtime.source = GeneratedBodySafety.input.document) :
    Miri.Interpreter.CompilerExecutionProviders.scalarClass facts 0 = .ok .boolean := by
  rcases facts with ⟨⟨document, target⟩, program, lowering⟩
  change document = _ at source
  subst document
  rfl

variable {K U : Type}
local notation "State" => MachineHooks.State K U

/-- Initialized byte storage of a live allocation in allocation-relative coordinates. -/
structure InitializedRegion (before : State) (length : UInt64) where
  id : AllocId
  relativeStart : Size
  entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K
  live : before.machine.memory.live[id]? = some entry
  writable : entry.allocation.mutability = .Mut
  backed : entry.allocation.len = entry.allocation.byteSize.bytes.toNat
  fits : relativeStart.bytes.toNat + length.toNat ≤ entry.allocation.byteSize.bytes.toNat
  initialized : length ≠ 0 →
    entry.allocation.initializationMask.isRangeInitialized
      (allocRange relativeStart (Size.ofBytes length)) = .ok (.ok ())

/-- Bind the slice and count to the actual argument slots of the prepared root. -/
structure EntryArguments (program : BodyVCGen.LoadedProgram) (before : State)
    (target : TargetDataLayout) (pointer : Pointer (Option Provenance))
    (length count : UInt64) : Prop where
  bound : ∃ frame buffer,
    before.stack.currentFrame? = some frame ∧
    frame.bodyIdentity = program.root.identity ∧ frame.body = program.root.body ∧
    frame.location = .mir ⟨0, 0⟩ ∧
    Immediate.newSlice pointer length target = .ok buffer ∧
    (frame.locals[1]?.map (·.value)) = some (.live (.immediate buffer)) ∧
    (frame.locals[2]?.map (·.value)) =
      some (.live (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 count)))))

theorem EntryArguments.entered {program : BodyVCGen.LoadedProgram} {before : State}
    {target : TargetDataLayout} {pointer : Pointer (Option Provenance)} {length count : UInt64}
    (entry : EntryArguments program before target pointer length count) :
    WholeBodyWP.entryMatchesLoaded program.root before := by
  obtain ⟨frame, _, current, identity, body, location, _⟩ := entry.bound
  exact ⟨frame, current, identity, body, location⟩

variable {C : Type}

private theorem notTrue (hooks : ScalarOpsHooks Provenance State C)
    (choice : C) (layout : LocalLayout) (before afterClassify afterLayout : State)
    (classified : (hooks.classify choice layout.ty).run before =
      .ok .boolean afterClassify)
    (boolLayout : (hooks.boolLayout choice).run afterClassify =
      .ok layout afterLayout) :
    (ScalarOps.unary hooks choice .Not
      ⟨.scalar (Scalar.fromBool true), layout⟩).run before =
      .ok ⟨.scalar (Scalar.fromBool false), layout⟩ afterLayout := by
  simp only [EStateM.run] at classified boolLayout
  simp only [ScalarOps.unary, EStateM.run, bind, Bind.bind, EStateM.bind, classified]
  conv => lhs; cbv
  cbv at boolLayout
  rw [boolLayout]
  rfl

private theorem eqFalse (hooks : ScalarOpsHooks Provenance State C)
    (choice : C) (layout : LocalLayout) (before classified laidOut : State)
    (classification : (hooks.classify choice layout.ty).run before = .ok .boolean classified)
    (boolLayout : (hooks.boolLayout choice).run classified = .ok layout laidOut) :
    (ScalarOps.binary hooks choice .Eq ⟨.scalar (Scalar.fromBool false), layout⟩
      ⟨.scalar (Scalar.fromBool false), layout⟩).run before =
      .ok ⟨.scalar (Scalar.fromBool true), layout⟩ laidOut := by
  simp only [EStateM.run] at classification boolLayout
  simp only [ScalarOps.binary, EStateM.run, bind, Bind.bind, EStateM.bind, classification]
  conv => lhs; cbv
  cbv at boolLayout
  rw [boolLayout]
  rfl

/-- Execute the Boolean operator under the real compiler-bound scalar
dictionary for the exported helper. The Boolean layout is a compiler query,
and the operator neither reads nor mutates the arbitrary machine state. -/
theorem languageCheckRuntimeScalar
    (facts : Miri.Input.CompilerFacts.Context)
    (source : facts.runtime.source = GeneratedBodySafety.input.document)
    (floats : FloatOpsHooks Provenance State C) (base : ScalarOpsHooks Provenance State C)
    (choice : C) (layout : LocalLayout) (before : State) (type : layout.ty = 0)
    (boolLayout : facts.runtime.findKind .bool = .ok layout) :
    (ScalarOps.unary (Miri.Interpreter.CompilerExecutionProviders.scalarHooks facts floats base)
      choice .Not ⟨.scalar (Scalar.fromBool true), layout⟩).run before =
      .ok ⟨.scalar (Scalar.fromBool false), layout⟩ before := by
  apply notTrue _ _ _ _ before
  · simp only [Miri.Interpreter.CompilerExecutionProviders.scalarHooks, type,
      languageCheckRuntimeCompilerClass facts source]
    rfl
  · simp only [Miri.Interpreter.CompilerExecutionProviders.scalarHooks, boolLayout]
    rfl

private def runExportedAssignment (hooks : RvalueHooks Provenance State C ExecutionMachine.Value)
    (choice : C) (body block index : Nat) : MachineHooks.M K U Unit :=
  match atStatement body block index with
  | some (.Assign destination expression) => evalRvalueIntoPlace hooks choice expression destination
  | _ => throw (.invalidProgram "expected exported assignment")

variable {O X Host : Type} [DecidableEq K]

private def boolOperand (value : Bool) (layout : LocalLayout) : OpTy Provenance :=
  ⟨.immediate (.scalar (Scalar.fromBool value)), layout⟩

/-- Reading a Boolean immediate follows the real memory-operand path but
does not dereference the caller's slice or touch an allocation. -/
theorem readBooleanImmediate (access : PlaceMachine.AccessConfig K U)
    (layout : LocalLayout) (before : State) (value : Bool)
    (primitive : Miri.Interpreter.isPrimitiveReadable layout.layout.backendRepr = true) :
    (PlaceMachine.readImmediate access (boolOperand value layout)).run before =
      .ok ⟨.scalar (Scalar.fromBool value), layout⟩
        { before with machine := access.retainTouched before.machine none } := by
  simp only [PlaceMachine.readImmediate, Miri.Interpreter.readImmediate, boolOperand,
    localMemoryLayout, primitive, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The exported helper assignment writes `false` through the production
rvalue dictionary. These local hypotheses describe place and operand
evaluation and the compiler's layouts. The Boolean is derived by the
actual unary evaluator, before invoking the write operation. -/
theorem languageCheckRuntimeAssignment
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (layout : LocalLayout) (place : ExecutionMachine.Value) (operand : OpTy Provenance)
    (before prepared evaluated read classified laidOut : State)
    (hooks : RvalueHooks Provenance State C ExecutionMachine.Value)
    (dictionary : hooks = ExecutionMachine.rvalueHooks config limits)
    (destination : (hooks.evalPlace choice (atLocal 0) true).run before = .ok place prepared)
    (placeType : hooks.placeLayout place = layout)
    (constant : (hooks.evalOperand choice (.Constant (boolConstant 1 ⟨350⟩))
      (some layout)).run prepared = .ok operand evaluated)
    (immediate : (hooks.readImmediate choice operand).run evaluated =
      .ok ⟨.scalar (Scalar.fromBool true), layout⟩ read)
    (classification : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
      choice layout.ty).run read = .ok .boolean classified)
    (boolLayout : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
      choice).run classified = .ok layout laidOut) :
    (runExportedAssignment hooks choice 19 0 0).run before =
      (hooks.writeImmediate choice (.scalar (Scalar.fromBool false)) place).run laidOut := by
  have unary : (hooks.unaryOp choice .Not
      ⟨.scalar (Scalar.fromBool true), layout⟩).run read =
      .ok ⟨.scalar (Scalar.fromBool false), layout⟩ laidOut := by
    rw [dictionary]
    exact notTrue _ _ _ _ _ _ classification boolLayout
  simp only [EStateM.run] at destination constant immediate unary
  simp only [runExportedAssignment, languageCheckRuntimeCode, evalRvalueIntoPlace,
    EStateM.run, bind, Bind.bind, EStateM.bind, destination, placeType]
  have homogeneous : UnOp.homogeneous .Not = true := rfl
  simp only [homogeneous, ↓reduceIte, constant, immediate, unary]
  conv => lhs; cbv
  rfl

private def selectExportedSwitch
    (hooks : TerminatorHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState K U) C (OpTy Provenance) (RvalueImmTy Provenance))
    (choice : C) (value : RvalueImmTy Provenance) (body block : Nat) (before : State) :
    StepResult State BasicBlockId :=
  match atTerminator body block with
  | some (.SwitchInt _ targets) => ControlFlow.selectSwitchTarget hooks choice value targets before
  | _ => (before, .error (.invalidProgram "expected exported switch"))

private theorem compareBooleanZero
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (layout : LocalLayout) (before classified laidOut : State)
    (width : layout.layout.size = Size.ofBytes 1)
    (classification : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
      choice layout.ty).run before = .ok .boolean classified)
    (boolLayout : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
      choice).run classified = .ok layout laidOut) :
    (ExecutionMachine.terminatorHooks config limits).compareSwitchCase choice
      ⟨.scalar (Scalar.fromBool false), layout⟩ 0 before = (laidOut, .ok true) := by
  have compared := eqFalse _ _ _ _ _ _ classification boolLayout
  simp only [EStateM.run] at compared
  simp only [MachineHooks.run, Call.run, bind, Bind.bind, EStateM.bind, width]
  generalize ScalarOps.binary (ExecutionMachine.scalarHooks
    (ExecutionMachine.withValidation config limits)) choice .Eq = compare at *
  conv => lhs; cbv
  cbv at compared
  erw [compared]
  rfl

/-- The real Boolean case comparison selects the false arm of the
exported dispatch, bypassing the runtime-check flag. -/
theorem languageCheckFalseSuccessor
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (layout : LocalLayout) (before classified laidOut : State)
    (width : layout.layout.size = Size.ofBytes 1)
    (classification : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
      choice layout.ty).run before = .ok .boolean classified)
    (boolLayout : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
      choice).run classified = .ok layout laidOut) :
    selectExportedSwitch (ExecutionMachine.terminatorHooks config limits) choice
      ⟨.scalar (Scalar.fromBool false), layout⟩ 9 1 before = (laidOut, .ok 3) := by
  have compared := compareBooleanZero config limits choice layout before classified laidOut
    width classification boolLayout
  simp only [selectExportedSwitch, languageCheckSwitch]
  generalize (ExecutionMachine.terminatorHooks config limits) = hooks at *
  conv => lhs; cbv
  cbv at compared
  rw [compared]
  rfl

/-- The imported helper's real switch transfers to the false arm after
reading the callee's Boolean return. The result includes the actual state
update performed by the jump. -/
theorem languageCheckBranchJump
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (layout : LocalLayout) (before read classified laidOut : State)
    (width : layout.layout.size = Size.ofBytes 1)
    (value : (ExecutionMachine.terminatorHooks config limits).evalDiscriminant choice
      (.Move (atLocal 1)) before = (read, .ok ⟨.scalar (Scalar.fromBool false), layout⟩))
    (classification : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
      choice layout.ty).run read = .ok .boolean classified)
    (boolLayout : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
      choice).run classified = .ok layout laidOut) :
    ControlFlow.evalSwitchInt (ExecutionMachine.terminatorHooks config limits) choice
      (.Move (atLocal 1)) ⟨#[.Case 0 3], 2⟩ before = ControlFlow.goToBlock 3 laidOut := by
  have selected := languageCheckFalseSuccessor config limits choice layout read classified laidOut
    width classification boolLayout
  simp only [selectExportedSwitch, languageCheckSwitch] at selected
  unfold ControlFlow.evalSwitchInt
  rw [value]
  simp only [bind, Bind.bind, pure, Pure.pure, Id.run, selected]

private def runtimeExpression : Rvalue := .UnaryOp .Not (.Constant (boolConstant 1 ⟨350⟩))

/-- Lift the actual imported helper assignment to a source machine step.
All driver checks and the next local PC remain those of the live frame. -/
theorem stepRuntimeGuardAssignment
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (layout : LocalLayout) (place : ExecutionMachine.Value) (operand : OpTy Provenance)
    (before prepared evaluated read classified laidOut : State)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (current : before.stack.currentFrame? = some frame)
    (source : GeneratedBodySafety.input.document.bodies[19]?.map (·.mir) = some frame.body)
    (location : frame.location = .mir ⟨0, 0⟩) :
    let checked := ExecutionMachine.withValidation config limits
    let hooks := ExecutionMachine.rvalueHooks checked limits
    (hooks.evalPlace choice (atLocal 0) true).run before = .ok place prepared →
    hooks.placeLayout place = layout →
    (hooks.evalOperand choice (.Constant (boolConstant 1 ⟨350⟩))
      (some layout)).run prepared = .ok operand evaluated →
    (hooks.readImmediate choice operand).run evaluated = .ok ⟨.scalar (Scalar.fromBool true), layout⟩ read →
    ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation checked limits)).classify
      choice layout.ty).run read = .ok .boolean classified →
    ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation checked limits)).boolLayout
      choice).run classified = .ok layout laidOut →
    ExecutionMachine.step config limits choice before = Step.finishStatement
      (before.stack.frames.size - 1)
      (MachineHooks.run (hooks.writeImmediate choice (.scalar (Scalar.fromBool false)) place) laidOut) := by
  intro checked hooks destination placeType constant immediate classification boolLayout
  have matching : (StepWP.Instruction.statement (.Assign (atLocal 0) runtimeExpression)).matches before := by
    unfold StepWP.Instruction.matches
    simp only [current, location]
    have first := congrArg (fun code : Option Body =>
      code.bind fun body => body.basicBlocks[0]?.bind fun block => block.statements[0]?.map (·.kind)) source
    change some (StatementKind.Assign (atLocal 0) runtimeExpression) =
      (frame.body.basicBlocks[0]?.bind fun block => block.statements[0]?.map (·.kind)) at first
    cases block : frame.body.basicBlocks[0]? with
    | none => simp [block] at first
    | some codeBlock =>
      cases slot : codeBlock.statements[0]? with
      | none => simp [block, slot] at first
      | some stmt =>
        simp only [block, slot, Option.bind_some, Option.map_some, Option.some.injEq] at first
        simpa [block, slot] using first.symm
  unfold ExecutionMachine.step
  rw [StepWP.step_eq_assign matching, ExecutionMachine.stepHooks_assign]
  have result := languageCheckRuntimeAssignment checked limits choice layout place operand
    before prepared evaluated read classified laidOut hooks rfl
    destination placeType constant immediate classification boolLayout
  simp only [runExportedAssignment, languageCheckRuntimeCode] at result
  unfold MachineHooks.run Call.run
  rw [show evalRvalueIntoPlace hooks choice runtimeExpression (atLocal 0) before =
    hooks.writeImmediate choice (.scalar (Scalar.fromBool false)) place laidOut from result]

private def pointerAddTargets : SwitchTargets := ⟨#[.Case 0 5], 2⟩

theorem pointerAddSwitchCode :
    atTerminator 4 1 = some (.SwitchInt (.Move (atLocal 4)) pointerAddTargets) := by rfl

/-- The current pointer-add switch sends the actual false guard result to
bb5, bypassing the additional debug precondition branch. -/
theorem pointerAddFalseJump
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (layout : LocalLayout) (before read classified laidOut : State)
    (width : layout.layout.size = Size.ofBytes 1)
    (value : (ExecutionMachine.terminatorHooks config limits).evalDiscriminant choice
      (.Move (atLocal 4)) before = (read, .ok ⟨.scalar (Scalar.fromBool false), layout⟩))
    (classification : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
      choice layout.ty).run read = .ok .boolean classified)
    (boolLayout : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
      choice).run classified = .ok layout laidOut) :
    ControlFlow.evalSwitchInt (ExecutionMachine.terminatorHooks config limits) choice
      (.Move (atLocal 4)) pointerAddTargets before = ControlFlow.goToBlock 5 laidOut := by
  have compared := compareBooleanZero config limits choice layout read classified laidOut
    width classification boolLayout
  have selected : ControlFlow.selectSwitchTarget (ExecutionMachine.terminatorHooks config limits) choice
      ⟨.scalar (Scalar.fromBool false), layout⟩ pointerAddTargets read = (laidOut, .ok 5) := by
    generalize (ExecutionMachine.terminatorHooks config limits) = hooks at *
    conv => lhs; cbv
    cbv at compared
    rw [compared]
    rfl
  unfold ControlFlow.evalSwitchInt
  rw [value]
  simp only [bind, Bind.bind, pure, Pure.pure, Id.run, selected]

end DuplicatePrefix.PreparedArguments

#print axioms DuplicatePrefix.PreparedArguments.EntryArguments.entered
#print axioms DuplicatePrefix.PreparedArguments.languageCheckRuntimeAssignment
#print axioms DuplicatePrefix.PreparedArguments.languageCheckFalseSuccessor
#print axioms DuplicatePrefix.PreparedArguments.languageCheckBranchJump

#print axioms DuplicatePrefix.PreparedArguments.stepRuntimeGuardAssignment

#print axioms DuplicatePrefix.PreparedArguments.pointerAddFalseJump

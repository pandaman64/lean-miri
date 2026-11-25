import Copy
import GeneratedCopyRows

namespace PointerObservation.Copy

open Miri.Interpreter Miri.Verification Miri.Memory Miri.MIR Fixture

/-- The emitted window checks the same executable copy observation, with a
finite endpoint after the load and the actual failed state on invalidation. -/
theorem generatedPrefix_iff_checked (source destination : UInt8) (stale : Bool) :
    (match scenario source destination stale with
    | .error _ => False
    | .ok (config, entry) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun after => stale = false ∧ scalarAt after 0 = some source)
        (fun error after => stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source]))
        ((GeneratedBodySafety.window_0_bb0_5 config limits).take 6) entry) ↔
      checked source destination stale = true := by
  rw [← required_iff_checked]
  cases each : scenario source destination stale with
  | error error => simp only [required, each]
  | ok entered =>
    obtain ⟨config, entry⟩ := entered
    simp only [required, each]
    exact (prefixPre_iff_windowPrefixPre config _ _ 5 rows
      ((GeneratedBodySafety.window_0_bb0_5 config limits).take 6) entry (by rfl)).symm

private theorem cachedMove
    (hooks : OperandMachine.Hooks MiriMemoryKind EmptyFunction.Configuration.RootUser Unit)
    (before : State) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (id : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (current : before.stack.currentFrame? = some frame)
    (cached : frame.getLocal id = .ok (localImmediate value (some layout)))
    (sized : layout.layout.backendRepr.isUnsized = false)
    (validating : hooks.compiler.validationInProgress before = .ok false before)
    (noClock : frame.extra.dataRace = none)
    (typeCheck : hooks.checkPlaceType () ⟨id, #[]⟩ ⟨.immediate value, layout⟩ before = .ok () before) :
    OperandMachine.evalOperand hooks () (.Move ⟨id, #[]⟩) none before =
      .ok ⟨.immediate value, layout⟩ before := by
  have found : frame.getLocalOperand id = .ok (.immediate value) := by
    simp only [Frame.getLocalOperand, cached, bind, Bind.bind, Except.bind]
    rfl
  have observed : RvalueWP.actionPre
      (OperandMachine.evalOperand hooks () (.Move ⟨id, #[]⟩) none)
      (fun op after => op = ⟨.immediate value, layout⟩ ∧ after = before)
      (fun _ _ => False) before := by
    simp only [OperandPlaceWP.actionPre_evalOperand, OperandPlaceWP.actionPre_evalPlaceToOpLocal,
      OperandPlaceWP.localOperandPre, StorageLiveWP.currentFramePre, current, cached, Except.mapError,
      RvalueWP.scalarCheckPre, localImmediate, found, sized, Bool.false_eq_true, ↓reduceIte,
      RvalueWP.actionPre_ok validating, OperandPlaceWP.actionPre_afterLocalRead,
      OperandPlaceWP.localReadClockPre, noClock, RvalueWP.actionPre_ok typeCheck, and_self]
  cases ran : OperandMachine.evalOperand hooks () (.Move ⟨id, #[]⟩) none before with
  | error => simp only [RvalueWP.actionPre, ran] at observed
  | ok op after =>
    simp only [RvalueWP.actionPre, ran] at observed
    rw [observed.1, observed.2]

/-- The saved intrinsic consumes its actual evaluated operands in order.
The assumptions concern only operand evaluation. The scalar conversions,
compiler layout, alignment, live memory, permissions, commit, and following
continuation remain obligations of the resulting predicate. -/
theorem reduceEvaluatedCopyOperands
    (config : Config) (post : Bool → State → Prop) (failure : StepError → State → Prop)
    (before afterSource afterDestination afterCount : State)
    (operands : CopyNonOverlapping) (source destination count : OpTy Provenance)
    (selected : GeneratedBodySafety.mir_0_bb0_5 =
      .statement (.Intrinsic (.CopyNonOverlapping operands)))
    (sourceRead : OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () operands.source none before = .ok source afterSource)
    (destinationRead : OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () operands.destination none afterSource = .ok destination afterDestination)
    (countRead : OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () operands.count none afterDestination = .ok count afterCount) :
    (GeneratedBodySafety.transfer_0_bb0_5 config limits).pre () post failure before ↔
      let checked := ExecutionMachine.withValidation config limits
      NondivergingIntrinsicWP.copyPreUsing (ExecutionMachine.memoryIntrinsicHooks checked)
        (fun src dst size nonoverlap => CopyTreeWP.copyPre checked.access checked.addresses
          checked.arithmetic src dst size 1 nonoverlap)
        () source destination count true
        (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post failure)
        failure afterCount := by
  rw [(GeneratedBodySafety.transfer_0_bb0_5 config limits).exact]
  change BodyCFG.nodePre config limits () post failure before GeneratedBodySafety.mir_0_bb0_5 ↔ _
  rw [selected]
  simp only [BodyCFG.nodePre, NondivergingIntrinsicWP.statementPre_intrinsic,
    NondivergingIntrinsicWP.evalPre, RvalueWP.actionPre_ok sourceRead,
    RvalueWP.actionPre_ok destinationRead, RvalueWP.actionPre_ok countRead,
    NondivergingIntrinsicWP.copyPre, CopyTreeWP.copyActionPre_eq]

private def importedOperands : Option CopyNonOverlapping :=
  match GeneratedBodySafety.mir_0_bb0_5 with
  | .statement (.Intrinsic (.CopyNonOverlapping operands)) => some operands
  | _ => none

private theorem operandsPresent : importedOperands.isSome = true := rfl

def copyOperands : CopyNonOverlapping := importedOperands.get operandsPresent

/-- The exported copy row reads its two immediate pointer locals from the
initial cached frame. The premises specify the frame and its policy facts,
the two cached layouts, the compiler type checks, and the constant operand.
The right-hand side still checks scalar/count conversions, pointee layout,
alignment, and both allocation accesses before committing the copied bytes.
Its success continuation can be the subsequent generated load. -/
theorem reduceCachedCopyOperands
    (config : Config) (post : Bool → State → Prop) (failure : StepError → State → Prop)
    (before afterCount : State) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (source destination : Immediate Provenance) (sourceLayout destinationLayout : LocalLayout)
    (count : OpTy Provenance)
    (current : before.stack.currentFrame? = some frame)
    (sourceCached : frame.getLocal 5 = .ok (localImmediate source (some sourceLayout)))
    (destinationCached : frame.getLocal 6 = .ok (localImmediate destination (some destinationLayout)))
    (sourceSized : sourceLayout.layout.backendRepr.isUnsized = false)
    (destinationSized : destinationLayout.layout.backendRepr.isUnsized = false)
    (noClock : frame.extra.dataRace = none)
    (validation :
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).compiler.validationInProgress
        before = .ok false before)
    (sourceTyped :
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).checkPlaceType
        () ⟨5, #[]⟩ ⟨.immediate source, sourceLayout⟩ before = .ok () before)
    (destinationTyped :
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).checkPlaceType
        () ⟨6, #[]⟩ ⟨.immediate destination, destinationLayout⟩ before = .ok () before)
    (constant :
      OperandMachine.evalOperand (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
        () copyOperands.count none before = .ok count afterCount) :
    (GeneratedBodySafety.transfer_0_bb0_5 config limits).pre () post failure before ↔
      let checked := ExecutionMachine.withValidation config limits
      NondivergingIntrinsicWP.copyPreUsing (ExecutionMachine.memoryIntrinsicHooks checked)
        (fun src dst size nonoverlap => CopyTreeWP.copyPre checked.access checked.addresses
          checked.arithmetic src dst size 1 nonoverlap)
        () ⟨.immediate source, sourceLayout⟩ ⟨.immediate destination, destinationLayout⟩ count true
        (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post failure)
        failure afterCount := by
  exact reduceEvaluatedCopyOperands config post failure before before before afterCount copyOperands _ _ count
    rfl (cachedMove _ before frame 5 source sourceLayout current sourceCached sourceSized validation
      noClock sourceTyped)
    (cachedMove _ before frame 6 destination destinationLayout current destinationCached destinationSized
      validation noClock destinationTyped)
    constant

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``generatedPrefix_iff_checked, ``reduceCachedCopyOperands] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms generatedPrefix_iff_checked
#print axioms reduceCachedCopyOperands

end PointerObservation.Copy

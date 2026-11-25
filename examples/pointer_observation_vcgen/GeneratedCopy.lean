import Copy
import CopyObserver
import CopyPhysical
import CopyTail
import Miri.Memory.ProvenanceMapVerification
import GeneratedCopyRows

namespace PointerObservation.Copy

open Miri.ABI Miri.Interpreter Miri.Verification Miri.Memory Miri.MIR Miri.TreeBorrows Fixture

/-- The actual emitted six-row copy and observer window. -/
def generatedPrefix (source destination : UInt8) (stale : Bool) : Prop :=
  match scenario source destination stale with
  | .error _ => False
  | .ok (config, entry) =>
    GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
      (fun after => stale = false ∧ scalarAt after 0 = some source)
      (fun error after => stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source]))
      ((GeneratedBodySafety.window_0_bb0_5 config limits).take 6) entry

/-- The executable observation checker and the emitted window agree. -/
theorem generatedPrefix_iff_checked (source destination : UInt8) (stale : Bool) :
    generatedPrefix source destination stale ↔ checked source destination stale = true := by
  unfold generatedPrefix
  rw [← required_iff_checked]
  cases each : scenario source destination stale with
  | error error => simp only [required, each]
  | ok entered =>
    obtain ⟨config, entry⟩ := entered
    simp only [required, each]
    exact (prefixPre_iff_windowPrefixPre config _ _ 5 rows
      ((GeneratedBodySafety.window_0_bb0_5 config limits).take 6) entry (by rfl)).symm

set_option maxHeartbeats 500000 in
set_option maxRecDepth 40000 in
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail in
private theorem entrySelected (source destination : UInt8) (stale : Bool) :
    (scenario source destination stale).toOption.bind (fun entry => BodyCFG.selected entry.2) =
      some (⟨0, 5⟩, mir_0_bb0_5) := by
  cbv

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

set_option maxHeartbeats 1100000 in
set_option maxRecDepth 65536 in
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail in
private theorem copyPreflight
    (source destination : UInt8) (stale : Bool)
    (copy : Pointer (Option Provenance) → Pointer (Option Provenance) → Size → Bool →
      (Unit → State → Prop) → (StepError → State → Prop) → State → Prop)
    (post : State → Unit → State → Prop) (failure : StepError → State → Prop) :
    match scenario source destination stale with
    | .error _ => False
    | .ok (config, before) =>
      let checked := ExecutionMachine.withValidation config limits
      let hooks := ExecutionMachine.memoryIntrinsicHooks checked
      let read := fun operand => OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) () operand none
      RvalueWP.actionPre (read copyOperands.source) (fun src =>
        RvalueWP.actionPre (read copyOperands.destination) (fun dst =>
          RvalueWP.actionPre (read copyOperands.count) (fun count =>
            NondivergingIntrinsicWP.copyPreUsing hooks copy () src dst count true (post before) failure)
          failure) failure) failure before =
        copy (pointer BorTag.one 0).withOptionalProvenance (pointer BorTag.one 1).withOptionalProvenance
          (Size.ofBytes 1) true (post before) failure before := by
  cbv

/-- On the imported initial state, the emitted copy row's operand evaluation,
compiler queries and alignment checks pass a one-byte copy to the memory rule.
The memory rule still checks live allocations and Tree Borrows and passes the
actual resulting machine to the statement continuation. -/
theorem reduceInitialCopy (source destination : UInt8) (stale : Bool)
    (config : Config) (before : State) (entry : scenario source destination stale = .ok (config, before))
    (post : Bool → State → Prop) (failure : StepError → State → Prop) :
    (GeneratedBodySafety.transfer_0_bb0_5 config limits).pre () post failure before ↔
      let checked := ExecutionMachine.withValidation config limits
      CopyTreeWP.copyPre checked.access checked.addresses checked.arithmetic
        (pointer BorTag.one 0).withOptionalProvenance (pointer BorTag.one 1).withOptionalProvenance
        (Size.ofBytes 1) 1 true
        (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post failure)
        failure before := by
  let checked := ExecutionMachine.withValidation config limits
  have evaluated := copyPreflight source destination stale
    (fun src dst size nonoverlap => CopyTreeWP.copyPre checked.access checked.addresses
      checked.arithmetic src dst size 1 nonoverlap)
    (fun initial _ => InstructionWP.finishStatementResultPre (initial.stack.frames.size - 1) post failure)
    failure
  simp only [entry] at evaluated
  rw [(GeneratedBodySafety.transfer_0_bb0_5 config limits).exact]
  change BodyCFG.nodePre config limits () post failure before GeneratedBodySafety.mir_0_bb0_5 ↔ _
  rw [show GeneratedBodySafety.mir_0_bb0_5 =
    .statement (.Intrinsic (.CopyNonOverlapping copyOperands)) from rfl]
  simp only [BodyCFG.nodePre, NondivergingIntrinsicWP.statementPre_intrinsic,
    NondivergingIntrinsicWP.evalPre, NondivergingIntrinsicWP.copyPre, CopyTreeWP.copyActionPre_eq]
  exact Iff.of_eq evaluated

set_option maxHeartbeats 1400000 in
set_option maxRecDepth 65536 in
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail in
attribute [local cbv_opaque] CopyMemoryWP.snapshotPre in
section

set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
attribute [local cbv_opaque] Allocation.Bridge.copyRepeatedlyPre

private theorem prepareByteSnapshot (data : Array UInt8) :
    (ProvenanceMap.new (Prov := Provenance)).prepareCopy
      ({start := ⟨⟨0#64⟩⟩, size := ⟨1⟩}) data ⟨⟨8#64⟩⟩ =
        .ok ⟨#[], #[]⟩ :=
  ProvenanceMap.prepareCopy_new _ _ _ (Size.ofBytes 1) (by decide) (by decide)

attribute [local cbv_opaque] ProvenanceMap.new ProvenanceMap.prepareCopy
attribute [local cbv_eval] prepareByteSnapshot

/-- Evaluate memory access and physical copy at the fixture's concrete
allocation and ranges, carrying the actual committed state into the next row. -/
private theorem copyMemoryAndAdvance (source destination : UInt8) (stale : Bool)
    (accept : Bool → State → Prop)
    (failure : StepError → State → Prop) :
    match scenario source destination stale with
    | .error _ => False
    | .ok (config, before) =>
      let checked := ExecutionMachine.withValidation config limits
      CopyTreeWP.copyPre checked.access checked.addresses checked.arithmetic
        (pointer BorTag.one 0).withOptionalProvenance (pointer BorTag.one 1).withOptionalProvenance
        (Size.ofBytes 1) 1 true
        (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) accept failure)
        failure before =
      match postCopyTree source stale with
      | some (_, after) => accept true after
      | none => False := by
  cbv
  change
    Allocation.Bridge.copyRepeatedlyPre
      ((unitImage source destination).withExtra ?readTree)
      (allocRange Size.ZERO (Size.ofBytes 1)) (Size.ofBytes 1) 1 (Size.ofBytes 8)
      true true ?commit ?reject ((unitImage source destination).withExtra ?writeTree) = _
  rw [physicalCopyPre]
  cbv

private theorem copyConfig (source destination : UInt8) (stale : Bool) :
    ((scenario source destination stale).toOption.map Prod.fst) =
      (postCopyTree source stale).map Prod.fst := by
  cbv

end

/-- Discharge the first emitted row and route its committed state through
the remaining five statements. -/
theorem checked_of_copy_suffix (source destination : UInt8) (stale : Bool)
    (suffix : match postCopyTree source stale with
      | none => False
      | some (config, after) =>
        prefixPre config
          (fun final => stale = false ∧ scalarAt final 0 = some source)
          (fun error final => stale = true ∧ error = disabledLoad ∧ bytesAt 1 final = some (.ok #[source]))
          6 rows.tail after) :
    checked source destination stale = true := by
  rw [← required_iff_checked, required]
  have selected := entrySelected source destination stale
  cases entry : scenario source destination stale with
  | error error =>
    simp only [entry, Except.toOption, Option.bind_none] at selected
    cases selected
  | ok entered =>
    obtain ⟨config, before⟩ := entered
    simp only [entry, Except.toOption, Option.bind_some] at selected
    change prefixPre config _ _ 5 (mir_0_bb0_5 :: rows.tail) before
    rw [prefixPre]
    refine ⟨selected, ?_⟩
    refine ((GeneratedBodySafety.transfer_0_bb0_5 config limits).exact () _ _ before).mp ?_
    rw [reduceInitialCopy source destination stale config before entry]
    have copy := copyMemoryAndAdvance source destination stale
      (fun more after => more = true ∧ prefixPre config
        (fun final => stale = false ∧ scalarAt final 0 = some source)
        (fun error final => stale = true ∧ error = disabledLoad ∧ bytesAt 1 final = some (.ok #[source]))
        6 rows.tail after)
      (fun error final => stale = true ∧ error = disabledLoad ∧ bytesAt 1 final = some (.ok #[source]))
    simp only [entry] at copy
    rw [copy]
    cases next : postCopyTree source stale with
    | none => simp only [next] at suffix
    | some after =>
      obtain ⟨resumedConfig, resumed⟩ := after
      have same := copyConfig source destination stale
      rw [entry, next] at same
      have sameConfig : config = resumedConfig := Option.some.inj same
      exact ⟨trivial, by simpa only [next, sameConfig] using suffix⟩

private theorem checked_initialCopy (source destination : UInt8) (stale : Bool) :
    checked source destination stale = true := by
  apply checked_of_copy_suffix source destination stale
  refine (postCopyTreeSuffix source stale
    (fun final => stale = false ∧ scalarAt final 0 = some source)
    (fun error final => stale = true ∧ error = disabledLoad ∧ bytesAt 1 final = some (.ok #[source]))).mpr ?_
  cases unitLayout : row6Layout with
  | none =>
    have ready := row6LayoutReady
    simp only [unitLayout, Option.isSome_none, Bool.false_eq_true] at ready
  | some layout =>
    have observed := postCopyLoad_observation source stale layout
    cases next : postCopyLoadEntry source stale layout with
    | none => simp only [next] at observed
    | some pair =>
      obtain ⟨config, after⟩ := pair
      simpa only [Option.bind_some, next] using observed

/-- With the root observer, the emitted six-row prefix succeeds and returns
the original source byte, for every pair of initial bytes. -/
theorem generatedCopyThenLoad (source destination : UInt8) :
    generatedPrefix source destination false :=
  (generatedPrefix_iff_checked source destination false).mpr (checked_initialCopy source destination false)

/-- With the stale child observer, the load in the emitted prefix returns
the exact Disabled-tag UB and the retained destination contains the copied byte. -/
theorem generatedCopyThenDisabledLoad (source destination : UInt8) :
    generatedPrefix source destination true :=
  (generatedPrefix_iff_checked source destination true).mpr (checked_initialCopy source destination true)

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``generatedPrefix_iff_checked, ``entrySelected,
      ``reduceCachedCopyOperands, ``reduceInitialCopy,
      ``copyMemoryAndAdvance, ``checked_of_copy_suffix, ``generatedCopyThenLoad, ``generatedCopyThenDisabledLoad] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms generatedPrefix_iff_checked
#print axioms reduceCachedCopyOperands
#print axioms reduceInitialCopy
#print axioms generatedCopyThenLoad
#print axioms generatedCopyThenDisabledLoad

end PointerObservation.Copy

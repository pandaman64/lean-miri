import duplicate_prefix.ReferenceVisitorFields
import duplicate_prefix.RetagReferencePlace
import duplicate_prefix.ReferenceMetadataFacts
import duplicate_prefix.CanonicalConfigFacts
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.CurrentReferenceLocalValidity
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
structure VisitorFields {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    : Prop where
  toOp : hooks.toOp = fun c place => placeToOp (ValidityMachine.placeHooks access allocation compiler) c place
  ghost : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
    @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance)
  read : hooks.readImmediate = fun c place expected => do
    let op ← placeToOp (ValidityMachine.placeHooks access allocation compiler) c place
    ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected
  write : hooks.writeNoValidate = fun c value destination => do
    let validate ← ValidityMachine.enforceValidity
    ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation compiler) c (fun _ => validate) value destination
  check : hooks.checkPointerAccess = fun _ => ValidityMachine.checkPointerAccessResult access
  align : hooks.checkPointerAlignResult = fun _ => ValidityMachine.checkPointerAlignResult access
  nonnull : hooks.scalarMayBeNull = fun _ => ValidityMachine.scalarMayBeNull

theorem reference_check_of_retag {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (prepared : CompilerFactAdapters.Prepared) (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C)
    (fields : VisitorFields hooks access allocation compiler)
    (reference pointee : LocalLayout) (id : AllocId) (parentTag childTag : BorTag) (base addressOffset len : UInt64)
    (nonzero : base + addressOffset ≠ 0)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : addressOffset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (pointerField : hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
      (CompilerExecutionProviders.pointerCompiler prepared))
    (_width : access.runtime.base.pointerWidth = .w64)
    (targetWidth : hooks.target.base.pointerWidth = .w64)
    (targetSize : hooks.target.pointerSize = Size.ofBytes 8)
    (pointeeUnsized : pointee.layout.isSized = false)
    (tail : hooks.metadataTail choice pointee.ty = pure .sliceOrStr)
    (inhabited : hooks.opsemInhabited choice pointee.ty = pure true)
    (name : String) (mutable : Bool)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = true)
    (retain : access.retainTouched = fun machine _ => machine)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (sizingAt : hooks.sizeAndAlign choice
      (RetagReferencePlace.slicePlace (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len pointee)
      (Storage.withCurrent frames frame machine) = .ok (some (Size.ofBytes len, Align.ONE))
      (Storage.withCurrent frames frame machine))
    (retaggedAt : hooks.retagPointer choice
      (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference)
      reference.ty (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference))
        (Storage.withCurrent frames afterFrame afterMachine)) :
    let state := Storage.withCurrent frames frame machine
    source_check_safe hooks choice (ReferenceValidity.referenceSession name)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) reference.ty (.reference mutable) state =
      .ok (ReferenceValidity.referenceSession name)
        (Storage.withCurrent frames
          {afterFrame with locals := (afterFrame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
              (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm),
             layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout} (by simpa [sameLocals] using valid))} afterMachine) := by
  let value := RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference
  let place := RetagReferencePlace.slicePlace (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len pointee
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let state := Storage.withCurrent frames frame machine
  let adjusted := RetagReferencePlace.sliceValue access.runtime.base
    (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference
  let after := Storage.withCurrent frames afterFrame afterMachine
  let written := Storage.withCurrent frames
    {afterFrame with locals := (afterFrame.locals.set localId
      {value := .live (.immediate adjusted.imm), layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
      (by simpa [sameLocals] using valid))} afterMachine
  have read : hooks.readImmediate choice destination .reference state = .ok value state := by
    rw [fields.read]
    exact ReferenceValidity.read_local_pair_ghost access allocation compiler choice frames frame machine localId
      reference _ _ valid live cached sized debug ghost pa pb ra rb offset repr retain .reference
  have construct : hooks.ptrToPlace choice value = pure place := by
    rw [pointerField]
    exact RetagReferencePlace.canonical_from_immediate access prepared choice _ len reference pointee
      dereference pointeeLayout pointeeAlign
  have metadata : source_check_metadata hooks choice place = pure () :=
    ReferenceValidity.metadata_slice hooks choice place len tail rfl targetSize
  have sizing : hooks.sizeAndAlign choice place state = .ok (some ((Size.ofBytes len), Align.ONE)) state := by
    exact sizingAt
  have check : hooks.checkPointerAccess choice place.mplace.ptr (Size.ofBytes len) state = .ok (.ok ()) state := by
    rw [fields.check]
    exact ReferenceChecks.check_result_cached pointers access state id parentTag base addressOffset len entry
      pointerWiring arithmetic cachedAddress present positive signedFits bounds
  have retagged : hooks.retagPointer choice value reference.ty state = .ok (some adjusted) after := retaggedAt
  have write : hooks.writeNoValidate choice adjusted.imm destination after = .ok () written := by
    rw [fields.write]
    simp only [destination, sameDestination]
    exact ReferenceValidity.visitor_write_local_ghost access allocation compiler choice frames afterFrame afterMachine localId
      value.imm adjusted.imm reference (by simpa [sameLocals] using valid)
      (by simpa [sameLocals] using live) (by simpa [sameLocals] using cached) sized debug
      noDebug ghostAfter
  have encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr =
      .ok (Scalar.fromPointer hooks.target.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset)))) := rfl
  have nonnull : hooks.scalarMayBeNull choice (Scalar.fromPointer hooks.target.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset)))) = pure false := by
    rw [fields.nonnull]
    exact ReferenceChecks.pointer_not_null hooks.target.base _ targetWidth nonzero
  have aligned : hooks.checkPointerAlignResult choice place.mplace.ptr Align.ONE written = .ok (.ok ()) written := by
    rw [fields.align]
    exact ReferenceChecks.alignment_one access place.mplace.ptr written
  exact ReferenceValidity.check_reference_stage_for hooks choice name mutable destination value adjusted place (Size.ofBytes len) Align.ONE
    _ state after written read construct pointeeUnsized metadata sizing check retagged write encoded nonnull inhabited aligned

theorem reference_validate_of_retag {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (prepared : CompilerFactAdapters.Prepared) (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choice : C) (fuel : Nat)
    (fields : VisitorFields hooks access allocation compiler)
    (reference pointee : LocalLayout) (id : AllocId) (parentTag childTag : BorTag) (base addressOffset len : UInt64)
    (nonzero : base + addressOffset ≠ 0)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : addressOffset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (pointerField : hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
      (CompilerExecutionProviders.pointerCompiler prepared))
    (width : access.runtime.base.pointerWidth = .w64)
    (targetWidth : hooks.target.base.pointerWidth = .w64)
    (targetSize : hooks.target.pointerSize = Size.ofBytes 8)
    (pointeeUnsized : pointee.layout.isSized = false)
    (tail : hooks.metadataTail choice pointee.ty = pure .sliceOrStr)
    (inhabited : hooks.opsemInhabited choice pointee.ty = pure true)
    (name : String) (mutable : Bool)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (offset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck (RetagReferencePlace.sliceValue access.runtime.base
      (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm reference = pure ())
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (sizingAt : hooks.sizeAndAlign choice
      (RetagReferencePlace.slicePlace (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len pointee)
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) = .ok (some (Size.ofBytes len, Align.ONE))
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}))
    (retaggedAt : hooks.retagPointer choice
      (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference)
      reference.ty (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference))
        (Storage.withCurrent frames afterFrame afterMachine))    (named : hooks.typeName choice reference.ty = pure name)
    (classified : hooks.classify choice reference.ty = pure (.reference mutable)) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) false true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue access.runtime.base
            (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
          (by simpa [sameLocals] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let destination := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let value := RetagReferencePlace.sliceValue access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + addressOffset))) len reference
  let adjusted := RetagReferencePlace.sliceValue access.runtime.base
    (Pointer.new (.concrete id childTag) (Size.ofBytes (base + addressOffset))) len reference
  let written := Storage.withCurrent frames
    {afterFrame with locals := (afterFrame.locals.set localId
      {value := .live (.immediate adjusted.imm),
       layout := (afterFrame.locals[localId]'(by simpa [sameLocals] using valid)).layout}
      (by simpa [sameLocals] using valid))} afterMachine
  have check := reference_check_of_retag hooks access allocation compiler prepared pointers choice
    fields reference pointee id parentTag childTag base addressOffset len nonzero entry pointerWiring arithmetic
    positive signedFits bounds dereference pointeeLayout pointeeAlign pointerField width targetWidth targetSize
    pointeeUnsized tail inhabited name mutable frames frame activeMachine localId valid live cached sized
    pa pb ra rb offset repr debug noDebug rfl retain cachedAddress present afterFrame afterMachine sameLocals
    sameDestination ghostAfter sizingAt retaggedAt
  have visited : ValidityVisitor.visit hooks choice (fuel + 1) (ReferenceValidity.referenceSession name)
      destination (Storage.withCurrent frames frame activeMachine) =
      .ok (ReferenceValidity.referenceSession name) written :=
    ReferenceValidity.visit_reference_of_check_for hooks choice fuel name mutable destination _ written classified check
  have toOp : hooks.toOp choice destination (Storage.withCurrent frames frame activeMachine) =
      .ok ⟨.immediate value.imm, reference⟩ (Storage.withCurrent frames frame activeMachine) := by
    rw [fields.toOp]
    exact ScalarCopyStage.place_to_op_ghost access allocation compiler choice frames frame activeMachine localId
      reference value.imm valid live cached sized debug rfl
  exact ReferenceValidity.validate_reference_shallow_of_visit hooks choice fuel name destination
    (Storage.withCurrent frames frame machine) written value.imm ghost ghostAfter named fields.ghost toOp visited

#print axioms reference_validate_of_retag


theorem actual_fields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    ∃ (pointers : CanonicalConfigFacts.RootPointers)
      (compiler : ValidityMachine.Compiler MiriMemoryKind CanonicalConfigFacts.RootStored Unit),
      VisitorFields cfg.validity cfg.access cfg.allocation compiler ∧
      compiler.debugAssertions = cfg.compiler.debugAssertions ∧
      compiler.debugAbiCheck = cfg.compiler.debugAbiCheck ∧
      cfg.validity.ptrToPlace =
        PointerPlaceMachine.fromImmediate cfg.access
          (CompilerExecutionProviders.pointerCompiler ReferenceMetadataFacts.prepared) ∧
      pointers.arithmetic = ⟨Size.ofBytes 8⟩ ∧
      cfg.access.resolvePointer = TypedMemoryProviders.resolvePointer pointers := by
  intro cfg
  obtain ⟨pointers, table, discriminant, globals, validity, arithmetic, resolve, _, _⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).validitySources
  let leaves := CompilerValidityLeaves.make PreparedReflection.actual.compiler PreparedReflection.actual.image
    EvalProjectionMachine.arrays cfg.projection pointers
  let base := ExecutionValidity.hooks leaves cfg.access cfg.allocation cfg.compiler
    cfg.projection table discriminant cfg.retag options.limits.retag
  have hooksEq : cfg.validity =
      TypedValidityProviders.visitor ReferenceMetadataFacts.prepared
        PreparedReflection.actual.compiler.lifecycle.calls.runtime cfg.access cfg.allocation cfg.compiler
        pointers cfg.retag options.limits.retag base := by
    exact validity
  obtain ⟨inner, debug, abi, toOp, read, write, pointer, check, align, nonnull, ghost, _⟩ :=
    ReferenceVisitorFields.typed_reference_fields ReferenceMetadataFacts.prepared
      PreparedReflection.actual.compiler.lifecycle.calls.runtime base cfg.access cfg.allocation cfg.compiler
      pointers cfg.retag options.limits.retag
  refine ⟨pointers, ValidityMachine.compilerPolicy inner, ?_, debug, abi, ?_, arithmetic, resolve⟩
  · rw [hooksEq]
    exact ⟨toOp, ghost, read, write, check, align, nonnull⟩
  · rw [hooksEq]
    exact pointer

end DuplicatePrefix.CurrentReferenceLocalValidity
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentReferenceLocalValidity.reference_check_of_retag,
      ``DuplicatePrefix.CurrentReferenceLocalValidity.reference_validate_of_retag] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved shared reference validation dependency {dependency}"

#print axioms DuplicatePrefix.CurrentReferenceLocalValidity.actual_fields

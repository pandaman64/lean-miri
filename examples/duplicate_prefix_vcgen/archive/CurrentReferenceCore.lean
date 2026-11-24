import duplicate_prefix.CurrentReferenceLocalValidity
import duplicate_prefix.CurrentReferenceMetadata
import duplicate_prefix.CurrentReferenceVisitor
import duplicate_prefix.CurrentReferenceLocalWrite

namespace DuplicatePrefix.CurrentReferenceCore
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open CanonicalConfigFacts CurrentReferenceMetadata

set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem validatePositiveAcrossFrame
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (fuel sizeFuel : Nat) (dynamicFuel : options.place.dynamicFuel = sizeFuel + 1)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame afterFrame : CompilerFrameContext.ActualFrame)
    (machine after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (reference : LocalLayout) (mutable : Bool) (ty : reference.ty = refTy mutable)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (pairOffset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := pairOffset))
    (id : AllocId) (parentTag childTag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (liveMemory : machine.memory.live[id]? = some entry)
    (nonzero : base + offset ≠ 0)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (sameLocals : afterFrame.locals = frame.locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (cached : frame.locals[localId].layout = some reference)
    (inactive : machine.user.payload.ghost = false)
    (activeAfter : after.user.payload.ghost = true)
    (shallow : machine.user.payload.validation = .Shallow)
    (comparator : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get
      (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (noArrayAlias : (EvalProjectionMachine.arrays.get
      (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let before := Storage.withCurrent frames frame machine
    let active := CurrentReferenceVisitor.ghost before true
    let parent := Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))
    let child := Pointer.new (.concrete id childTag) (Size.ofBytes (base + offset))
    let value := RetagReferencePlace.sliceValue cfg.access.runtime.base parent len reference
    let replacement := RetagReferencePlace.sliceValue cfg.access.runtime.base child len reference
    frame.locals[localId].value = .live (.immediate value.imm) →
    cfg.validity.retagPointer () value reference.ty active = .ok (some replacement) (Storage.withCurrent frames afterFrame after) →
    ValidityMachine.validateRuntime cfg.validity () (fuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true before =
      .ok () (Storage.withCurrent frames (CurrentReferenceLocalWrite.written afterFrame localId replacement.imm (by simpa [sameLocals] using valid))
        {after with user := {after.user with payload := {after.user.payload with ghost := false}}}) := by
  intro cfg before active parent child value replacement hasValue retagged
  obtain ⟨pointers, compiler, fields, debugField, abiField, pointer, arithmetic, resolve⟩ :=
    CurrentReferenceLocalValidity.actual_fields options remaining span
  have configFields := CanonicalConfigFacts.actual_fields options () remaining span
  have noDebug : compiler.debugAbiCheck replacement.imm reference = pure () := by
    rw [abiField, configFields.debugAbiNoChecks debugOff]
  have debug : compiler.debugAssertions = false := by
    rw [debugField, configFields.debug]
    exact debugOff
  have signedFits : len.toNat < 9223372036854775808 := by
    have b := UInt64.le_iff_toNat_le.mp bounded
    exact Nat.lt_of_le_of_lt b (by decide)
  let pointee := ProjectionMetadataFacts.sliceLayout
  have pointeeTy : pointee.ty = 2 := ProjectionMetadataFacts.slice_layout_shape.1
  have dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context reference.ty true =
      .ok (some pointee.ty) := by
    rw [ty, pointeeTy]
    cases mutable <;> with_unfolding_all rfl
  have layout : CompilerFacts.layoutOf ReferenceMetadataFacts.prepared.context pointee.ty = .ok pointee := by
    rw [pointeeTy]
    exact ActualCurrentSlice.compilerLayout
  have named : cfg.validity.typeName () reference.ty = pure (refName mutable) := by
    rw [ty]
    exact CurrentReferenceMetadata.named options remaining span mutable
  have classified : cfg.validity.classify () reference.ty = pure (.reference mutable) := by
    rw [ty]
    exact CurrentReferenceMetadata.classified options remaining span mutable
  let place := RetagReferencePlace.slicePlace parent len pointee
  have sizeAt : cfg.validity.sizeAndAlign () place active = .ok (some (Size.ofBytes len, Align.ONE)) active :=
    ProjectionMetadataFacts.actual_validity_size_at options remaining span comparator active sizeFuel dynamicFuel len
      metadata noArrayAlias bounded place rfl rfl
  have targetEq : cfg.validity.target = cfg.access.runtime := by
    obtain ⟨_, _, _, actual⟩ := configFields.validity
    dsimp only [cfg]
    rw [actual]
    rfl
  have width : cfg.access.runtime.base.pointerWidth = .w64 :=
    CanonicalConfigFacts.actual_target_width options () remaining span
  have visitorWidth : cfg.validity.target.base.pointerWidth = .w64 := by rw [targetEq, width]
  have target : cfg.validity.target.pointerSize = Size.ofBytes 8 := by
    rw [targetEq, configFields.accessRuntime]
    rfl
  apply CurrentReferenceVisitor.runtimeShallow cfg.validity () (fuel+1)
  · exact shallow
  · exact CurrentReferenceLocalValidity.reference_validate_of_retag cfg.validity cfg.access cfg.allocation compiler
      ReferenceMetadataFacts.prepared pointers () fuel fields reference pointee id parentTag childTag base offset len
      nonzero entry resolve arithmetic positive signedFits bounds dereference layout
      ProjectionMetadataFacts.slice_layout_shape.2.2 pointer width visitorWidth target ProjectionMetadataFacts.slice_layout_shape.2.1
      (by simpa only [pointeeTy] using CurrentReferenceMetadata.metadataTail options remaining span)
      (by simpa only [pointeeTy] using CurrentReferenceMetadata.inhabited options remaining span)
      (refName mutable) mutable frames frame machine localId valid hasValue cached sized pa pb ra rb pairOffset repr debug noDebug
      inactive configFields.retainTouched cachedAddress liveMemory afterFrame after sameLocals sameDestination activeAfter sizeAt retagged named classified

theorem validatePositive
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (fuel sizeFuel : Nat) (dynamicFuel : options.place.dynamicFuel = sizeFuel + 1)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (reference : LocalLayout) (mutable : Bool) (ty : reference.ty = refTy mutable)
    (sized : reference.layout.isSized = true)
    (pa pb : Primitive) (ra rb : WrappingRange) (pairOffset : Size)
    (repr : reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := pairOffset))
    (id : AllocId) (parentTag childTag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (liveMemory : machine.memory.live[id]? = some entry)
    (nonzero : base + offset ≠ 0)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (cached : frame.locals[localId].layout = some reference)
    (inactive : machine.user.payload.ghost = false)
    (activeAfter : after.user.payload.ghost = true)
    (shallow : machine.user.payload.validation = .Shallow)
    (comparator : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get
      (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (noArrayAlias : (EvalProjectionMachine.arrays.get
      (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let before := Storage.withCurrent frames frame machine
    let active := CurrentReferenceVisitor.ghost before true
    let parent := Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))
    let child := Pointer.new (.concrete id childTag) (Size.ofBytes (base + offset))
    let value := RetagReferencePlace.sliceValue cfg.access.runtime.base parent len reference
    let replacement := RetagReferencePlace.sliceValue cfg.access.runtime.base child len reference
    frame.locals[localId].value = .live (.immediate value.imm) →
    cfg.validity.retagPointer () value reference.ty active = .ok (some replacement) (Storage.withCurrent frames frame after) →
    ValidityMachine.validateRuntime cfg.validity () (fuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true before =
      .ok () (Storage.withCurrent frames (CurrentReferenceLocalWrite.written frame localId replacement.imm valid)
        {after with user := {after.user with payload := {after.user.payload with ghost := false}}}) := by
  intro cfg before active parent child value replacement hasValue retagged
  exact validatePositiveAcrossFrame options remaining span fuel sizeFuel dynamicFuel debugOff
    frames frame frame machine after localId valid reference mutable ty sized pa pb ra rb pairOffset repr
    id parentTag childTag base offset len entry cachedAddress liveMemory nonzero positive bounded bounds
    rfl rfl cached inactive activeAfter shallow comparator metadata noArrayAlias hasValue retagged

end DuplicatePrefix.CurrentReferenceCore

#print axioms DuplicatePrefix.CurrentReferenceCore.validatePositive
#print axioms DuplicatePrefix.CurrentReferenceCore.validatePositiveAcrossFrame

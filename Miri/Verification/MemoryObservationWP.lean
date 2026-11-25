import Miri.Verification.ScalarMemoryWP
import Miri.Verification.InitialWPAttr
import Miri.Verification.RvalueWP

/-! Exact scalar observations of physical memory after a store or byte copy. -/
namespace Miri.Verification.MemoryObservationWP

open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Std.WP

variable {P E K U : Type}

/-- A scalar read from its byte slice, initialization mask and provenance map.
The slice is inspected only after initialization succeeds. -/
def scalarFromImage [DecidableEq P] [PointerProvenance P]
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (bytes : Except AllocError (Array UInt8))
    (initialization : Except InitMaskError (Except AllocRange Unit))
    (provenance : ProvenanceMap P) : Except AllocError (Scalar P) := do
  match ← initialization.mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← bytes
  let bits ← (do
    if bytes.size > 16 then throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))
    let mut value := 0
    for index in [:bytes.size] do
      let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
      let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
      value := value + byte.toNat * 2 ^ (8 * valueIndex)
    return BitVec.ofNat 128 value
    : Except AllocError U128)
  let pointerSize := Size.fromBits layout.pointerWidth.bits
  if readProvenance then
    if range.size != pointerSize then
      throw (.scalarPointerNotTargetSized range.size pointerSize)
    let pointer ← match provenance.readPtr range.start pointerSize with
      | .ok pointer => pure pointer
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match pointer with
    | some tag =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Scalar.fromPointer layout (Pointer.new tag (Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none => (Scalar.fromUInt bits range.size).mapError AllocError.scalar
  else
    if PointerProvenance.offsetIsAddr (Prov := P) then
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar
    else
      let empty ← (provenance.rangeEmpty range pointerSize).mapError AllocError.provenance
      if empty then (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      else throw (.readPointerAsInt none)

/-- Scalar decoding depends only on the selected bytes and metadata. -/
@[miri_initial_wp] theorem readScalar_eq_image [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      scalarFromImage layout range readProvenance (allocation.getBytesUnchecked range)
        (allocation.initializationMask.isRangeInitialized range) allocation.provenanceMap := by
  rw [Allocation.Bridge.readScalar_eq]
  unfold scalarFromImage
  rfl

/-- A successful physical mutation supplies the image to the next scalar read.
A failed mutation hands its retained allocation to the mutation error branch. -/
def afterMutationPre [DecidableEq P] [PointerProvenance P]
    (mutation : EStateM.Result AllocError (Allocation P E) Unit)
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (post : Scalar P → Allocation P E → Prop)
    (onMutationError onReadError : AllocError → Allocation P E → Prop) : Prop :=
  match mutation with
  | .error error allocation => onMutationError error allocation
  | .ok () allocation =>
    match scalarFromImage layout range readProvenance (allocation.getBytesUnchecked range)
        (allocation.initializationMask.isRangeInitialized range) allocation.provenanceMap with
    | .ok value => post value allocation
    | .error error => onReadError error allocation

theorem afterMutationPre_eq [DecidableEq P] [PointerProvenance P]
    (mutation : EStateM.Result AllocError (Allocation P E) Unit)
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (post : Scalar P → Allocation P E → Prop)
    (onMutationError onReadError : AllocError → Allocation P E → Prop) :
    (match mutation with
    | .error error allocation => onMutationError error allocation
    | .ok () allocation =>
      match allocation.readScalar layout range readProvenance with
      | .ok value => post value allocation
      | .error error => onReadError error allocation) =
    afterMutationPre mutation layout range readProvenance post onMutationError onReadError := by
  cases mutation with
  | error => rfl
  | ok result allocation =>
    cases result
    simp only [afterMutationPre, readScalar_eq_image]

/-- Use the initial byte image and the exact splice when the next load
observes any in-bounds range, including a partially overwritten range. -/
theorem readScalar_of_fullImage [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (readProvenance : Bool) (finish : Size) (image : Array UInt8)
    (full : allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok image)
    (endpoint : range.endExclusive = .ok finish)
    (ordered : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (bound : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    allocation.readScalar layout range readProvenance =
      scalarFromImage layout range readProvenance
        (.ok (image.extract range.start.bytes.toNat finish.bytes.toNat))
        (allocation.initializationMask.isRangeInitialized range) allocation.provenanceMap := by
  rw [readScalar_eq_image, Allocation.Bridge.getBytesUnchecked_eq_extract allocation range finish image
    full endpoint ordered bound]

/-- An observing allocation ID aliases the newly committed allocation exactly
when the IDs agree. Other live entries retain their initial value. -/
@[miri_initial_wp] theorem lookup_after_commit [DecidableEq K]
    (memory : MemoryState P E K) (written observed : AllocId) (updated : Allocation P E)
    (entry : LocalAllocation P E K) (present : memory.live[written]? = some entry) :
    (memory.setLiveAllocation written updated).map (fun after => after.live[observed]?) =
      .ok (if observed = written then some {entry with allocation := updated}
        else memory.live[observed]?) := by
  rw [memory.setLiveAllocation_of_find written entry updated present]
  change Except.ok ((memory.live.insert written {entry with allocation := updated})[observed]?) = _
  rw [Std.ExtTreeMap.getElem?_insert]
  simp only [Std.compare_eq_iff_eq, eq_comm (a := written) (b := observed)]

local notation "State" => MachineHooks.State K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "Access" => MemoryOperandResult Provenance BorrowTree K (PlaceMachine.AccessState K U)
  (Option (AllocationAccessRef Provenance BorrowTree))

/-- Connect the physical observation to the typed read's actual access and
retained machine state. The read policy may change that state before decoding. -/
theorem scalarLoad_image_resultPre_iff [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (primitive : BackendPrimitive) (access : Access)
    (reference : AllocationAccessRef Provenance BorrowTree) (range : AllocRange)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO layout.size) = .ok range)
    (post : ImmediateValue Provenance → State → Prop) (onError : StepError → State → Prop) :
    MemoryWP.resultPre config before (scalarReadAfterAccess layout primitive config.runtime access)
        post onError ↔
      let after := {before with machine := (config.retainTouched
        {access.hooks.machine with memory := access.memory} access.touched)}
      match scalarFromImage config.runtime.base range (match primitive with | .Pointer _ => true | _ => false)
        (reference.allocation.getBytesUnchecked range) (reference.allocation.initializationMask.isRangeInitialized range)
        reference.allocation.provenanceMap with
      | .ok value => post ⟨.scalar value, layout⟩ after
      | .error error =>
        onError (access.hooks.pendingError.getD (config.memoryError (.allocation error))) after := by
  have load := readScalar_eq_image reference.allocation config.runtime.base range
    (match primitive with | .Pointer _ => true | _ => false)
  have exactRead := MemoryWP.scalarLoad_resultPre_iff config before layout primitive access
    reference range _ selected component load post onError
  split at exactRead <;>
    (rename_i result value loadEq resultEq imageEq
     simpa only [resultEq] using exactRead)

/-- Open the full physical copy before observing its destination. The source
snapshot is taken from the supplied initial source even when the ranges alias. -/
theorem copyThenReadPre_eq [DecidableEq P] [PointerProvenance P]
    (source dest : Allocation P E) (sourceRange : AllocRange) (destStart : Size)
    (repeatCount : UInt64) (pointerSize : Size) (sameAllocation nonoverlap : Bool)
    (layout : TargetDataLayout) (readRange : AllocRange) (readProvenance : Bool)
    (post : Scalar P → Allocation P E → Prop)
    (onCopyError onReadError : AllocError → Allocation P E → Prop) :
    afterMutationPre (source.copyRepeatedly sourceRange destStart repeatCount pointerSize
        sameAllocation nonoverlap dest)
      layout readRange readProvenance post onCopyError onReadError =
      Allocation.Bridge.copyRepeatedlyPre source sourceRange destStart repeatCount pointerSize
        sameAllocation nonoverlap
        (fun after => match scalarFromImage layout readRange readProvenance
            (after.getBytesUnchecked readRange) (after.initializationMask.isRangeInitialized readRange) after.provenanceMap with
          | .ok value => post value after
          | .error error => onReadError error after)
        onCopyError dest := by
  rw [← Allocation.Bridge.copyRepeatedlyPre_eq]
  cases source.copyRepeatedly sourceRange destStart repeatCount pointerSize sameAllocation nonoverlap dest with
  | ok result => cases result; rfl
  | error => rfl

/-- Pull a full-width load of the written range back to the serialized input
scalar and the provenance produced by clearing or inserting at the initial
allocation. The load can still fail, for example on a partial pointer. -/
theorem storeThenRead_image [DecidableEq P] [PointerProvenance P]
    (initial : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar P) (converted : ScalarBitsOrPointer P) (cleared final : ProvenanceMap P)
    (storage : initial.len = initial.byteSize.bytes.toNat)
    (mutable : initial.mutability = .Mut)
    (maskLength : initial.initializationMask.len = initial.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed initial.initializationMask)
    (nonzero : range.size.bytes ≠ 0) (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ initial.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (clear : ∀ image : Array UInt8,
      initial.getBytesUnchecked (allocRange Size.ZERO initial.byteSize) = .ok image →
      initial.provenanceMap.clear range image (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (insert : match converted with
      | .bits _ => final = cleared
      | .pointer pointer => range.size = Size.fromBits layout.pointerWidth.bits ∧
        cleared.insertPtr range.start pointer.provenance
          (Size.fromBits layout.pointerWidth.bits) = .ok () final)
    (readProvenance : Bool) (post : Scalar P → Allocation P E → Prop)
    (onWriteError onReadError : AllocError → Allocation P E → Prop) :
    let bits := match converted with
      | .bits bits => bits
      | .pointer pointer => BitVec.ofNat 128 pointer.offset.bytes.toNat
    ∃ updated, Allocation.writeScalar layout range value initial = .ok () updated ∧
      afterMutationPre (Allocation.writeScalar layout range value initial)
        layout range readProvenance post onWriteError onReadError =
      match scalarFromImage layout range readProvenance
        (.ok (MemoryWP.scalarBytes layout range.size bits.toNat))
        (.ok (.ok ())) final with
      | .ok scalar => post scalar updated
      | .error error => onReadError error updated := by
  obtain ⟨updated, write, _, _, _, _, _, _, _, _, _, initialized, provenance, intBytes, ptrBytes, _⟩ :=
    Allocation.writeScalar_spec layout initial range value converted cleared final storage mutable
      maskLength maskValid nonzero width bound conversion clear insert
  refine ⟨updated, write, ?_⟩
  have bytes : updated.getBytesUnchecked range = .ok (MemoryWP.scalarBytes layout range.size
      (match converted with
      | .bits bits => bits
      | .pointer pointer => BitVec.ofNat 128 pointer.offset.bytes.toNat).toNat) := by
    cases converted with
    | bits bits => exact intBytes bits rfl
    | pointer pointer => exact ptrBytes pointer rfl
  rw [write]
  simp only [afterMutationPre, initialized, provenance, bytes]

/-- For an observing range crossing a write boundary, extract from the
original image with the encoded write spliced into it. Initialization for
the observing range is queried on the actual updated mask. -/
theorem storeThenRead_splice [DecidableEq P] [PointerProvenance P]
    (initial : Allocation P E) (layout : TargetDataLayout)
    (written observed : AllocRange) (finish : Size) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (bits : U128) (nextMask : InitMask)
    (cleared final : ProvenanceMap P) (image oldBytes encoded : Array UInt8)
    (bitValue : bits = match converted with
      | .bits bits => bits
      | .pointer pointer => BitVec.ofNat 128 pointer.offset.bytes.toNat)
    (full : initial.getBytesUnchecked (allocRange Size.ZERO initial.byteSize) = .ok image)
    (mutable : initial.mutability = .Mut)
    (conversion : value.toBitsOrPtrInternal written.size = .ok converted)
    (slice : initial.getBytesUnchecked written = .ok oldBytes)
    (mark : initial.initializationMask.setRange written true = .ok nextMask)
    (clear : initial.provenanceMap.clear written image (Size.fromBits layout.pointerWidth.bits) =
      .ok () cleared)
    (serialize :
      (do
        if written.size.bytes > 16 then throw (.scalarBytesTooWide written.size)
        let count := written.size.bytes.toNat
        let mut result := #[]
        for index in [:count] do
          let valueIndex := if layout.endian == .little then index else count - index - 1
          result := result.push (UInt8.ofNat ((bits.toNat / 2 ^ (8 * valueIndex)) % 256))
        return result : Except AllocError (Array UInt8)) = .ok encoded)
    (length : (image.extract 0 written.start.bytes.toNat ++ encoded ++
        image.extract (written.start.bytes.toNat + written.size.bytes.toNat) image.size).size =
      initial.byteSize.bytes.toNat)
    (insert : match converted with
      | .bits _ => final = cleared
      | .pointer pointer => written.size = Size.fromBits layout.pointerWidth.bits ∧
        cleared.insertPtr written.start pointer.provenance
          (Size.fromBits layout.pointerWidth.bits) = .ok () final)
    (endpoint : observed.endExclusive = .ok finish)
    (ordered : observed.start.bytes.toNat ≤ finish.bytes.toNat)
    (bound : finish.bytes.toNat ≤ initial.byteSize.bytes.toNat)
    (readProvenance : Bool) (post : Scalar P → Allocation P E → Prop)
    (onWriteError onReadError : AllocError → Allocation P E → Prop) :
    let splice := image.extract 0 written.start.bytes.toNat ++ encoded ++
      image.extract (written.start.bytes.toNat + written.size.bytes.toNat) image.size
    ∃ updated, Allocation.writeScalar layout written value initial = .ok () updated ∧
      afterMutationPre (Allocation.writeScalar layout written value initial)
        layout observed readProvenance post onWriteError onReadError =
      match scalarFromImage layout observed readProvenance
        (.ok (splice.extract observed.start.bytes.toNat finish.bytes.toNat))
        (nextMask.isRangeInitialized observed) final with
      | .ok scalar => post scalar updated
      | .error error => onReadError error updated := by
  obtain ⟨updated, write, size, _, _, _, _, _, mask, provenance, spliced⟩ :=
    Allocation.Bridge.writeScalar_step_bridge layout initial written value converted bits nextMask
      cleared final image oldBytes encoded bitValue full mutable conversion slice mark clear
      serialize length insert
  have bytes := Allocation.Bridge.getBytesUnchecked_eq_extract updated observed finish _ spliced
    endpoint ordered (size.symm ▸ bound)
  exact ⟨updated, write, by simp only [write, afterMutationPre, bytes, mask, provenance]⟩

/-- An initialized one-copy load over the destination uses the source's
initial byte slice, even when source and destination are the same allocation.
Provenance comes from applying the source snapshot to the cleared destination. -/
theorem copyThenRead_image [DecidableEq P] [PointerProvenance P]
    (source dest : Allocation P E) (sourceRange : AllocRange)
    (sourceEnd destStart : Size) (sameAllocation nonoverlap : Bool)
    (layout : TargetDataLayout) (bytes : Array UInt8) (copied : ProvenanceCopy P)
    (cleared final : ProvenanceMap P)
    (sourceStorage : source.len = source.byteSize.bytes.toNat)
    (endpoint : sourceRange.endExclusive = .ok sourceEnd)
    (nonzero : sourceRange.size.bytes ≠ 0)
    (sourceMaskLength : source.initializationMask.len = source.byteSize)
    (sourceMaskValid : InitMask.WriteProof.WellFormed source.initializationMask)
    (initialized : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (sourceBytes : source.getBytesUnchecked sourceRange = .ok bytes)
    (sourceBounds : sourceEnd.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (prepare : ∀ image : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok image →
      source.provenanceMap.prepareCopy sourceRange image (Size.fromBits layout.pointerWidth.bits) =
        .ok copied)
    (disjoint : sameAllocation = true → nonoverlap = true →
      sourceEnd.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : dest.len = dest.byteSize.bytes.toNat)
    (destMutable : dest.mutability = .Mut)
    (destMaskLength : dest.initializationMask.len = dest.byteSize)
    (destMaskValid : InitMask.WriteProof.WellFormed dest.initializationMask)
    (destBounds : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ dest.byteSize.bytes.toNat)
    (clear : ∀ image : Array UInt8,
      dest.getBytesUnchecked (allocRange Size.ZERO dest.byteSize) = .ok image →
      dest.provenanceMap.clear (allocRange destStart sourceRange.size) image
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (applyCopy : cleared.applyCopy copied (allocRange destStart sourceRange.size) 1 = .ok () final)
    (readProvenance : Bool) (post : Scalar P → Allocation P E → Prop)
    (onCopyError onReadError : AllocError → Allocation P E → Prop) :
    let destRange := allocRange destStart sourceRange.size
    ∃ updated,
      Allocation.copy source sourceRange destStart (Size.fromBits layout.pointerWidth.bits)
        sameAllocation nonoverlap dest = .ok () updated ∧
      afterMutationPre (Allocation.copy source sourceRange destStart (Size.fromBits layout.pointerWidth.bits)
          sameAllocation nonoverlap dest)
        layout destRange readProvenance post onCopyError onReadError =
      match scalarFromImage layout destRange readProvenance (.ok bytes) (.ok (.ok ())) final with
      | .ok scalar => post scalar updated
      | .error error => onReadError error updated := by
  obtain ⟨updated, copy, _, _, _, _, _, _, _, _, destInit, _, _, provenance, destBytes, _⟩ :=
    Allocation.copy_initialized_spec source dest sourceRange sourceEnd destStart
      (Size.fromBits layout.pointerWidth.bits) sameAllocation nonoverlap bytes copied cleared final
      sourceStorage endpoint nonzero sourceMaskLength sourceMaskValid initialized sourceBytes sourceBounds
      prepare disjoint destStorage destMutable destMaskLength destMaskValid destBounds clear applyCopy
  exact ⟨updated, copy, by simp only [copy, afterMutationPre, destBytes, destInit, provenance]⟩

/-- In the typed machine, only a successful write starts the next load.
Both operations retain their independent access checks and error states. -/
theorem wp_storeThenLoad [DecidableEq K] (config : Config)
    (later : MemoryOperandLayout → Bool) (value : Scalar Provenance) (dest : MPlaceTy Provenance)
    (operand : OpTy Provenance) (before : State)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    wp (do
      PlaceMachine.writeMemory config later (.scalar value) dest
      PlaceMachine.readImmediate config operand) post onError before ↔
    MemoryWP.immediateWritePre config later (.scalar value) dest before
      (fun _ after => wp (PlaceMachine.readImmediate config operand) post onError after) onError := by
  rw [← RvalueWP.actionPre_eq_wp, RvalueWP.actionPre_bind]
  simp only [RvalueWP.actionPre_eq_wp]
  exact (MemoryWP.immediateWritePre_iff ..).symm

end Miri.Verification.MemoryObservationWP

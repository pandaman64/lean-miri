import Miri.Verification.MemoryObservationWP

namespace MiriTests.Verification.MemoryObservationWP

open Miri.ABI Miri.Memory Miri.Verification.MemoryObservationWP Std.WP

private def layout : TargetDataLayout := ⟨.little, .w64⟩
private def range (start width : UInt64) : AllocRange := allocRange (Size.ofBytes start) (Size.ofBytes width)

/- A partial overwrite is visible through a wider observing range. -/
#guard
    (do
      let initial ← Allocation.fromBytes (Prov := AllocId) #[0x34, 0xff] Align.ONE .Mut
      match Allocation.writeScalar layout (range 1 1) (Scalar.fromBool true) initial with
      | .error error _ => throw error
      | .ok () updated => updated.readScalar layout (range 0 2) false) =
    (Scalar.fromUInt (Prov := AllocId) 0x0134 (Size.ofBytes 2)).mapError AllocError.scalar

/- Overlapping ranges in one allocation read the original source snapshot. -/
#guard
    (do
      let initial ← Allocation.fromBytes (Prov := AllocId) #[0x12, 0x34, 0x56] Align.ONE .Mut
      match Allocation.copy initial (range 0 2) (Size.ofBytes 1) (Size.ofBytes 8) true false
          initial with
      | .error error _ => throw error
      | .ok () updated => updated.readScalar layout (range 1 2) false) =
    (Scalar.fromUInt (Prov := AllocId) 0x3412 (Size.ofBytes 2)).mapError AllocError.scalar

/- The copy succeeds but transfers an uninitialized byte. The next load
reports its initialization failure before inspecting pointer provenance. -/
#guard
    (do
      let source ← Allocation.tryNew (Prov := AllocId) (Size.ofBytes 1) Align.ONE .Uninit
        (fun _ _ => some #[0])
      let dest ← Allocation.fromBytes (Prov := AllocId) #[0xff] Align.ONE .Mut
      match Allocation.copy source (range 0 1) Size.ZERO (Size.ofBytes 8) false true dest with
      | .error error _ => throw error
      | .ok () updated => updated.readScalar layout (range 0 1) true) =
    .error (.invalidUninitBytes (some ⟨range 0 1, range 0 1⟩))

/- A pointer copied to a new range retains its allocation identity. -/
#guard
    let pointer : Pointer AllocId := Pointer.new ⟨3, by decide⟩ (Size.ofBytes 7)
    (do
      let initial ← Allocation.fromBytes (Prov := AllocId) (Array.replicate 16 0) Align.ONE .Mut
      match Allocation.writePointer layout (range 0 8) pointer initial with
      | .error error _ => throw error
      | .ok () source =>
        match Allocation.copy source (range 0 8) (Size.ofBytes 8) (Size.ofBytes 8) true true source with
        | .error error _ => throw error
        | .ok () updated => updated.readScalar layout (range 8 8) true) =
    .ok (Scalar.fromPointer layout pointer)

/- A disallowed overlap retains the original bytes after destination preparation. -/
#guard
    (do
      let initial ← Allocation.fromBytes (Prov := AllocId) #[0x12, 0x34, 0x56] Align.ONE .Mut
      match Allocation.copy initial (range 0 2) (Size.ofBytes 1) (Size.ofBytes 8) true true initial with
      | .error .copyRangesOverlap retained => retained.getBytesUnchecked (range 0 3)
      | .error error _ => throw error
      | .ok () _ => throw AllocError.readOnlyAllocation) =
    .ok #[0x12, 0x34, 0x56]

/-- A failed mutation never tries to decode its retained allocation. -/
example (retained : Allocation AllocId Unit) :
    afterMutationPre (.error .copyRangesOverlap retained) layout (range 1 2) false
      (fun _ _ => False) (fun error after => error = .copyRangesOverlap ∧ after = retained)
      (fun _ _ => False) := ⟨rfl, rfl⟩

/-- The exact scalar image rule sends the initialization error to the load's
error continuation, even when the pointer width and byte slice are invalid. -/
example (retained : Allocation AllocId Unit) (r bad : AllocRange)
    (uninit : retained.initializationMask.isRangeInitialized r = .ok (.error bad)) :
    afterMutationPre (.ok () retained) layout r true (fun _ _ => False) (fun _ _ => False)
      (fun error after => error = .invalidUninitBytes (some ⟨r, bad⟩) ∧ after = retained) := by
  simp only [afterMutationPre, scalarOutcomePre, scalarFromImage, uninit]
  constructor <;> first | rfl | trivial

/-- The live-map alias selects the written entry and preserves a distinct entry. -/
example (initial : MemoryState AllocId Unit Unit) (written other : AllocId)
    (entry : LocalAllocation AllocId Unit Unit) (updated : Allocation AllocId Unit)
    (present : initial.live[written]? = some entry) (distinct : other ≠ written) :
    (initial.setLiveAllocation written updated).map (fun after => after.live[written]?) =
        .ok (some {entry with allocation := updated}) ∧
    (initial.setLiveAllocation written updated).map (fun after => after.live[other]?) =
        .ok initial.live[other]? := by
  rw [lookup_after_commit initial written written updated entry present,
    lookup_after_commit initial written other updated entry present]
  simp [distinct]

/-- The public tactic reduces an ordinary store/load WP using facts about
the initial allocation and the scalar representation, before a store result
or a post-store allocation is available. -/
example (initial : Allocation AllocId Unit) (target : TargetDataLayout) (r : AllocRange)
    (value : Scalar AllocId) (converted : ScalarBitsOrPointer AllocId)
    (cleared final : ProvenanceMap AllocId)
    (storage : initial.len = initial.byteSize.bytes.toNat)
    (mutable : initial.mutability = .Mut)
    (maskLength : initial.initializationMask.len = initial.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed initial.initializationMask)
    (nonzero : r.size.bytes ≠ 0) (width : r.size.bytes.toNat ≤ 16)
    (bound : r.start.bytes.toNat + r.size.bytes.toNat ≤ initial.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal r.size = .ok converted)
    (clear : ∀ image : Array UInt8,
      initial.getBytesUnchecked (allocRange Size.ZERO initial.byteSize) = .ok image →
      initial.provenanceMap.clear r image (Size.fromBits target.pointerWidth.bits) = .ok () cleared)
    (insert : scalarProvenanceAfterWrite target r cleared final converted)
    (readProvenance : Bool) (post : Scalar AllocId → Prop) (failure : AllocError → Prop) :
    wp (do
      Allocation.writeScalar target r value
      loadScalar target r readProvenance)
      (fun scalar _ => post scalar) (fun error _ => failure error) initial ↔
    scalarOutcomePre (scalarFromImage target r readProvenance
      (.ok (Miri.Verification.MemoryWP.scalarBytes target r.size (storedScalarBits converted).toNat)) (.ok (.ok ())) final) post failure := by
  miri_observe_memory

/-- The copy/load WP observes the original source bytes and the result
of applying the source provenance image to the destination. -/
example (source dest : Allocation AllocId Unit) (target : TargetDataLayout)
    (srcRange : AllocRange) (srcEnd destStart : Size) (same nonoverlap : Bool)
    (bytes : Array UInt8) (copied : ProvenanceCopy AllocId) (cleared final : ProvenanceMap AllocId)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (endpoint : srcRange.endExclusive = .ok srcEnd)
    (nonzero : srcRange.size.bytes ≠ 0)
    (srcMaskLength : source.initializationMask.len = source.byteSize)
    (srcMaskValid : InitMask.WriteProof.WellFormed source.initializationMask)
    (initialized : source.initializationMask.isRangeInitialized srcRange = .ok (.ok ()))
    (srcBytes : source.getBytesUnchecked srcRange = .ok bytes)
    (srcBounds : srcEnd.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (prepare : ∀ image : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok image →
      source.provenanceMap.prepareCopy srcRange image (Size.fromBits target.pointerWidth.bits) =
        .ok copied)
    (disjoint : same = true → nonoverlap = true →
      srcEnd.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + srcRange.size.bytes.toNat ≤ srcRange.start.bytes.toNat)
    (destStorage : dest.len = dest.byteSize.bytes.toNat)
    (destMutable : dest.mutability = .Mut)
    (destMaskLength : dest.initializationMask.len = dest.byteSize)
    (destMaskValid : InitMask.WriteProof.WellFormed dest.initializationMask)
    (destBounds : destStart.bytes.toNat + srcRange.size.bytes.toNat ≤ dest.byteSize.bytes.toNat)
    (clear : ∀ image : Array UInt8,
      dest.getBytesUnchecked (allocRange Size.ZERO dest.byteSize) = .ok image →
      dest.provenanceMap.clear (allocRange destStart srcRange.size) image
        (Size.fromBits target.pointerWidth.bits) = .ok () cleared)
    (applyCopy : cleared.applyCopy copied (allocRange destStart srcRange.size) 1 = .ok () final)
    (readProvenance : Bool) (post : Scalar AllocId → Prop) (failure : AllocError → Prop) :
    wp (do
      Allocation.copy source srcRange destStart (Size.fromBits target.pointerWidth.bits) same nonoverlap
      loadScalar target (allocRange destStart srcRange.size) readProvenance)
      (fun scalar _ => post scalar) (fun error _ => failure error) dest ↔
    scalarOutcomePre (scalarFromImage target (allocRange destStart srcRange.size) readProvenance
      (.ok bytes) (.ok (.ok ())) final) post failure := by
  miri_observe_memory

/-- When a copy fails, the actual mutation error and its retained allocation
are available without inspecting a load or its success continuation. -/
example (source initial retained : Allocation AllocId Unit) (sourceRange readRange : AllocRange)
    (destStart : Size) (error : AllocError)
    (copy : Allocation.copyRepeatedly source sourceRange destStart 1 (Size.ofBytes 8) false true initial =
      .error error retained) :
    wp (do
      Allocation.copyRepeatedly source sourceRange destStart 1 (Size.ofBytes 8) false true
      loadScalar layout readRange false)
      (fun _ _ => False) (fun failed after => failed = error ∧ after = retained) initial := by
  miri_observe_memory

end MiriTests.Verification.MemoryObservationWP

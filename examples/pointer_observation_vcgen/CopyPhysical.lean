import Miri.Memory.Allocation
import Miri.Memory.ProvenanceMapVerification

namespace PointerObservation.Copy

open Miri.ABI Miri.Memory
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-- The fixture allocation before attaching its Tree Borrows state. -/
def unitImage (source destination : UInt8) : Allocation Provenance Unit :=
  (Allocation.fromBytes #[source, destination] Align.ONE .Mut).toOption.get (by cbv)

/-- Copy the first byte to the second byte of the same initialized allocation.
The ordered permission checks supply independently tracked source and
destination snapshots. The physical write retains the destination snapshot. -/
theorem physicalCopyPre (source destination : UInt8) {E : Type}
    (readTree writeTree : E) (post : Allocation Provenance E → Prop)
    (failure : AllocError → Allocation Provenance E → Prop) :
    Allocation.Bridge.copyRepeatedlyPre
      ((unitImage source destination).withExtra readTree)
      (allocRange Size.ZERO (Size.ofBytes 1)) (Size.ofBytes 1) 1 (Size.ofBytes 8)
      true true post failure ((unitImage source destination).withExtra writeTree) =
        post ((unitImage source source).withExtra writeTree) := by
  let src := (unitImage source destination).withExtra readTree
  let dst := (unitImage source destination).withExtra writeTree
  let srcRange := allocRange Size.ZERO (Size.ofBytes 1)
  let dstStart := Size.ofBytes 1
  let ptrSize := Size.ofBytes 8
  change Allocation.Bridge.copyRepeatedlyPre src srcRange dstStart 1 ptrSize true true post failure dst = _
  unfold Allocation.Bridge.copyRepeatedlyPre
  have srcBytes : src.getBytesUnchecked srcRange = .ok #[source] := by rfl
  have dstSize : srcRange.size.mul 1 = .ok (Size.ofBytes 1) := by cbv
  have dstBytes : dst.getBytesUnchecked (allocRange dstStart (Size.ofBytes 1)) = .ok #[destination] := by rfl
  simp only [srcBytes, dstSize, dstBytes]
  have provenance (image : Array UInt8) :
      src.provenanceMap.prepareCopy srcRange image ptrSize = .ok ⟨#[], #[]⟩ :=
    ProvenanceMap.prepareCopy_new srcRange image ptrSize (Size.ofBytes 1) (by decide) (by cbv)
  have snapshot : src.initializationMask.prepareCopy srcRange = .ok ⟨true, #[1]⟩ := by
    dsimp only [src, srcRange]
    cbv
  simp only [provenance, snapshot]
  simp only [Allocation.Bridge.prepareCopyOverwrite_eq, dstBytes]
  dsimp only [src, dst, srcRange, dstStart, ptrSize]
  cbv

#print axioms physicalCopyPre

end PointerObservation.Copy

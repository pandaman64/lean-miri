import Miri.Memory.AllocationVerification

/-! Byte-level refinements for a common scalar memory operand. -/
namespace Miri.Verification.MemoryWP

open Miri.ABI Miri.Memory

private theorem boolByteEncoding (layout : TargetDataLayout) (value : Bool) :
    Array.ofFn (fun i : Fin ((Size.ofBytes 1).bytes.toNat) =>
      UInt8.ofNat (((if value then (1 : U128) else 0).toNat / 2 ^ (8 *
        (if layout.endian == .little then i.1 else
          (Size.ofBytes 1).bytes.toNat - i.1 - 1))) % 256)) = #[if value then 1 else 0] := by
  cases value <;> cases layout.endian <;> decide

/-- A scalar load from an initialized Boolean byte produces the Boolean
immediate for either byte order. A non-address provenance mode requires
the same empty-overlap check as the interpreter. -/
theorem readBool_of_bytes {P E : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange) (value : Bool)
    (width : range.size = Size.ofBytes 1)
    (initialized : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (bytes : allocation.getBytesUnchecked range = .ok #[if value then 1 else 0])
    (provenance : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.readScalar layout range false = .ok (Scalar.fromBool value) := by
  rw [allocation.readScalar_int_of_bytes layout range _ initialized bytes (by simp) provenance, width]
  cases value <;> cases layout.endian <;> rfl

/-- The scalar write specification specialized to a Boolean byte. The
selected range becomes initialized and contains the serialized value.
Provenance is the actual result of clearing that range. -/
theorem writeBool_of_bytes {P E : Type} (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (value : Bool) (cleared : ProvenanceMap P)
    (width : range.size = Size.ofBytes 1)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared) :
    ∃ updated, Allocation.writeScalar layout range (Scalar.fromBool value) allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.extra = allocation.extra ∧ updated.provenanceMap = cleared ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.getBytesUnchecked range = .ok #[if value then 1 else 0] := by
  have conversion : (Scalar.fromBool value : Scalar P).toBitsOrPtrInternal range.size =
      .ok (.bits (if value then 1 else 0)) := by
    rw [width]
    cases value <;> rfl
  obtain ⟨updated, store, size, len, _, _, extra, _, _, _, _, initialized, provenance, bytes, _, _⟩ :=
    Allocation.writeScalar_spec layout allocation range (Scalar.fromBool value)
      (.bits (if value then 1 else 0)) cleared cleared storage mutable maskLength maskValid
      (by rw [width]; decide)
      (by rw [width]; decide)
      bound conversion clear rfl
  refine ⟨updated, store, size, len, extra, provenance, initialized, ?_⟩
  have encoded := bytes (if value then 1 else 0) rfl
  rw [width, boolByteEncoding] at encoded
  exact encoded

end Miri.Verification.MemoryWP

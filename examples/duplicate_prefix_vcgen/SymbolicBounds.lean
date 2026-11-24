import Miri.Interpreter.IntegerOps
import Miri.Memory.Access

namespace DuplicatePrefix.SymbolicBounds

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR

private def usize (value : UInt64) : IntegerValue :=
  ⟨ScalarInt.ofUInt64 value, ⟨Size.ofBytes 8, .usize⟩⟩

private theorem decodeUsize (value : UInt64) :
    IntegerOps.decode (usize value) = .ok (Int.ofNat value.toNat) := by
  have fits : value.toNat < 2 ^ 128 := by
    have := value.toNat_lt
    omega
  simp [IntegerOps.decode, usize, IntegerType.signed, IntegerKind.signed,
    ScalarInt.ofUInt64, ScalarInt.toUInt, ScalarInt.toBits]
  change Except.ok (Int.ofNat (value.toNat % 2 ^ 128)) = _
  rw [Nat.mod_eq_of_lt fits]
  rfl

/-- The current root's first comparison accepts exactly count zero. -/
theorem zeroCheck (count : UInt64) :
    IntegerOps.binary .Eq (usize count) (usize 0) = .ok (.boolean (count.toNat == 0)) := by
  unfold IntegerOps.binary
  rw [decodeUsize, decodeUsize]
  change Except.ok (IntegerResult.boolean (Int.ofNat count.toNat == 0)) = _
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

/-- The production unsigned comparison used in the second switch. -/
theorem greaterCheck (count halfLength : UInt64) :
    IntegerOps.binary .Gt (usize count) (usize halfLength) =
      .ok (.boolean (decide (halfLength.toNat < count.toNat))) := by
  unfold IntegerOps.binary
  rw [decodeUsize, decodeUsize]
  change Except.ok (IntegerResult.boolean (decide ((halfLength.toNat : Int) < (count.toNat : Int)))) = _
  simp

/-- The `usize` division in the exported second guard is exact and total. -/
theorem halfLength (length : UInt64) :
    IntegerOps.binary .Div (usize length) (usize 2) =
      .ok (.scalar (ScalarInt.ofUInt64 (length / 2))) := by
  unfold IntegerOps.binary
  rw [decodeUsize, decodeUsize]
  change (do
    let result := Int.tdiv (Int.ofNat length.toNat) 2
    let (value, lossy) ← (ScalarInt.truncateFromUInt
      (BitVec.ofInt 128 result) (Size.ofBytes 8))
      |>.mapError IntegerOpError.scalar
    if (result < 0 || result ≥ (2 ^ 128 : Int) || lossy) && false then
      throw (IntegerOpError.undefinedBehavior (.arithmeticOverflow .Div))
    pure (IntegerResult.scalar value)) = _

  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  change Except.ok (IntegerResult.scalar _) = Except.ok (IntegerResult.scalar _)
  congr 2
  unfold ScalarInt.ofUInt64

  have raw : BitVec.zeroExtend 128 (BitVec.extractLsb 63 0
      (BitVec.ofInt 128 ((Int.ofNat length.toNat).tdiv 2))) =
      BitVec.ofNat 128 (length / 2).toNat := by
    apply BitVec.eq_of_toNat_eq
    have exactHalf : (Int.ofNat length.toNat).tdiv 2 = Int.ofNat (length.toNat / 2) := rfl
    have limit : length.toNat / 2 < 2 ^ 64 := by
      have bound : length.toNat < 2 ^ 64 := length.toNat_lt_size
      omega
    have limit128 : length.toNat / 2 < 2 ^ 128 := by omega
    have sameBits : BitVec.ofInt 128 (Int.ofNat (length.toNat / 2)) =
        BitVec.ofNat 128 (length.toNat / 2) := rfl
    rw [exactHalf, sameBits]
    simp [UInt64.toNat_div, Nat.mod_eq_of_lt limit, Nat.mod_eq_of_lt limit128]
  have width : (((Size.ofBytes 8).bytes * 8).toNat - 1) = 63 := by decide
  rw [width, raw]

theorem copy_fits {length n : Nat} (guard : n ≤ length / 2) :
    n + n ≤ length := by omega

/-- Connect the 64-bit unsigned guard to the natural-number range lemma. -/
theorem usize_guard {length n : UInt64} (guard : ¬ n > length / 2) :
    n.toNat + n.toNat ≤ length.toNat := by
  have guardNat : n.toNat ≤ length.toNat / 2 := by
    simpa [UInt64.lt_iff_toNat_lt] using guard
  exact copy_fits guardNat

/-- Checked addition cannot wrap when the natural-number sum fits u64. -/
theorem size_add_ok (left right : Size)
    (fits : left.bytes.toNat + right.bytes.toNat < 2 ^ 64) :
    Size.add left right = .ok (Size.ofBytes (left.bytes + right.bytes)) := by
  have noWrap : ¬ left.bytes + right.bytes < left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    omega
  simp [Size.add, noWrap]

/-- The one-copy size multiplication performed by the memory-copy path
cannot overflow, even at the maximum representable byte count. -/
theorem size_mul_one (size : Size) : Size.mul size 1 = .ok size := by
  cases size
  simp [Size.mul, Size.ofBytes]

/-- Conversion to the signed access-size representation is also checked by
the real library operation. -/
theorem signed_size_ok (size : Size)
    (fits : size.bytes.toNat < 9223372036854775808) :
    sizeAsI64 size = .ok (Int.ofNat size.bytes.toNat) := by
  simp [sizeAsI64, fits]

/-- Compute the real checked source endpoint; this is the destination offset
required for the nonoverlapping copy. -/
theorem source_end (source : Size) (n : UInt64)
    (fits : source.bytes.toNat + n.toNat < 2 ^ 64) :
    (allocRange source (Size.ofBytes n)).endExclusive =
      .ok (Size.ofBytes (source.bytes + n)) := by
  unfold AllocRange.endExclusive AllocRange.end allocRange
  rw [size_add_ok source (Size.ofBytes n) fits]
  rfl

theorem copy_intervals {base length n capacity : Nat}
    (sliceFits : base + length ≤ capacity) (guard : n ≤ length / 2) :
    base + n ≤ capacity ∧ base + n + n ≤ capacity ∧
      (∀ index, base ≤ index → index < base + n →
        ¬ (base + n ≤ index ∧ index < base + n + n)) := by
  have := copy_fits guard
  refine ⟨by omega, by omega, ?_⟩
  intro index lower upper
  omega

/-- The archived intersection test and the current start-in-interval test
agree on nonempty checked ranges, as used by the positive copy branch. -/
theorem overlap_guard_migration (srcStart srcEnd dstStart dstEnd : UInt64)
    (srcPositive : srcStart < srcEnd) (dstPositive : dstStart < dstEnd) :
    ((srcStart < dstEnd) && (dstStart < srcEnd)) =
      ((srcStart ≤ dstStart && dstStart < srcEnd) ||
        (dstStart ≤ srcStart && srcStart < dstEnd)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
  omega

/-- The actual lean-miri bounds checker accepts any nonnegative in-bounds
interval whose size fits its signed host representation. -/
theorem checkedBounds_ok (target : PointerArithmetic) (id : AllocId)
    (capacity offset : Size) (count : Nat) (message : CheckInAllocMsg)
    (signedFits : count < 9223372036854775808)
    (inBounds : offset.bytes.toNat + count ≤ capacity.bytes.toNat) :
    checkedBounds target id capacity offset (Int.ofNat count) message = .ok () := by
  simp [checkedBounds]
  split
  · rename_i badSize
    change (decide (-(2 ^ 63 : Int) ≤ (count : Int)) &&
      decide ((count : Int) < (2 ^ 63 : Int))) = false at badSize
    simp at badSize
    omega
  · simp [Nat.not_lt.mpr inBounds]
    rfl

/-- Both real allocation-bounds checks for the copy, with the destination
offset supplied by the pointer-resolution layer. Provenance/permissions are
separate obligations. -/
theorem copy_bounds_ok (target : PointerArithmetic) (id : AllocId)
    (capacity source destination : Size) (length n : Nat)
    (sliceFits : source.bytes.toNat + length ≤ capacity.bytes.toNat)
    (guard : n ≤ length / 2)
    (signedFits : n < 9223372036854775808)
    (destinationOffset : destination.bytes.toNat = source.bytes.toNat + n) :
    checkedBounds target id capacity source (Int.ofNat n) .memoryAccess = .ok () ∧
    checkedBounds target id capacity destination (Int.ofNat n) .memoryAccess = .ok () := by
  have fits := copy_fits guard
  constructor
  · apply checkedBounds_ok <;> omega
  · apply checkedBounds_ok <;> omega

/-- Derive both bounds checks and the checked source endpoint directly from
the unsigned guard and a slice region. No destination-offset or count-size
conclusion is assumed. This remains a component theorem: resolving pointers
and establishing access permissions belong to the interpreter connection. -/
theorem guarded_copy_checks (target : PointerArithmetic) (id : AllocId)
    (capacity source : Size) (length n : UInt64)
    (sliceFits : source.bytes.toNat + length.toNat ≤ capacity.bytes.toNat)
    (guard : ¬ n > length / 2) :
    let destination := Size.ofBytes (source.bytes + n)
    checkedBounds target id capacity source (Int.ofNat n.toNat) .memoryAccess = .ok () ∧
    checkedBounds target id capacity destination (Int.ofNat n.toNat) .memoryAccess = .ok () ∧
    (allocRange source (Size.ofBytes n)).endExclusive = .ok destination := by
  dsimp only
  have countFits := usize_guard guard
  have capacityFits : capacity.bytes.toNat < 18446744073709551616 :=
    capacity.bytes.toNat_lt_size
  have sumFits : source.bytes.toNat + n.toNat < 2 ^ 64 := by omega
  have destinationOffset : (Size.ofBytes (source.bytes + n)).bytes.toNat =
      source.bytes.toNat + n.toNat := by
    simp [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt sumFits]
  refine ⟨?_, ?_, source_end source n sumFits⟩
  · apply checkedBounds_ok <;> omega
  · apply checkedBounds_ok <;> omega

/-- The byte-layout specialization of the intrinsic's actual size check
on the 64-bit target used for the exported root. -/
theorem copyIntrinsicSize (length count : UInt64) (accepted : ¬ count > length / 2) :
    IntegerOps.computeSizeInBytes (Size.ofBytes 1) count (Size.ofBytes 9223372036854775807) =
      some (Size.ofBytes count) := by
  have fits := usize_guard accepted
  have lenRange : length.toNat < 2 ^ 64 := length.toNat_lt_size
  have max : count.toNat ≤ 9223372036854775807 := by omega
  have range : count.toNat < 2 ^ 64 := count.toNat_lt_size
  simp [IntegerOps.computeSizeInBytes, Size.ofBytes, range, max]

/-- The admitted signed count fits in both in-bounds copy intervals and
the destination starts at the checked exclusive source end. -/
theorem positive_copy_geometry (target : PointerArithmetic) (id : AllocId)
    (capacity source : Size) (length count : UInt64)
    (positive : 0 < count.toNat)
    (sliceFits : source.bytes.toNat + length.toNat ≤ capacity.bytes.toNat)
    (accepted : ¬ count > length / 2) :
    let size := Size.ofBytes count
    let destination := Size.ofBytes (source.bytes + count)
    sizeAsI64 size = .ok (Int.ofNat count.toNat) ∧
    Size.mul size 1 = .ok size ∧
    checkedBounds target id capacity source (Int.ofNat count.toNat) .inboundsPointerArithmetic = .ok () ∧
    checkedBounds target id capacity source (Int.ofNat count.toNat) .memoryAccess = .ok () ∧
    checkedBounds target id capacity destination (Int.ofNat count.toNat) .memoryAccess = .ok () ∧
    ∃ sourceEnd destinationEnd,
      (allocRange source size).endExclusive = .ok sourceEnd ∧
      (allocRange destination size).endExclusive = .ok destinationEnd ∧
      ((source.bytes ≤ destination.bytes && destination.bytes < sourceEnd.bytes) ||
        (destination.bytes ≤ source.bytes && source.bytes < destinationEnd.bytes)) = false := by
  dsimp only
  have fits := usize_guard accepted
  have lenRange : length.toNat < 2 ^ 64 := length.toNat_lt_size
  have capRange : capacity.bytes.toNat < 2 ^ 64 := capacity.bytes.toNat_lt_size
  have signed : count.toNat < 9223372036854775808 := by omega
  have sourceSumFits : source.bytes.toNat + count.toNat < 2 ^ 64 := by omega
  have shifted : (Size.ofBytes (source.bytes + count)).bytes.toNat = source.bytes.toNat + count.toNat := by
    simp [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt sourceSumFits]
  have destSumFits : (Size.ofBytes (source.bytes + count)).bytes.toNat + count.toNat < 2 ^ 64 := by
    rw [shifted]
    omega
  obtain ⟨readBounds, writeBounds, sourceEndpoint⟩ :=
    guarded_copy_checks target id capacity source length count sliceFits accepted
  refine ⟨signed_size_ok _ signed, size_mul_one _, ?_, readBounds, writeBounds,
    _, _, sourceEndpoint, source_end _ _ destSumFits, ?_⟩
  · apply checkedBounds_ok <;> omega
  · have after : source.bytes < (Size.ofBytes (source.bytes + count)).bytes := by
      rw [UInt64.lt_iff_toNat_lt, shifted]
      omega
    simp [UInt64.not_le.mpr after]

end DuplicatePrefix.SymbolicBounds

#print axioms DuplicatePrefix.SymbolicBounds.zeroCheck
#print axioms DuplicatePrefix.SymbolicBounds.halfLength
#print axioms DuplicatePrefix.SymbolicBounds.greaterCheck
#print axioms DuplicatePrefix.SymbolicBounds.copyIntrinsicSize
#print axioms DuplicatePrefix.SymbolicBounds.overlap_guard_migration
#print axioms DuplicatePrefix.SymbolicBounds.positive_copy_geometry

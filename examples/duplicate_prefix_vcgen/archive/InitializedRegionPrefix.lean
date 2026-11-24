import PreparedArguments
import duplicate_prefix.InitMaskReadComplete

namespace DuplicatePrefix.InitializedRegionPrefix
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open PreparedArguments

/-- Recover the copy source's bitwise initialization from the admitted
operational whole-slice check. Bytes beyond the admitted slice may be
arbitrary, and the mask may be lazy or materialized. -/
theorem initialized {K U : Type} {state : MachineHooks.State K U}
    (length count : UInt64) (storage : InitializedRegion state length)
    (nonempty : length ≠ 0) (countBound : count.toNat ≤ length.toNat)
    (maskLen : storage.entry.allocation.initializationMask.len = storage.entry.allocation.byteSize)
    (room : storage.entry.allocation.len + 64 < 18446744073709551616) :
    InitMaskCopy.InitializedOn storage.entry.allocation.initializationMask storage.relativeStart
      (Size.ofBytes (storage.relativeStart.bytes+count)) := by
  let start := storage.relativeStart
  let finish := Size.ofBytes (start.bytes+length)
  let prefixStop := Size.ofBytes (start.bytes+count)
  have bounds : start.bytes.toNat + length.toNat ≤ storage.entry.allocation.byteSize.bytes.toNat := storage.fits
  have capacity := storage.entry.allocation.byteSize.bytes.toNat_lt
  have fit : start.bytes.toNat + length.toNat < 2^64 := by omega
  have prefixFit : start.bytes.toNat + count.toNat < 2^64 := by omega
  have finishNat : finish.bytes.toNat = start.bytes.toNat + length.toNat := by
    change (start.bytes+length).toNat = _
    simp only [UInt64.toNat_add, Nat.mod_eq_of_lt fit]
  have prefixNat : prefixStop.bytes.toNat = start.bytes.toNat + count.toNat := by
    change (start.bytes+count).toNat = _
    simp only [UInt64.toNat_add, Nat.mod_eq_of_lt prefixFit]
  have noWrap : ¬ start.bytes + length < start.bytes := by
    rw [UInt64.lt_iff_toNat_lt]
    change ¬ finish.bytes.toNat < start.bytes.toNat
    rw [finishNat]
    omega
  have endpoint :
      (allocRange start (Size.ofBytes length)).endExclusive = .ok finish := by
    simp [finish, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add, Size.ofBytes, noWrap, Except.mapError]
  have within : finish.bytes.toNat ≤ storage.entry.allocation.initializationMask.len.bytes.toNat := by
    rw [maskLen,finishNat]
    exact bounds
  have size : finish.bytes.toNat + 64 < 18446744073709551616 := by
    rw [storage.backed] at room
    omega
  apply InitMaskReadComplete.initialized_prefix _ start finish prefixStop (by omega)
  exact InitMaskReadComplete.of_is_range_initialized _ _ finish endpoint within size (storage.initialized nonempty)

#print axioms initialized
end DuplicatePrefix.InitializedRegionPrefix

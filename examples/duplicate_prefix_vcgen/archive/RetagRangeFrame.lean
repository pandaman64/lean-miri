import Miri.Verification.RangeModifyLaw
import duplicate_prefix.GeneralRangeMapOriginPrepare
import duplicate_prefix.GeneralRangeMapState

namespace DuplicatePrefix.RetagRangeFrame

open Miri.ABI Miri.DataStructures Miri.Verification.RangeModifyLaw
open DuplicatePrefix.GeneralRangeMapOrigins

theorem partition_eq {A : Type} {left right : DedupRangeMap A}
    (same : left.entries.map (·.range) = right.entries.map (·.range)) :
    left.WellFormed ↔ right.WellFormed := by
  have size : left.entries.size = right.entries.size := by
    simpa using congrArg Array.size same
  have rangeAt (position : Nat) (leftValid : position < left.entries.size)
      (rightValid : position < right.entries.size) :
      left.entries[position].range = right.entries[position].range := by
    have eq := congrArg (fun (rows : Array ByteRange) => rows[position]?) same
    have leftBound : position < (left.entries.map (·.range)).size := by simpa using leftValid
    have rightBound : position < (right.entries.map (·.range)).size := by simpa using rightValid
    simp only [Array.getElem?_eq_getElem leftBound, Array.getElem?_eq_getElem rightBound,
      Array.getElem_map, Option.some.injEq] at eq
    exact eq
  apply Iff.intro
  · intro well
    unfold DedupRangeMap.WellFormed at well ⊢
    by_cases empty : right.entries.size = 0
    · simp [empty]
    · have notEmpty : left.entries.size ≠ 0 := by rwa [size]
      simp only [empty, notEmpty, ↓reduceDIte] at well ⊢
      refine ⟨(rangeAt 0 (by omega) (by omega)).symm ▸ well.1, ?_, ?_⟩
      · intro position valid
        rw [← rangeAt position (by omega) valid]
        apply well.2.1
      · intro position valid
        rw [← rangeAt position (by omega) (by omega), ← rangeAt (position + 1) (by omega) valid]
        apply well.2.2
  · intro well
    unfold DedupRangeMap.WellFormed at well ⊢
    by_cases empty : left.entries.size = 0
    · simp [empty]
    · have notEmpty : right.entries.size ≠ 0 := by rwa [← size]
      simp only [empty, notEmpty, ↓reduceDIte] at well ⊢
      refine ⟨(rangeAt 0 (by omega) (by omega)) ▸ well.1, ?_, ?_⟩
      · intro position valid
        rw [rangeAt position valid (by omega)]
        apply well.2.1
      · intro position valid
        rw [rangeAt position (by omega) (by omega), rangeAt (position + 1) valid (by omega)]
        apply well.2.2

/-- A successful actual split/merge/update preserves byte-local rights
through a pure update under independently supplied allocation bounds. -/
theorem modify_of_bounded {A : Type} [DecidableEq A] (map : DedupRangeMap A)
    (offset length : Size) (modify : ByteRange → A → A) (holds : UInt64 → A → Prop)
    (well : map.WellFormed) (bounds : offset.bytes.toNat + length.bytes.toNat ≤ map.size.bytes.toNat)
    (ready : EachByte map holds)
    (preserve : ∀ range point value, range.start ≤ point → point < range.stop →
      holds point value → holds point (modify range value)) :
    let result := map.modifyRange offset length modify
    result.outcome = .ok () ∧ result.state.WellFormed ∧ result.state.size = map.size ∧
      EachByte result.state holds := by
  let prepared := map.iterMut offset length
  obtain ⟨good, origins, _⟩ := GeneralRangeMapOriginPrepare.iter_mut map offset length well bounds
  have positions : ∀ position ∈ prepared.positions.toList, position < prepared.state.entries.size := by
    intro position member
    obtain ⟨cursor, bounded, equal⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr member)
    exact equal ▸ (good.selected cursor bounded).choose
  have transferred : EachByte prepared.state holds := by
    intro point index valid start stop
    obtain ⟨origin, bounded, lo, hi, equal⟩ := origins point prepared.state.entries[index].data
      ⟨index, valid, UInt64.le_iff_toNat_le.mp start, UInt64.lt_iff_toNat_lt.mp stop, rfl⟩
    exact equal ▸ ready point origin bounded (UInt64.le_iff_toNat_le.mpr lo) (UInt64.lt_iff_toNat_lt.mpr hi)
  let result := map.modifyRange offset length modify
  have changed := modifier_preserves map offset length modify holds prepared rfl good.outcome positions
    transferred preserve
  have shape : result.state.entries.map (·.range) = prepared.state.entries.map (·.range) := changed.2.2
  have size : result.state.size = prepared.state.size := by
    rw [GeneralRangeMapState.size_from_ranges result.state, shape, ← GeneralRangeMapState.size_from_ranges]
  exact ⟨changed.1, (partition_eq shape).mpr good.wellFormed, size.trans (congrArg Size.ofBytes good.capacity), changed.2.1⟩

end DuplicatePrefix.RetagRangeFrame

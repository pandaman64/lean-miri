import Miri.Memory.ProvenanceMap

/-! Empty-map and empty-copy specification lemmas for `Miri.Memory.ProvenanceMap`,
kept in a companion verification module off the interpreter critical path. -/

namespace Miri.Memory.ProvenanceMap

open Miri.ABI

set_option autoImplicit false

variable {P : Type}

/-- Reading a pointer from an empty provenance map returns `.ok none` whenever
the pointer-sized range does not overflow and the pointer size is nonzero. -/
theorem readPtr_new [DecidableEq P] [PointerProvenance P]
    (offset pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0)
    (endEq : (allocRange offset pointerSize).endExclusive = .ok finish) :
    (new (Prov := P)).readPtr offset pointerSize = .ok none := by
  have h_get : (new (Prov := P)).getPtr offset = none := rfl
  have h_rp := rangePtrs_new (P := P) (allocRange offset pointerSize) pointerSize finish positive endEq
  have h_rb := rangeBytes_new (P := P) (allocRange offset pointerSize) finish endEq
  unfold readPtr
  rw [h_get]
  dsimp only
  rw [h_rp, h_rb]
  rfl

/-- Preparing a provenance copy from an empty provenance map over any
non-overflowing range yields an empty `ProvenanceCopy`. -/
theorem prepareCopy_new (range : AllocRange) (data : Array UInt8) (pointerSize finish : Size)
    (positive : pointerSize.bytes ≠ 0)
    (endEq : range.endExclusive = .ok finish) :
    (new (Prov := P)).prepareCopy range data pointerSize = .ok ⟨#[], #[]⟩ := by
  have h_zero_end : ∀ s : Size, (allocRange s Size.ZERO).endExclusive = .ok s := by
    intro ⟨b⟩
    simp only [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes,
      Size.add, UInt64.add_zero, UInt64.lt_irrefl, ↓reduceIte, Except.mapError]
  have h_start0 := rangePtrs_new (P := P) (allocRange range.start Size.ZERO) pointerSize range.start
    positive (h_zero_end range.start)
  have h_fin0 := rangePtrs_new (P := P) (allocRange finish Size.ZERO) pointerSize finish
    positive (h_zero_end finish)
  refine prepareCopy_new_of_sub_ok range data pointerSize finish positive endEq h_start0 h_fin0 ?_
  intro h_ge
  apply UInt64.not_lt.mpr
  have h_end_def : Size.add range.start range.size = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end at endEq
    cases h_add : Size.add range.start range.size with
    | error _ => simp only [h_add, Except.mapError] at endEq; cases endEq
    | ok v => simp only [h_add, Except.mapError, Except.ok.injEq] at endEq; subst endEq; rfl
  unfold Size.add at h_end_def
  by_cases h_wrap : range.start.bytes + range.size.bytes < range.start.bytes
  · rw [ite_eq_left h_wrap] at h_end_def; cases h_end_def
  · rw [ite_eq_right h_wrap] at h_end_def
    injection h_end_def with h_fin_eq
    subst h_fin_eq
    have h_ge_nat : pointerSize.bytes.toNat ≤ range.size.bytes.toNat :=
      UInt64.le_iff_toNat_le.mp h_ge
    have h_nw : ¬((range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat) := by
      simpa only [UInt64.lt_iff_toNat_lt] using h_wrap
    have h1 := range.start.bytes.toNat_lt
    have h2 := range.size.bytes.toNat_lt
    have h_fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
      by_cases h_lt : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64
      · exact h_lt
      · have h_mod : (range.start.bytes + range.size.bytes).toNat =
            range.start.bytes.toNat + range.size.bytes.toNat - 2 ^ 64 := by
          rw [UInt64.toNat_add]; omega
        omega
    have h_p1 : (1 : UInt64).toNat ≤ pointerSize.bytes.toNat :=
      Nat.pos_of_ne_zero (fun h0 => positive (UInt64.toNat_inj.mp h0))
    have h_sub : (pointerSize.bytes - 1).toNat = pointerSize.bytes.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h_p1)]
      rfl
    rw [UInt64.le_iff_toNat_le, h_sub]
    change pointerSize.bytes.toNat - 1 ≤ (range.start.bytes + range.size.bytes).toNat
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
    omega

/-- Applying an empty `ProvenanceCopy` succeeds without modifying the target
provenance map. -/
theorem applyCopy_empty (range : AllocRange) (repeatCount : UInt64) (pm : ProvenanceMap P) :
    applyCopy ⟨#[], #[]⟩ range repeatCount pm = .ok () pm :=
  rfl

end Miri.Memory.ProvenanceMap

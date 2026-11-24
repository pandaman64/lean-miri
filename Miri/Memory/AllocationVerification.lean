import Miri.Memory.Allocation
import Miri.Memory.InitMaskVerification
import Miri.Memory.ProvenanceMapVerification

/-! Extra-metadata commutation, construction, raw-slice, checked-read,
partial-range write, disjoint-frame, and initialized-copy specifications for
`Miri.Memory.Allocation`, kept in a companion verification module off the
interpreter critical path. -/

namespace Miri.Memory.Allocation

open Miri.ABI
open Miri.Memory
open Miri.Memory.Allocation.Bridge

set_option autoImplicit false

variable {P E E' : Type}

private def targetUIntBytesPub (layout : TargetDataLayout) (size : Size) (bits : U128) :
    Except AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

private def readUIntPub (layout : TargetDataLayout) (bytes : Array UInt8) :
    Except AllocError U128 := do
  if bytes.size > 16 then throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private theorem add_size_no_wrap (left right : Size)
    (fits : left.bytes.toNat + right.bytes.toNat < 2 ^ 64) :
    Size.add left right = .ok (Size.ofBytes (left.bytes + right.bytes)) := by
  have h_not_lt : ¬(left.bytes + right.bytes < left.bytes) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    exact Nat.not_lt.mpr (Nat.le_add_right _ _)
  unfold Size.add
  rw [ite_eq_right h_not_lt]

private theorem endExclusive_fits (range : AllocRange) (finish : Size)
    (h_end : range.endExclusive = .ok finish) :
    range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 ∧
      finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
  unfold AllocRange.endExclusive AllocRange.end Size.add at h_end
  by_cases hw : range.start.bytes + range.size.bytes < range.start.bytes
  · simp only [hw, ↓reduceIte, Except.mapError] at h_end; cases h_end
  · simp only [hw, ↓reduceIte, Except.mapError, Except.ok.injEq] at h_end
    subst h_end
    have hnw : ¬((range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat) := by
      simpa only [UInt64.lt_iff_toNat_lt] using hw
    have h1 := range.start.bytes.toNat_lt
    have h2 := range.size.bytes.toNat_lt
    have h_fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
      by_cases hlt : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64
      · exact hlt
      · rw [UInt64.toNat_add] at hnw; omega
    exact ⟨h_fits, by simp only [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]⟩

private theorem extract_size_of_le (arr : Array UInt8) (a b : Nat) (hb : b ≤ arr.size) :
    (arr.extract a b).size = b - a := by
  rw [Array.size_extract, Nat.min_eq_left hb]

private theorem extract_subrange (arr : Array UInt8) (oStart oFin iStart iFin : Nat)
    (h_lo : oStart ≤ iStart) (h_mid : iStart ≤ iFin) (h_hi : iFin ≤ oFin) (h_raw : oFin ≤ arr.size) :
    arr.extract iStart iFin = (arr.extract oStart oFin).extract (iStart - oStart) (iFin - oStart) := by
  have h_oSz : (arr.extract oStart oFin).size = oFin - oStart := extract_size_of_le arr oStart oFin h_raw
  apply Array.ext
  · rw [extract_size_of_le arr iStart iFin (Nat.le_trans h_hi h_raw),
      Array.size_extract, h_oSz, Nat.min_eq_left (by omega)]
    omega
  · intro i _ _
    rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_extract]
    have h_idx : iStart + i = oStart + (iStart - oStart + i) := by omega
    simp only [h_idx]

private theorem extract_split (arr : Array UInt8) (s mid fin : Nat)
    (h1 : s ≤ mid) (h2 : mid ≤ fin) (h_raw : fin ≤ arr.size) :
    arr.extract s fin = arr.extract s mid ++ arr.extract mid fin := by
  have h_sz1 : (arr.extract s mid).size = mid - s := extract_size_of_le arr s mid (Nat.le_trans h2 h_raw)
  have h_sz2 : (arr.extract mid fin).size = fin - mid := extract_size_of_le arr mid fin h_raw
  apply Array.ext
  · rw [extract_size_of_le arr s fin h_raw, Array.size_append, h_sz1, h_sz2]; omega
  · intro i hi1 _
    by_cases h_left : i < mid - s
    · rw [Array.getElem_append_left (by rw [h_sz1]; exact h_left),
        Array.getElem_extract, Array.getElem_extract]
    · rw [Array.getElem_append_right (by rw [h_sz1]; exact Nat.le_of_not_lt h_left),
        Array.getElem_extract, Array.getElem_extract]
      have h_idx : s + i = mid + (i - (arr.extract s mid).size) := by rw [h_sz1]; omega
      simp only [h_idx]

private theorem extract_byteAt (arr : Array UInt8) (start finish idx : Nat)
    (h_fin : finish ≤ arr.size) (h_lo : start ≤ idx) (h_hi : idx < finish) :
    (arr.extract start finish)[idx - start]? = arr[idx]? := by
  have h_idx_lt : idx < arr.size := Nat.lt_of_lt_of_le h_hi h_fin
  have h_sub_lt : idx - start < (arr.extract start finish).size := by
    rw [extract_size_of_le arr start finish h_fin]; omega
  rw [Array.getElem?_eq_getElem h_sub_lt, Array.getElem?_eq_getElem h_idx_lt, Array.getElem_extract]
  have h_add_sub : start + (idx - start) = idx := Nat.add_sub_of_le h_lo
  simp only [h_add_sub]

private theorem splice_size (raw data : Array UInt8) (start finish : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size) (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size).size = raw.size := by
  rw [Array.size_append, Array.size_append,
    extract_size_of_le raw 0 start (Nat.le_trans h_lo h_fin),
    extract_size_of_le raw finish raw.size (Nat.le_refl _),
    Nat.sub_zero, h_data_sz]
  omega

private theorem splice_getElem? (raw data : Array UInt8) (start finish k : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size)[k]? =
      if start ≤ k ∧ k < finish then data[k - start]? else raw[k]? := by
  let pfx := raw.extract 0 start
  let sfx := raw.extract finish raw.size
  have h_pfx_sz : pfx.size = start := by
    dsimp only [pfx]; rw [extract_size_of_le raw 0 start (Nat.le_trans h_lo h_fin), Nat.sub_zero]
  have h_sfx_sz : sfx.size = raw.size - finish := extract_size_of_le raw finish raw.size (Nat.le_refl _)
  have h_pd_sz : (pfx ++ data).size = finish := by rw [Array.size_append, h_pfx_sz, h_data_sz]; omega
  by_cases h_lt_start : k < start
  · rw [ite_eq_right (fun h => Nat.not_lt.mpr h.1 h_lt_start)]
    rw [Array.getElem?_append_left (by rw [h_pd_sz]; exact Nat.lt_of_lt_of_le h_lt_start h_lo),
      Array.getElem?_append_left (by rw [h_pfx_sz]; exact h_lt_start)]
    simpa only [pfx, Nat.sub_zero] using extract_byteAt raw 0 start k (Nat.le_trans h_lo h_fin) (Nat.zero_le _) h_lt_start
  · by_cases h_lt_fin : k < finish
    · rw [ite_eq_left ⟨Nat.le_of_not_lt h_lt_start, h_lt_fin⟩]
      rw [Array.getElem?_append_left (by rw [h_pd_sz]; exact h_lt_fin),
        Array.getElem?_append_right (by rw [h_pfx_sz]; exact Nat.le_of_not_lt h_lt_start), h_pfx_sz]
    · rw [ite_eq_right (fun h => h_lt_fin h.2)]
      rw [Array.getElem?_append_right (by rw [h_pd_sz]; exact Nat.le_of_not_lt h_lt_fin), h_pd_sz]
      by_cases h_lt_raw : k < raw.size
      · exact extract_byteAt raw finish raw.size k (Nat.le_refl _) (Nat.le_of_not_lt h_lt_fin) h_lt_raw
      · rw [Array.getElem?_eq_none (by rw [h_sfx_sz]; omega), Array.getElem?_eq_none (Nat.le_of_not_lt h_lt_raw)]

private theorem splice_extract_exact (raw data : Array UInt8) (start finish : Nat)
    (h_lo : start ≤ finish) (h_fin : finish ≤ raw.size)
    (h_data_sz : data.size = finish - start) :
    (raw.extract 0 start ++ data ++ raw.extract finish raw.size).extract start finish = data := by
  let spliced := raw.extract 0 start ++ data ++ raw.extract finish raw.size
  have h_sp_sz : spliced.size = raw.size := splice_size raw data start finish h_lo h_fin h_data_sz
  apply Array.ext
  · rw [extract_size_of_le spliced start finish (h_sp_sz.symm ▸ h_fin), h_data_sz]
  · intro i hi1 hi2
    have hi_lt : i < finish - start := h_data_sz ▸ hi2
    have h_eq? := extract_byteAt spliced start finish (start + i) (h_sp_sz.symm ▸ h_fin)
      (Nat.le_add_right _ _) (by omega)
    rw [Nat.add_sub_cancel_left] at h_eq?
    have h_sp_i := splice_getElem? raw data start finish (start + i) h_lo h_fin h_data_sz
    rw [ite_eq_left ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left] at h_sp_i
    exact Option.some.inj ((Array.getElem?_eq_getElem hi1).symm.trans ((h_eq?.trans h_sp_i).trans (Array.getElem?_eq_getElem hi2)))

private theorem splice_extract_disjoint (raw data : Array UInt8) (wStart wFin qStart qFin : Nat)
    (h_w_lo : wStart ≤ wFin) (h_w_fin : wFin ≤ raw.size)
    (h_q_lo : qStart ≤ qFin) (h_q_fin : qFin ≤ raw.size)
    (h_data_sz : data.size = wFin - wStart)
    (h_disj : wFin ≤ qStart ∨ qFin ≤ wStart) :
    (raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size).extract qStart qFin =
      raw.extract qStart qFin := by
  let spliced := raw.extract 0 wStart ++ data ++ raw.extract wFin raw.size
  have h_sp_sz : spliced.size = raw.size := splice_size raw data wStart wFin h_w_lo h_w_fin h_data_sz
  apply Array.ext
  · rw [Array.size_extract, h_sp_sz, Array.size_extract]
  · intro i hi1 hi2
    have hi_lt : i < qFin - qStart := by
      rw [extract_size_of_le raw qStart qFin h_q_fin] at hi2; exact hi2
    have h_eq1 := extract_byteAt spliced qStart qFin (qStart + i) (h_sp_sz.symm ▸ h_q_fin)
      (Nat.le_add_right _ _) (by omega)
    have h_eq2 := extract_byteAt raw qStart qFin (qStart + i) h_q_fin (Nat.le_add_right _ _) (by omega)
    rw [Nat.add_sub_cancel_left] at h_eq1 h_eq2
    have h_sp_i := splice_getElem? raw data wStart wFin (qStart + i) h_w_lo h_w_fin h_data_sz
    have h_out : ¬(wStart ≤ qStart + i ∧ qStart + i < wFin) := by omega
    rw [ite_eq_right h_out] at h_sp_i
    exact Option.some.inj ((Array.getElem?_eq_getElem hi1).symm.trans
      (((h_eq1.trans h_sp_i).trans h_eq2.symm).trans (Array.getElem?_eq_getElem hi2)))

private theorem replicate_extract_zero (n start finish : Nat) (h_fin : finish ≤ n) :
    (Array.replicate n (0 : UInt8)).extract start finish = Array.replicate (finish - start) 0 := by
  apply Array.ext
  · rw [extract_size_of_le _ start finish (by rw [Array.size_replicate]; exact h_fin), Array.size_replicate]
  · intro i _ _
    rw [Array.getElem_extract, Array.getElem_replicate, Array.getElem_replicate]

/-- `withExtra` preserves `byteSize`. -/
theorem byteSize_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).byteSize = allocation.byteSize := rfl

/-- `withExtra` preserves backing byte storage length `len`. -/
theorem len_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).len = allocation.len := rfl

/-- `withExtra` preserves `align`. -/
theorem align_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).align = allocation.align := rfl

/-- `withExtra` preserves `mutability`. -/
theorem mutability_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).mutability = allocation.mutability := rfl

/-- `withExtra` preserves `provenanceMap`. -/
theorem provenanceMap_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).provenanceMap = allocation.provenanceMap := rfl

/-- `withExtra` preserves `initializationMask`. -/
theorem initializationMask_withExtra (allocation : Allocation P Unit) (extra : E) :
    (allocation.withExtra extra).initializationMask = allocation.initializationMask := rfl

/-- `withExtra` preserves unchecked raw-byte reads. -/
theorem getBytesUnchecked_withExtra (allocation : Allocation P Unit) (extra : E) (range : AllocRange) :
    (allocation.withExtra extra).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

/-- `mapExtra` preserves `byteSize`. -/
theorem byteSize_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).byteSize = allocation.byteSize := rfl

/-- `mapExtra` preserves backing byte storage length `len`. -/
theorem len_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).len = allocation.len := rfl

/-- `mapExtra` preserves `align`. -/
theorem align_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).align = allocation.align := rfl

/-- `mapExtra` preserves `mutability`. -/
theorem mutability_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).mutability = allocation.mutability := rfl

/-- `mapExtra` preserves `provenanceMap`. -/
theorem provenanceMap_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).provenanceMap = allocation.provenanceMap := rfl

/-- `mapExtra` preserves `initializationMask`. -/
theorem initializationMask_mapExtra (allocation : Allocation P E) (f : E → E') :
    (allocation.mapExtra f).initializationMask = allocation.initializationMask := rfl

/-- `mapExtra` preserves unchecked raw-byte reads. -/
theorem getBytesUnchecked_mapExtra (allocation : Allocation P E) (f : E → E') (range : AllocRange) :
    (allocation.mapExtra f).getBytesUnchecked range = allocation.getBytesUnchecked range := rfl

/-- `mapExtra` preserves provenance-stripping byte reads. -/
theorem getBytesStripProvenance_mapExtra [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout) (range : AllocRange) :
    (allocation.mapExtra f).getBytesStripProvenance layout range =
      allocation.getBytesStripProvenance layout range := rfl

/-- `mapExtra` preserves scalar reads. -/
theorem readScalar_mapExtra [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (f : E → E') (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    (allocation.mapExtra f).readScalar layout range readProvenance =
      allocation.readScalar layout range readProvenance := rfl

/-- `writeBytes` commutes with `mapExtra` on both success and failure states. -/
theorem writeBytes_mapExtra (start : Size) (bytes : Array UInt8) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.writeBytes start bytes ptrSize (allocation.mapExtra f) =
      (match Allocation.writeBytes start bytes ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) :=
  writeBytes_mapExtra_bridge start bytes ptrSize allocation f

/-- `clearProvenance` commutes with `mapExtra` on both success and failure states. -/
theorem clearProvenance_mapExtra (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (f : E → E') :
    Allocation.clearProvenance range ptrSize (allocation.mapExtra f) =
      (match Allocation.clearProvenance range ptrSize allocation with
       | .ok value state => .ok value (state.mapExtra f)
       | .error error state => .error error (state.mapExtra f)) :=
  clearProvenance_mapExtra_bridge range ptrSize allocation f

/-- Full metadata, initialization, provenance, and raw-slice specification of a
successful `Allocation.fromBytes` construction. -/
theorem fromBytes_spec (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (alloc : Allocation P Unit)
    (created : Allocation.fromBytes bytes align mutability = .ok alloc) :
    alloc.byteSize.bytes.toNat = bytes.size ∧
      alloc.len = bytes.size ∧
      alloc.mutability = mutability ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      alloc.initializationMask = InitMask.new alloc.byteSize true ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ bytes.size →
        alloc.getBytesUnchecked range =
          .ok (bytes.extract range.start.bytes.toNat finish.bytes.toNat) := by
  obtain ⟨hbs, hlen, hmut, hex, hnb, hprov, hmask, hfull⟩ :=
    fromBytes_ok_bridge bytes align mutability alloc created
  refine ⟨hbs, hlen, hmut, hex, hnb, hprov, hmask, ?_, fun range finish h_end h_lo h_fin => ?_⟩
  · rw [hmask]; trivial
  · exact getBytesUnchecked_eq_extract alloc range finish bytes hfull h_end h_lo (hbs.symm ▸ h_fin)

/-- Existence of an allocation constructed by `Allocation.fromBytes` whenever
`align` roundtrips through `Align.bytes` / `Align.fromBytes` and `bytes.size`
fits in `UInt64`. -/
theorem fromBytes_exists (bytes : Array UInt8) (align : Align) (alignmentBytes : UInt64)
    (mutability : Mutability)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align)
    (h_fits : bytes.size < 2 ^ 64) :
    ∃ alloc : Allocation P Unit,
      Allocation.fromBytes bytes align mutability = .ok alloc ∧
      alloc.byteSize = Size.ofBytes (UInt64.ofNat bytes.size) ∧
      alloc.align = align :=
  fromBytes_exists_bridge bytes align alignmentBytes mutability h_bytes h_norm h_fits

/-- Full metadata, initialization-mask, provenance, and zeroed-byte-slice
specification of a successful `Allocation.tryNew` backed by `Array.replicate`. -/
theorem tryNew_spec (size : Size) (align : Align) (init : AllocInit)
    (alloc : Allocation P Unit)
    (created : Allocation.tryNew size align init
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc) :
    alloc.byteSize = size ∧
      alloc.len = size.bytes.toNat ∧
      alloc.mutability = .Mut ∧
      alloc.extra = () ∧
      alloc.nativeBuffer = none ∧
      alloc.provenanceMap = ProvenanceMap.new ∧
      (init = .Uninit → alloc.initializationMask = InitMask.new size false) ∧
      (init = .Zero → alloc.initializationMask = InitMask.new size true) ∧
      InitMask.WriteProof.WellFormed alloc.initializationMask ∧
      ∀ (range : AllocRange) (finish : Size),
        range.endExclusive = .ok finish →
        range.start.bytes.toNat ≤ finish.bytes.toNat →
        finish.bytes.toNat ≤ size.bytes.toNat →
        alloc.getBytesUnchecked range =
          .ok (Array.replicate (finish.bytes.toNat - range.start.bytes.toNat) 0) := by
  obtain ⟨hbs, hlen, hmut, hex, hnb, hprov, hmu, hmz, hfull⟩ :=
    tryNew_ok_bridge size align init alloc created
  refine ⟨hbs, hlen, hmut, hex, hnb, hprov, hmu, hmz, ?_, fun range finish h_end h_lo h_fin => ?_⟩
  · cases init
    · rw [hmu rfl]; trivial
    · rw [hmz rfl]; trivial
  · rw [getBytesUnchecked_eq_extract alloc range finish (Array.replicate size.bytes.toNat 0)
      hfull h_end h_lo (hbs ▸ h_fin)]
    exact congrArg Except.ok (replicate_extract_zero size.bytes.toNat _ _ h_fin)

/-- Existence of a zeroed-backing `Allocation.tryNew` result for any valid
alignment and either `.Uninit` or `.Zero` initialization mode. -/
theorem tryNew_exists (size : Size) (align : Align) (alignmentBytes : UInt64) (init : AllocInit)
    (h_bytes : Align.bytes align = .ok alignmentBytes)
    (h_norm : Align.fromBytes alignmentBytes = .ok align) :
    ∃ alloc : Allocation P Unit,
      Allocation.tryNew size align init
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok alloc ∧
      alloc.align = align :=
  tryNew_exists_bridge size align alignmentBytes init h_bytes h_norm

/-- An in-bounds `getBytesUnchecked` slice succeeds and has length
`finish - range.start`. -/
theorem getBytesUnchecked_size (allocation : Allocation P E) (range : AllocRange) (finish : Size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    ∃ slice, allocation.getBytesUnchecked range = .ok slice ∧
      slice.size = finish.bytes.toNat - range.start.bytes.toNat := by
  obtain ⟨fullBytes, h_full, h_fsz⟩ := getBytesUnchecked_full_exists allocation storage
  refine ⟨fullBytes.extract range.start.bytes.toNat finish.bytes.toNat,
    getBytesUnchecked_eq_extract allocation range finish fullBytes h_full endEq startLe inBounds,
    extract_size_of_le fullBytes _ _ (h_fsz.symm ▸ inBounds)⟩

/-- Reading a subrange `rInner ⊆ rOuter` via `getBytesUnchecked` returns the
corresponding `Array.extract` slice of the outer read. -/
theorem getBytesUnchecked_subrange (allocation : Allocation P E)
    (rOuter rInner : AllocRange) (fOuter fInner : Size) (outerBytes : Array UInt8)
    (h_outer_end : rOuter.endExclusive = .ok fOuter)
    (h_inner_end : rInner.endExclusive = .ok fInner)
    (h_lo : rOuter.start.bytes.toNat ≤ rInner.start.bytes.toNat)
    (h_mid : rInner.start.bytes.toNat ≤ fInner.bytes.toNat)
    (h_hi : fInner.bytes.toNat ≤ fOuter.bytes.toNat)
    (h_outer : allocation.getBytesUnchecked rOuter = .ok outerBytes) :
    allocation.getBytesUnchecked rInner =
      .ok (outerBytes.extract
        (rInner.start.bytes.toNat - rOuter.start.bytes.toNat)
        (fInner.bytes.toNat - rOuter.start.bytes.toNat)) := by
  obtain ⟨storage, h_o_lo, h_o_ib⟩ :=
    getBytesUnchecked_ok_bounds allocation rOuter fOuter outerBytes h_outer_end h_outer
  obtain ⟨fullBytes, h_full, h_fsz⟩ := getBytesUnchecked_full_exists allocation storage
  have h_o_eq := getBytesUnchecked_eq_extract allocation rOuter fOuter fullBytes h_full h_outer_end h_o_lo h_o_ib
  have h_ob : outerBytes = fullBytes.extract rOuter.start.bytes.toNat fOuter.bytes.toNat :=
    Except.ok.inj (h_outer.symm.trans h_o_eq)
  rw [getBytesUnchecked_eq_extract allocation rInner fInner fullBytes h_full h_inner_end h_mid
    (Nat.le_trans h_hi h_o_ib), h_ob]
  exact congrArg Except.ok (extract_subrange fullBytes _ _ _ _ h_lo h_mid h_hi (h_fsz.symm ▸ h_o_ib))

/-- Joining two adjacent `getBytesUnchecked` slices `[r1.start, mid)` and
`[mid, fin)` yields the concatenated byte array on `[r1.start, fin)`. -/
theorem getBytesUnchecked_split (allocation : Allocation P E)
    (r1 r2 r12 : AllocRange) (mid fin : Size) (b1 b2 : Array UInt8)
    (h_end1 : r1.endExclusive = .ok mid)
    (h_start2 : r2.start = mid)
    (h_end2 : r2.endExclusive = .ok fin)
    (h_start12 : r12.start = r1.start)
    (h_end12 : r12.endExclusive = .ok fin)
    (h_lo1 : r1.start.bytes.toNat ≤ mid.bytes.toNat)
    (h_lo2 : mid.bytes.toNat ≤ fin.bytes.toNat)
    (h_get1 : allocation.getBytesUnchecked r1 = .ok b1)
    (h_get2 : allocation.getBytesUnchecked r2 = .ok b2) :
    allocation.getBytesUnchecked r12 = .ok (b1 ++ b2) := by
  obtain ⟨storage, _, h_fin_ib⟩ :=
    getBytesUnchecked_ok_bounds allocation r2 fin b2 h_end2 h_get2
  obtain ⟨fullBytes, h_full, h_fsz⟩ := getBytesUnchecked_full_exists allocation storage
  have hs1 := getBytesUnchecked_eq_extract allocation r1 mid fullBytes h_full h_end1 h_lo1 (Nat.le_trans h_lo2 h_fin_ib)
  have hs2 := getBytesUnchecked_eq_extract allocation r2 fin fullBytes h_full h_end2 (h_start2 ▸ h_lo2) h_fin_ib
  have hb1 : b1 = fullBytes.extract r1.start.bytes.toNat mid.bytes.toNat := Except.ok.inj (h_get1.symm.trans hs1)
  have hb2 : b2 = fullBytes.extract mid.bytes.toNat fin.bytes.toNat :=
    h_start2 ▸ Except.ok.inj (h_get2.symm.trans hs2)
  rw [getBytesUnchecked_eq_extract allocation r12 fin fullBytes h_full h_end12
    (h_start12 ▸ Nat.le_trans h_lo1 h_lo2) h_fin_ib, h_start12, hb1, hb2]
  exact congrArg Except.ok (extract_split fullBytes _ _ _ h_lo1 h_lo2 (h_fsz.symm ▸ h_fin_ib))

private theorem targetUIntBytesPub_eq_ofFn (layout : TargetDataLayout) (size : Size) (bits : U128)
    (limit : size.bytes.toNat ≤ 16) :
    targetUIntBytesPub layout size bits =
      .ok (Array.ofFn (fun i : Fin size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else size.bytes.toNat - i.1 - 1))) % 256))) := by
  let byteFn : Nat → UInt8 := fun index =>
    UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))) % 256)
  have h_loop : ∀ (indices : List Nat) (acc : Array UInt8),
      (forIn indices acc (fun index cur =>
        (Except.ok (ForInStep.yield (cur.push (byteFn index))) :
          Except AllocError (ForInStep (Array UInt8))))) =
      .ok (acc ++ (indices.map byteFn).toArray) := by
    intro indices
    induction indices with
    | nil =>
      intro acc
      simp only [List.forIn_nil, Pure.pure, Except.pure, List.map_nil, Array.append_empty]
    | cons idx rest ih =>
      intro acc
      rw [List.forIn_cons]
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [ih (acc.push (byteFn idx))]
      apply congrArg Except.ok
      apply Array.ext
      · simp only [Array.size_append, Array.size_push, List.size_toArray, List.length_map,
          List.length_cons, Nat.add_assoc, Nat.add_comm 1]
      · intro k _ _
        by_cases hk : k < acc.size
        · rw [Array.getElem_append_left (by rw [Array.size_push]; exact Nat.lt_succ_of_lt hk),
            Array.getElem_push_lt hk, Array.getElem_append_left hk]
        · by_cases hk_eq : k = acc.size
          · subst hk_eq
            rw [Array.getElem_append_left (by rw [Array.size_push]; exact Nat.lt_succ_self _),
              Array.getElem_push_eq, Array.getElem_append_right (Nat.le_refl _)]
            simp only [Nat.sub_self, List.map_cons, List.getElem_toArray, List.getElem_cons_zero]
          · rw [Array.getElem_append_right (by rw [Array.size_push]; omega),
              Array.getElem_append_right (Nat.le_of_not_lt hk)]
            simp only [Array.size_push, List.map_cons, List.getElem_toArray]
            have h_pos : k - acc.size = (k - (acc.size + 1)) + 1 := by omega
            simp only [h_pos, List.getElem_cons_succ]
  have small : ¬size.bytes > 16 := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
    exact Nat.not_lt.mpr limit
  unfold targetUIntBytesPub
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_inst := h_loop (List.range' 0 [:size.bytes.toNat].size) #[]
  dsimp only [byteFn] at h_inst
  change (forIn (List.range' 0 [:size.bytes.toNat].size) #[] (fun index cur =>
    Except.ok (ForInStep.yield (cur.push (UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then index else size.bytes.toNat - index - 1))) % 256))))) >>=
    Except.ok) = _
  rw [h_inst]
  simp only [Bind.bind, Except.bind, Array.empty_append]
  apply congrArg Except.ok
  apply Array.ext
  · simp only [List.size_toArray, List.length_map, List.length_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Array.size_ofFn]
  · intro i _ _
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.zero_add,
      Nat.one_mul, Array.getElem_ofFn]

private theorem readUIntPub_eq_foldl (layout : TargetDataLayout) (bytes : Array UInt8)
    (limit : bytes.size ≤ 16) :
    readUIntPub layout bytes =
      .ok (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc index =>
        acc + (bytes[index]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then index else bytes.size - index - 1))) 0)) := by
  have h_loop : ∀ (indices : List Nat) (acc : Nat),
      (∀ idx ∈ indices, idx < bytes.size) →
      (forIn indices acc (fun index value =>
        (match bytes[index]? with
          | some byte =>
            pure (ForInStep.yield (value + byte.toNat * 2 ^ (8 *
              (if layout.endian == .little then index else bytes.size - index - 1))))
          | _ => do
            throw (.invalidSliceEndpoints index (index + 1) bytes.size)
            pure (ForInStep.yield value) :
          Except AllocError (ForInStep Nat)))) =
      .ok (indices.foldl (fun v index =>
        v + (bytes[index]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then index else bytes.size - index - 1))) acc) := by
    intro indices
    induction indices with
    | nil => intro acc _; rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < bytes.size := h_in idx (List.mem_cons_self ..)
      have h_get : bytes[idx]? = some (bytes[idx]'h_ib) := Array.getElem?_eq_getElem h_ib
      rw [List.forIn_cons, List.foldl_cons]
      simp only [h_get, Option.getD_some, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  have small : ¬bytes.size > 16 := Nat.not_lt.mpr limit
  unfold readUIntPub
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range']
  have h_rng_eq : List.range' [0:bytes.size].start [0:bytes.size].size [0:bytes.size].step =
      List.range bytes.size := by
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range_eq_range']
  rw [h_rng_eq, h_loop (List.range bytes.size) 0 (fun idx h => List.mem_range.mp h)]
  rfl

private theorem digit_step_mod (val m : Nat) :
    val % 2 ^ (8 * m) + ((val / 2 ^ (8 * m)) % 256) * 2 ^ (8 * m) =
      val % 2 ^ (8 * (m + 1)) := by
  let P := 2 ^ (8 * m)
  have hP_pos : 0 < P := Nat.two_pow_pos (8 * m)
  let r := val % P
  let d := (val / P) % 256
  let q := (val / P) / 256
  have hr : r < P := Nat.mod_lt val hP_pos
  have hd : d < 256 := Nat.mod_lt _ (by decide)
  have h_dp : d * P ≤ 255 * P := Nat.mul_le_mul_right P (Nat.le_of_lt_succ hd)
  have h_sum_lt : r + d * P < P * 256 := by omega
  have h_div1 : P * (val / P) + r = val := Nat.div_add_mod val P
  have h_div2 : 256 * q + d = val / P := Nat.div_add_mod (val / P) 256
  have h_pow_succ : 2 ^ (8 * (m + 1)) = P * 256 := by
    rw [Nat.mul_add, Nat.pow_add]
  have h_val_decomp : val = (r + d * P) + (P * 256) * q := by
    calc
      val = P * (val / P) + r := h_div1.symm
      _ = P * (256 * q + d) + r := by rw [← h_div2]
      _ = (r + d * P) + (P * 256) * q := by
        rw [Nat.mul_add, Nat.mul_comm P d, ← Nat.mul_assoc, Nat.add_comm _ r, Nat.add_assoc, Nat.add_comm (P * 256 * q)]
  have h_rhs : val % 2 ^ (8 * (m + 1)) = ((r + d * P) + (P * 256) * q) % (P * 256) := by
    rw [h_pow_succ]
    exact congrArg (· % (P * 256)) h_val_decomp
  rw [h_rhs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_sum_lt]

private theorem foldl_add_init (xs : List Nat) (g : Nat → Nat) (init : Nat) :
    xs.foldl (fun acc x => acc + g x) init =
      init + xs.foldl (fun acc x => acc + g x) 0 := by
  induction xs generalizing init with
  | nil => exact (Nat.add_zero init).symm
  | cons x rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + g x), ih (g x), Nat.add_assoc]

private theorem endian_digits_fold_mod (endian : Endian) (val n : Nat) :
    (List.range n).foldl (fun acc idx =>
      acc + ((val / 2 ^ (8 * (if endian == .little then idx else n - idx - 1))) % 256) *
        2 ^ (8 * (if endian == .little then idx else n - idx - 1))) 0 =
      val % 2 ^ (8 * n) := by
  cases endian with
  | little =>
    simp only [beq_self_eq_true, ↓reduceIte]
    induction n with
    | zero => simp only [List.range_zero, List.foldl_nil, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      exact digit_step_mod val m
  | big =>
    have h_be : (Endian.big == Endian.little) = false := rfl
    simp only [h_be, Bool.false_eq_true, ↓reduceIte]
    induction n with
    | zero => simp only [List.range_zero, List.foldl_nil, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
    | succ m ih =>
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hm0 : m + 1 - 0 - 1 = m := by omega
      simp only [Nat.zero_add, hm0]
      have h_fn_eq : (fun acc (x : Nat) =>
          acc + ((val / 2 ^ (8 * (m + 1 - x.succ - 1))) % 256) *
            2 ^ (8 * (m + 1 - x.succ - 1))) =
        (fun acc (x : Nat) =>
          acc + ((val / 2 ^ (8 * (m - x - 1))) % 256) * 2 ^ (8 * (m - x - 1))) := by
        funext acc x
        have hx : m + 1 - x.succ - 1 = m - x - 1 := by omega
        rw [hx]
      rw [h_fn_eq, foldl_add_init, ih, Nat.add_comm]
      exact digit_step_mod val m

private theorem readUIntPub_ofFn_mod (layout : TargetDataLayout) (n val : Nat)
    (limit : n ≤ 16) :
    readUIntPub layout (Array.ofFn (fun i : Fin n =>
      UInt8.ofNat ((val / 2 ^ (8 *
        (if layout.endian == .little then i.1 else n - i.1 - 1))) % 256))) =
      .ok (BitVec.ofNat 128 (val % 2 ^ (8 * n))) := by
  let arr := Array.ofFn (fun i : Fin n =>
    UInt8.ofNat ((val / 2 ^ (8 *
      (if layout.endian == .little then i.1 else n - i.1 - 1))) % 256))
  have h_sz : arr.size = n := Array.size_ofFn ..
  rw [readUIntPub_eq_foldl layout arr (h_sz.symm ▸ limit), h_sz]
  apply congrArg Except.ok
  apply congrArg (BitVec.ofNat 128)
  have h_congr : ∀ (xs : List Nat) (acc : Nat),
      (∀ idx ∈ xs, idx < n) →
      xs.foldl (fun a idx =>
        a + (arr[idx]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then idx else n - idx - 1))) acc =
      xs.foldl (fun a idx =>
        a + ((val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256) *
          2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) acc := by
    intro xs
    induction xs with
    | nil => intro acc _; rfl
    | cons idx rest ih =>
      intro acc h_in
      have h_ib : idx < n := h_in idx (List.mem_cons_self ..)
      have h_elem : (arr[idx]?.getD 0).toNat =
          (val / 2 ^ (8 * (if layout.endian == .little then idx else n - idx - 1))) % 256 := by
        rw [Array.getElem?_eq_getElem (h_sz.symm ▸ h_ib), Option.getD_some]
        dsimp only [arr]
        rw [Array.getElem_ofFn, UInt8.toNat_ofNat', Nat.mod_mod_of_dvd _ (Nat.dvd_refl 256)]
      simp only [List.foldl_cons, h_elem]
      exact ih _ (fun x hx => h_in x (List.mem_cons_of_mem _ hx))
  rw [h_congr (List.range n) 0 (fun idx h => List.mem_range.mp h)]
  exact endian_digits_fold_mod layout.endian val n

/-- `getBytesStripProvenance` reports `.invalidUninitBytes` whenever the
initialization check returns an uninitialized subrange `bad`. -/
theorem getBytesStripProvenance_uninit_err [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.getBytesStripProvenance layout range =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) :=
  getBytesStripProvenance_uninit_bridge allocation layout range bad h_uninit

/-- When `range` is initialized and either provenance offsets act as addresses
or the range has no overlapping provenance, `getBytesStripProvenance` agrees
with `getBytesUnchecked`. -/
theorem getBytesStripProvenance_ok [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.getBytesStripProvenance layout range = allocation.getBytesUnchecked range :=
  getBytesStripProvenance_ok_bridge allocation layout range h_init h_prov

/-- `readScalar` reports `.invalidUninitBytes` whenever the initialization check
returns an uninitialized subrange `bad`. -/
theorem readScalar_uninit_err [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range bad : AllocRange) (readProvenance : Bool)
    (h_uninit : allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    allocation.readScalar layout range readProvenance =
      .error (.invalidUninitBytes (some ⟨range, bad⟩)) := by
  rw [readScalar_eq, h_uninit]
  rfl

private theorem readScalar_after_readUInt [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) (bytes : Array UInt8) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_slice : allocation.getBytesUnchecked range = .ok bytes)
    (h_read : readUIntPub layout bytes = .ok bits) :
    allocation.readScalar layout range readProvenance =
      if readProvenance then
        let targetSize := Size.fromBits layout.pointerWidth.bits
        if range.size != targetSize then
          throw (.scalarPointerNotTargetSized range.size targetSize)
        else
          (match allocation.provenanceMap.readPtr range.start targetSize with
            | .ok provenance => pure provenance
            | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
            | .error reason => throw (.provenance reason)) >>= fun provenance =>
          match provenance with
          | some provenance =>
            if bits.toNat > 18446744073709551615 then
              throw (.pointerBitsDoNotFitOffset bits)
            else
              pure (Scalar.fromPointer layout
                (Pointer.new provenance (Size.ofBytes (UInt64.ofNat bits.toNat))))
          | none => (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      else
        if PointerProvenance.offsetIsAddr (Prov := P) then
          (Scalar.fromUInt bits range.size).mapError AllocError.scalar
        else
          (allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits)).mapError AllocError.provenance >>= fun isEmpty =>
            if isEmpty then (Scalar.fromUInt bits range.size).mapError AllocError.scalar
            else throw (.readPointerAsInt none) := by
  rw [readScalar_eq, h_init]
  change (allocation.getBytesUnchecked range >>= fun b => readUIntPub layout b >>= _) = _
  rw [h_slice]
  dsimp only [Bind.bind, Except.bind]
  rw [h_read]
  dsimp only [Bind.bind, Except.bind]
  cases readProvenance
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    by_cases h_sz : (range.size != Size.fromBits layout.pointerWidth.bits) = true
    · rw [ite_eq_left h_sz, ite_eq_left h_sz]; rfl
    · rw [ite_eq_right h_sz, ite_eq_right h_sz]
      cases allocation.provenanceMap.readPtr range.start (Size.fromBits layout.pointerWidth.bits) with
      | error e => cases e <;> rfl
      | ok p =>
        cases p with
        | none => dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
        | some prov =>
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
          by_cases h_gt : bits.toNat > 18446744073709551615
          · rw [ite_eq_left h_gt, ite_eq_left h_gt]; rfl
          · rw [ite_eq_right h_gt, ite_eq_right h_gt]

/-- Closed-form byte-fold decoding specification of `readScalar` with
`readProvenance := false` on an initialized range of at most 16 bytes. -/
theorem readScalar_int_of_bytes [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bytes : Array UInt8)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_slice : allocation.getBytesUnchecked range = .ok bytes)
    (h_limit : bytes.size ≤ 16)
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt (BitVec.ofNat 128 ((List.range bytes.size).foldl (fun acc idx =>
        acc + (bytes[idx]?.getD 0).toNat * 2 ^ (8 *
          (if layout.endian == .little then idx else bytes.size - idx - 1))) 0))
        range.size).mapError AllocError.scalar := by
  rw [readScalar_after_readUInt allocation layout range false bytes _ h_init h_slice
    (readUIntPub_eq_foldl layout bytes h_limit)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases h_prov with h_addr | h_empty
  · rw [ite_eq_left h_addr]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · rw [ite_eq_left h_addr]
    · rw [ite_eq_right h_addr, h_empty]; rfl

/-- Endian-independent integer scalar roundtrip for `readScalar` with
`readProvenance := false` over bytes serialized from `bits`. -/
theorem readScalar_int_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range false =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  have h_read := readUIntPub_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  rw [readScalar_after_readUInt allocation layout range false _ bits h_init h_slice h_read]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases h_prov with h_addr | h_empty
  · rw [ite_eq_left h_addr]
  · by_cases h_addr : PointerProvenance.offsetIsAddr (Prov := P) = true
    · rw [ite_eq_left h_addr]
    · rw [ite_eq_right h_addr, h_empty]; rfl

/-- Endian-independent pointer scalar roundtrip for `readScalar` with
`readProvenance := true` when the provenance map yields `some ptr.provenance`. -/
theorem readScalar_ptr_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (ptr : Pointer P)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_off_bound : ptr.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok (some ptr.provenance))
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range true = .ok (Scalar.fromPointer layout ptr) := by
  have h_read := readUIntPub_ofFn_mod layout range.size.bytes.toNat ptr.offset.bytes.toNat h_limit
  rw [Nat.mod_eq_of_lt h_off_bound] at h_read
  have h_u64_lt := ptr.offset.bytes.toNat_lt
  have h_lt128 : ptr.offset.bytes.toNat < 2 ^ 128 := Nat.lt_trans h_u64_lt (by decide)
  have h_bv_nat : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt128]
  have h_not_gt : ¬(18446744073709551615 < ptr.offset.bytes.toNat) :=
    Nat.not_lt.mpr (Nat.le_of_lt_succ h_u64_lt)
  have h_ptr_eta : Pointer.new ptr.provenance (Size.ofBytes (UInt64.ofNat ptr.offset.bytes.toNat)) = ptr := by
    cases ptr with
    | mk off _ =>
      cases off with
      | mk b =>
        simp only [Pointer.new, Size.ofBytes, UInt64.ofNat_toNat]
  rw [readScalar_after_readUInt allocation layout range true _ _ h_init h_slice h_read]
  simp only [↓reduceIte, h_ptr_sz, bne_self_eq_false, Bool.false_eq_true, h_prov,
    Bind.bind, Except.bind, Pure.pure, Except.pure, h_bv_nat, gt_iff_lt, h_not_gt, h_ptr_eta]

/-- Endian-independent scalar roundtrip for `readScalar` with
`readProvenance := true` when the provenance map yields `none` (an integer value
read at pointer width). -/
theorem readScalar_ptr_none_roundtrip [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (bits : U128)
    (h_init : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (h_ptr_sz : range.size = Size.fromBits layout.pointerWidth.bits)
    (h_limit : range.size.bytes.toNat ≤ 16)
    (h_bits_bound : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (h_prov : allocation.provenanceMap.readPtr range.start
      (Size.fromBits layout.pointerWidth.bits) = .ok none)
    (h_slice : allocation.getBytesUnchecked range =
      .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
        UInt8.ofNat ((bits.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) :
    allocation.readScalar layout range true =
      (Scalar.fromUInt bits range.size).mapError AllocError.scalar := by
  have h_read := readUIntPub_ofFn_mod layout range.size.bytes.toNat bits.toNat h_limit
  rw [Nat.mod_eq_of_lt h_bits_bound, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h_read
  rw [readScalar_after_readUInt allocation layout range true _ bits h_init h_slice h_read]
  simp only [↓reduceIte, h_ptr_sz, bne_self_eq_false, Bool.false_eq_true, h_prov,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Partial-range specification of `Allocation.writeScalar`, returning the
updated allocation together with preserved metadata, initialization-mask
transition (`setRange` and `isRangeInitialized`), provenance transition,
exact serialized bytes at `range`, and a disjoint-range raw-byte frame. -/
theorem writeScalar_spec (layout : TargetDataLayout)
    (allocation : Allocation P E) (range : AllocRange) (value : Scalar P)
    (converted : ScalarBitsOrPointer P) (cleared nextProvenance : ProvenanceMap P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok converted)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (insert : match converted with
      | .bits _ => nextProvenance = cleared
      | .pointer pointer => range.size = Size.fromBits layout.pointerWidth.bits ∧
          cleared.insertPtr range.start pointer.provenance
            (Size.fromBits layout.pointerWidth.bits) = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range true = .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      (∀ b, converted = .bits b →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat ((b.toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      (∀ p, converted = .pointer p →
        updated.getBytesUnchecked range =
          .ok (Array.ofFn (fun i : Fin range.size.bytes.toNat =>
            UInt8.ofNat (((BitVec.ofNat 128 p.offset.bytes.toNat).toNat /
              2 ^ (8 * (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256)))) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (range.start.bytes.toNat + range.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ range.start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt bound allocation.byteSize.bytes.toNat_lt
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (add_size_no_wrap range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat :=
    Nat.pos_of_ne_zero (fun h0 => nonzero (UInt64.toNat_inj.mp h0))
  have h_lt_sf : range.start.bytes.toNat < finish.bytes.toNat :=
    finishNat ▸ Nat.lt_add_of_pos_right positive
  have h_fin_ib : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat := finishNat ▸ bound
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint h_lt_sf (maskLength.symm ▸ h_fin_ib)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      h_lt_sf (maskLength.symm ▸ h_fin_ib) maskOk
  obtain ⟨fullBytes, h_full, h_fsz⟩ := getBytesUnchecked_full_exists allocation storage
  have h_slice := getBytesUnchecked_eq_extract allocation range finish fullBytes h_full
    endpoint (Nat.le_of_lt h_lt_sf) h_fin_ib
  let bits : U128 := match converted with
    | .bits b => b
    | .pointer p => BitVec.ofNat 128 p.offset.bytes.toNat
  let data := Array.ofFn (fun i : Fin range.size.bytes.toNat =>
    UInt8.ofNat ((bits.toNat / 2 ^ (8 *
      (if layout.endian == .little then i.1 else range.size.bytes.toNat - i.1 - 1))) % 256))
  have h_data : targetUIntBytesPub layout range.size bits = .ok data :=
    targetUIntBytesPub_eq_ofFn layout range.size bits width
  have h_dsz : data.size = range.size.bytes.toNat := Array.size_ofFn ..
  have h_spliced_sz :
      (fullBytes.extract 0 range.start.bytes.toNat ++ data ++
        fullBytes.extract (range.start.bytes.toNat + range.size.bytes.toNat) fullBytes.size).size =
        allocation.byteSize.bytes.toNat := by
    rw [splice_size fullBytes data range.start.bytes.toNat (range.start.bytes.toNat + range.size.bytes.toNat)
      (Nat.le_add_right _ _) (h_fsz.symm ▸ bound) (by rw [h_dsz, Nat.add_sub_cancel_left]), h_fsz]
  obtain ⟨updated, h_ws, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_im, h_pm, h_upd_full⟩ :=
    writeScalar_step_bridge layout allocation range value converted bits mask cleared nextProvenance
      fullBytes _ data (by cases converted <;> rfl) h_full mutable conversion h_slice maskOk
      (clear fullBytes h_full) h_data h_spliced_sz (by cases converted <;> exact insert)
  have h_get_data : updated.getBytesUnchecked range = .ok data := by
    rw [getBytesUnchecked_eq_extract updated range finish _ h_upd_full endpoint
      (Nat.le_of_lt h_lt_sf) (h_bs.symm ▸ h_fin_ib), finishNat]
    exact congrArg Except.ok (splice_extract_exact fullBytes data _ _
      (Nat.le_add_right _ _) (h_fsz.symm ▸ bound) (by rw [h_dsz, Nat.add_sub_cancel_left]))
  refine ⟨updated, h_ws, h_bs, h_len, h_mut, h_al, h_ex, h_nb,
    h_im ▸ maskSize, h_im ▸ maskWF, h_im ▸ maskOk, h_im ▸ h_is_init, h_pm,
    fun b hb => by subst hb; exact h_get_data,
    fun p hp => by subst hp; exact h_get_data,
    fun qRange qFin h_qend h_qlo h_qib h_disj => ?_⟩
  rw [getBytesUnchecked_eq_extract updated qRange qFin _ h_upd_full h_qend h_qlo (h_bs.symm ▸ h_qib),
    getBytesUnchecked_eq_extract allocation qRange qFin fullBytes h_full h_qend h_qlo h_qib]
  exact congrArg Except.ok (splice_extract_disjoint fullBytes data _ _ _ _
    (Nat.le_add_right _ _) (h_fsz.symm ▸ bound) h_qlo (h_fsz.symm ▸ h_qib)
    (by rw [h_dsz, Nat.add_sub_cancel_left]) h_disj)

/-- Writing an empty byte array at any in-bounds offset is a no-op (even on
immutable allocations). -/
theorem writeBytes_zero_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E)
    (h_empty : bytes.size = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (inBounds : start.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Allocation.writeBytes start bytes ptrSize allocation = .ok () allocation := by
  have h_end : (allocRange start Size.ZERO).endExclusive = .ok start := by
    cases start
    simp [allocRange, AllocRange.endExclusive, AllocRange.end, Size.ZERO, Size.ofBytes, Size.add, Except.mapError]
  obtain ⟨fullBytes, h_full, _⟩ := getBytesUnchecked_full_exists allocation storage
  have h_slice := getBytesUnchecked_eq_extract allocation (allocRange start Size.ZERO) start
    fullBytes h_full h_end (Nat.le_refl _) inBounds
  have h_ext0 : fullBytes.extract start.bytes.toNat start.bytes.toNat = #[] := by
    apply Array.ext
    · rw [Array.size_extract]; simp only [Array.size_empty]; omega
    · intro i hi _; rw [Array.size_extract] at hi; omega
  dsimp only [allocRange] at h_slice
  rw [h_ext0] at h_slice
  exact writeBytes_zero_bridge start ptrSize bytes allocation h_empty h_slice

/-- Partial-range specification of `Allocation.writeBytes` for a nonempty byte
array, characterizing metadata preservation, initialization-mask update,
provenance clear, written bytes, and disjoint-range byte framing. -/
theorem writeBytes_spec (start ptrSize : Size) (bytes : Array UInt8)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (h_nonempty : 0 < bytes.size)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : start.bytes.toNat + bytes.size ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) fullBytes ptrSize =
        .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeBytes start bytes ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) true =
        .ok updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized
        (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) = .ok (.ok ()) ∧
      updated.provenanceMap = nextProvenance ∧
      updated.getBytesUnchecked (allocRange start (Size.ofBytes (UInt64.ofNat bytes.size))) =
        .ok bytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ allocation.byteSize.bytes.toNat →
        (start.bytes.toNat + bytes.size ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ start.bytes.toNat) →
        updated.getBytesUnchecked qRange = allocation.getBytesUnchecked qRange := by
  have h_sum_lt : start.bytes.toNat + bytes.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt inBounds allocation.byteSize.bytes.toNat_lt
  have h_bsz_lt : bytes.size < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h_sum_lt
  let writeSize := Size.ofBytes (UInt64.ofNat bytes.size)
  have h_wsz_nat : writeSize.bytes.toNat = bytes.size := by
    simp only [writeSize, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_bsz_lt]
  let range := allocRange start writeSize
  have fits : start.bytes.toNat + writeSize.bytes.toNat < 2 ^ 64 := h_wsz_nat.symm ▸ h_sum_lt
  let finish := Size.ofBytes (start.bytes + writeSize.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end range allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (add_size_no_wrap start writeSize fits)
  have finishNat : finish.bytes.toNat = start.bytes.toNat + bytes.size := by
    have h_def : finish.bytes.toNat = (start.bytes + writeSize.bytes).toNat := rfl
    rw [h_def, UInt64.toNat_add, Nat.mod_eq_of_lt fits, h_wsz_nat]
  have h_lt_sf : range.start.bytes.toNat < finish.bytes.toNat :=
    finishNat ▸ Nat.lt_add_of_pos_right h_nonempty
  have h_fin_ib : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat := finishNat ▸ inBounds
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish true
      maskValid endpoint h_lt_sf (maskLength.symm ▸ h_fin_ib)
  have h_is_init : mask.isRangeInitialized range = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true
      allocation.initializationMask mask range finish maskValid endpoint
      h_lt_sf (maskLength.symm ▸ h_fin_ib) maskOk
  obtain ⟨fullBytes, h_full, h_fsz⟩ := getBytesUnchecked_full_exists allocation storage
  have h_slice := getBytesUnchecked_eq_extract allocation range finish fullBytes h_full
    endpoint (Nat.le_of_lt h_lt_sf) h_fin_ib
  have h_bsz_eq : bytes.size = finish.bytes.toNat - start.bytes.toNat := by
    rw [finishNat, Nat.add_sub_cancel_left]
  have h_spliced_sz :
      (fullBytes.extract 0 start.bytes.toNat ++ bytes ++
        fullBytes.extract finish.bytes.toNat fullBytes.size).size =
        allocation.byteSize.bytes.toNat := by
    rw [splice_size fullBytes bytes start.bytes.toNat finish.bytes.toNat
      (Nat.le_of_lt h_lt_sf) (h_fsz.symm ▸ h_fin_ib) h_bsz_eq, h_fsz]
  obtain ⟨updated, h_wb, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_im, h_pm, h_upd_full⟩ :=
    writeBytes_step_bridge start ptrSize finish bytes allocation mask nextProvenance
      fullBytes _ h_full h_bsz_lt (Nat.ne_of_gt h_nonempty) h_slice mutable maskOk
      (clear fullBytes h_full) endpoint h_spliced_sz
  refine ⟨updated, h_wb, h_bs, h_len, h_mut, h_al, h_ex, h_nb,
    h_im ▸ maskSize, h_im ▸ maskWF, h_im ▸ maskOk, h_im ▸ h_is_init, h_pm, ?_, ?_⟩
  · rw [getBytesUnchecked_eq_extract updated range finish _ h_upd_full endpoint
      (Nat.le_of_lt h_lt_sf) (h_bs.symm ▸ h_fin_ib)]
    exact congrArg Except.ok (splice_extract_exact fullBytes bytes _ _
      (Nat.le_of_lt h_lt_sf) (h_fsz.symm ▸ h_fin_ib) h_bsz_eq)
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    rw [getBytesUnchecked_eq_extract updated qRange qFin _ h_upd_full h_qend h_qlo (h_bs.symm ▸ h_qib),
      getBytesUnchecked_eq_extract allocation qRange qFin fullBytes h_full h_qend h_qlo h_qib]
    exact congrArg Except.ok (splice_extract_disjoint fullBytes bytes start.bytes.toNat finish.bytes.toNat
      qRange.start.bytes.toNat qFin.bytes.toNat (Nat.le_of_lt h_lt_sf) (h_fsz.symm ▸ h_fin_ib)
      h_qlo (h_fsz.symm ▸ h_qib) h_bsz_eq (finishNat.symm ▸ h_disj))

/-- Uninitializing a zero-sized in-bounds range is a no-op (even on immutable
allocations). -/
theorem writeUninit_zero_spec (range : AllocRange) (finish ptrSize : Size)
    (allocation : Allocation P E)
    (h_zero : range.size.bytes = 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (endEq : range.endExclusive = .ok finish)
    (startLe : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat) :
    Allocation.writeUninit range ptrSize allocation = .ok () allocation := by
  obtain ⟨fullBytes, h_full, _⟩ := getBytesUnchecked_full_exists allocation storage
  have h_slice := getBytesUnchecked_eq_extract allocation range finish fullBytes h_full endEq startLe inBounds
  exact writeUninit_zero_bridge range ptrSize allocation _ h_zero h_slice

/-- Partial-range specification of `Allocation.writeUninit`: clears the
initialization mask over `range`, clears overlapping provenance, and leaves
raw byte storage unchanged on every range. -/
theorem writeUninit_spec (range : AllocRange) (ptrSize : Size)
    (allocation : Allocation P E) (nextProvenance : ProvenanceMap P)
    (nonzero : range.size.bytes ≠ 0)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (inBounds : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes ptrSize = .ok () nextProvenance) :
    ∃ updated,
      Allocation.writeUninit range ptrSize allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧
      updated.len = allocation.len ∧
      updated.mutability = allocation.mutability ∧
      updated.align = allocation.align ∧
      updated.extra = allocation.extra ∧
      updated.nativeBuffer = allocation.nativeBuffer ∧
      updated.initializationMask.len = allocation.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      allocation.initializationMask.setRange range false = .ok updated.initializationMask ∧
      updated.provenanceMap = nextProvenance ∧
      ∀ (anyRange : AllocRange),
        updated.getBytesUnchecked anyRange = allocation.getBytesUnchecked anyRange := by
  have fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt inBounds allocation.byteSize.bytes.toNat_lt
  let finish := Size.ofBytes (range.start.bytes + range.size.bytes)
  have endpoint : range.endExclusive = .ok finish := by
    unfold AllocRange.endExclusive AllocRange.end
    exact congrArg (Except.mapError MemoryError.sizeError) (add_size_no_wrap range.start range.size fits)
  have finishNat : finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat := by
    simp only [finish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have positive : 0 < range.size.bytes.toNat :=
    Nat.pos_of_ne_zero (fun h0 => nonzero (UInt64.toNat_inj.mp h0))
  have h_lt_sf : range.start.bytes.toNat < finish.bytes.toNat :=
    finishNat ▸ Nat.lt_add_of_pos_right positive
  have h_fin_ib : finish.bytes.toNat ≤ allocation.byteSize.bytes.toNat := finishNat ▸ inBounds
  obtain ⟨mask, maskOk, maskSize, maskWF⟩ :=
    InitMask.WriteProof.set_range_exists allocation.initializationMask range finish false
      maskValid endpoint h_lt_sf (maskLength.symm ▸ h_fin_ib)
  obtain ⟨fullBytes, h_full, _⟩ := getBytesUnchecked_full_exists allocation storage
  have h_slice := getBytesUnchecked_eq_extract allocation range finish fullBytes h_full
    endpoint (Nat.le_of_lt h_lt_sf) h_fin_ib
  obtain ⟨updated, h_wu, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_im, h_pm, h_bytes⟩ :=
    writeUninit_step_bridge range ptrSize allocation mask nextProvenance fullBytes _
      h_full nonzero h_slice mutable maskOk (clear fullBytes h_full)
  exact ⟨updated, h_wu, h_bs, h_len, h_mut, h_al, h_ex, h_nb,
    h_im ▸ maskSize, h_im ▸ maskWF, h_im ▸ maskOk, h_pm, h_bytes⟩

private theorem size_mul_toNat (sz total : Size) (count : UInt64)
    (h_pos : 0 < count.toNat) (h_mul : Size.mul sz count = .ok total) :
    total.bytes.toNat = sz.bytes.toNat * count.toNat := by
  unfold Size.mul at h_mul
  have h_rc_nz : (count != 0) = true := bne_iff_ne.mpr (fun h0 => by subst h0; cases h_pos)
  by_cases h_ovf : (sz.bytes * count) / count != sz.bytes
  · simp only [h_rc_nz, Bool.true_and, h_ovf, ↓reduceIte] at h_mul; cases h_mul
  · simp only [h_rc_nz, Bool.true_and, h_ovf, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h_mul
    subst h_mul
    have h_div_eq : (sz.bytes * count) / count = sz.bytes := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_ovf; exact h_ovf
    have h_prod_lt : sz.bytes.toNat * count.toNat < 2 ^ 64 := by
      have h_le_u64 := (sz.bytes * count).toNat_lt
      have h_div_nat : ((sz.bytes * count) / count).toNat = (sz.bytes * count).toNat / count.toNat :=
        UInt64.toNat_div ..
      rw [h_div_eq] at h_div_nat
      have h_mul_le := Nat.mul_le_of_le_div count.toNat _ _ (Nat.le_of_eq h_div_nat)
      exact Nat.lt_of_le_of_lt (Nat.mul_comm _ _ ▸ h_mul_le) h_le_u64
    simp only [Size.ofBytes, UInt64.toNat_mul, Nat.mod_eq_of_lt h_prod_lt]

private theorem replicate_append_loop (srcBytes : Array UInt8) (k s : Nat) (acc : Array UInt8) :
    forIn (m := Id) (List.range' s k) acc (fun _ cur =>
      pure (ForInStep.yield (cur ++ srcBytes))) =
    acc ++ (List.replicate k srcBytes.toList).flatten.toArray := by
  induction k generalizing s acc with
  | zero =>
    simp only [List.range', List.forIn_nil, Pure.pure, List.replicate_zero, List.flatten_nil]
    exact (Array.append_empty (xs := acc)).symm
  | succ m ih =>
    rw [List.range'_succ, List.forIn_cons]
    change forIn (m := Id) (List.range' (s + 1) m) (acc ++ srcBytes)
      (fun _ cur => pure (ForInStep.yield (cur ++ srcBytes))) = _
    rw [ih (s + 1) (acc ++ srcBytes)]
    apply Array.ext
    · simp only [Array.size_append, List.size_toArray, List.replicate_succ, List.flatten_cons,
        List.length_append, Array.length_toList, Nat.add_assoc]
    · intro i _ _
      have h_toList : (acc ++ srcBytes ++ (List.replicate m srcBytes.toList).flatten.toArray).toList =
          (acc ++ (List.replicate (m + 1) srcBytes.toList).flatten.toArray).toList := by
        simp only [Array.toList_append, List.replicate_succ, List.flatten_cons, List.append_assoc]
      exact List.getElem_of_eq h_toList _

private theorem flatten_replicate_length (xs : List UInt8) (k : Nat) :
    (List.replicate k xs).flatten.length = k * xs.length := by
  induction k with
  | zero => simp only [List.replicate_zero, List.flatten_nil, List.length_nil, Nat.zero_mul]
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

/-- Partial-range specification of `Allocation.copyRepeatedly` when the source
range is nonempty and fully initialized and `repeatCount > 0`. Covers both
distinct allocations and same-allocation copies (requiring source/destination
disjointness over the full `totalSize` span when `sameAllocation = true` and
`nonoverlapping = true`), and yields pointwise initialization, disjoint
initialization/byte frames, provenance updates, and replicated destination
bytes. -/
theorem copyRepeatedly_initialized_spec
    (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart totalSize ptrSize : Size)
    (repeatCount : UInt64) (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (h_repPos : 0 < repeatCount.toNat)
    (h_mul : Size.mul sourceRange.size repeatCount = .ok totalSize)
    (h_repMode : repeatCount > 1 → nonoverlapping = true)
    (h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + totalSize.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : state.len = state.byteSize.bytes.toNat)
    (destMut : state.mutability = .Mut)
    (destMaskLen : state.initializationMask.len = state.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (destInBounds : destStart.bytes.toNat + totalSize.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart totalSize) stFull ptrSize =
        .ok () clearedProv)
    (h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) repeatCount = .ok () finalProv) :
    ∃ updated,
      Allocation.copyRepeatedly source sourceRange destStart repeatCount
        ptrSize sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart totalSize) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart totalSize) =
        .ok ((List.replicate repeatCount.toNat srcBytes.toList).flatten.toArray) ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange := by
  have h_src_pos : 0 < sourceRange.size.bytes.toNat :=
    Nat.pos_of_ne_zero (fun h0 => srcNonzero (UInt64.toNat_inj.mp h0))
  obtain ⟨_, h_srcFin_nat⟩ := endExclusive_fits sourceRange srcFinish srcEnd
  have h_src_lt : sourceRange.start.bytes.toNat < srcFinish.bytes.toNat :=
    h_srcFin_nat ▸ Nat.lt_add_of_pos_right h_src_pos
  obtain ⟨srcFull, h_srcFull, h_srcFull_sz⟩ := getBytesUnchecked_full_exists source srcStorage
  have h_srcBytes_sz : srcBytes.size = sourceRange.size.bytes.toNat := by
    have hs := getBytesUnchecked_eq_extract source sourceRange srcFinish srcFull h_srcFull srcEnd
      (Nat.le_of_lt h_src_lt) srcInBounds
    have heq : srcBytes = srcFull.extract sourceRange.start.bytes.toNat srcFinish.bytes.toNat :=
      Except.ok.inj (srcSlice.symm.trans hs)
    rw [heq, extract_size_of_le srcFull _ _ (h_srcFull_sz.symm ▸ srcInBounds), h_srcFin_nat, Nat.add_sub_cancel_left]
  have h_mul_nat : totalSize.bytes.toNat = sourceRange.size.bytes.toNat * repeatCount.toNat :=
    size_mul_toNat sourceRange.size totalSize repeatCount h_repPos h_mul
  have h_tot_pos : 0 < totalSize.bytes.toNat := h_mul_nat ▸ Nat.mul_pos h_src_pos h_repPos
  have h_tot_nz : (totalSize.bytes == 0) = false :=
    beq_false_of_ne (fun h0 => Nat.ne_of_gt h_tot_pos (congrArg UInt64.toNat h0))
  let destRange := allocRange destStart totalSize
  have h_dest_fits : destStart.bytes.toNat + totalSize.bytes.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt destInBounds state.byteSize.bytes.toNat_lt
  let destFinish := Size.ofBytes (destStart.bytes + totalSize.bytes)
  have destEnd : destRange.endExclusive = .ok destFinish := by
    unfold AllocRange.endExclusive AllocRange.end destRange allocRange
    exact congrArg (Except.mapError MemoryError.sizeError) (add_size_no_wrap destStart totalSize h_dest_fits)
  have h_destFin_nat : destFinish.bytes.toNat = destStart.bytes.toNat + totalSize.bytes.toNat := by
    simp only [destFinish, Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_dest_fits]
  have h_dest_lt : destRange.start.bytes.toNat < destFinish.bytes.toNat :=
    h_destFin_nat ▸ Nat.lt_add_of_pos_right h_tot_pos
  have h_destFin_ib : destFinish.bytes.toNat ≤ state.byteSize.bytes.toNat := h_destFin_nat ▸ destInBounds
  have h_src_unif := (InitMask.WriteProof.isRangeInitialized_nonempty_iff source.initializationMask
    sourceRange srcFinish srcMaskWF srcEnd h_src_lt (srcMaskLen.symm ▸ srcInBounds)).1.mp srcInit
  have h_prep_init : source.initializationMask.prepareCopy sourceRange =
      .ok ⟨true, #[sourceRange.size.bytes]⟩ :=
    InitMask.WriteProof.prepareCopy_of_uniform source.initializationMask
      sourceRange srcFinish true srcMaskWF srcEnd h_src_lt (srcMaskLen.symm ▸ srcInBounds) h_src_unif
  obtain ⟨mask1, mask1Ok, mask1Len, mask1WF⟩ :=
    InitMask.WriteProof.set_range_exists state.initializationMask destRange destFinish true
      destMaskWF destEnd h_dest_lt (destMaskLen.symm ▸ h_destFin_ib)
  obtain ⟨mask2, mask2Ok, mask2Len, mask2WF⟩ :=
    InitMask.WriteProof.set_range_exists mask1 destRange destFinish true
      mask1WF destEnd h_dest_lt (mask1Len.symm ▸ destMaskLen.symm ▸ h_destFin_ib)
  have h_apply_init : mask1.applyCopy ⟨true, #[sourceRange.size.bytes]⟩
      (allocRange destStart sourceRange.size) repeatCount = .ok mask2 := by
    rw [InitMask.WriteProof.applyCopy_singleton mask1 destStart sourceRange.size totalSize
      repeatCount true srcNonzero h_mul]
    exact mask2Ok
  have h_mask2_isInit : mask2.isRangeInitialized destRange = .ok (.ok ()) :=
    InitMask.WriteProof.isRangeInitialized_after_setRange_true mask1 mask2 destRange destFinish
      mask1WF destEnd h_dest_lt (mask1Len.symm ▸ destMaskLen.symm ▸ h_destFin_ib) mask2Ok
  obtain ⟨stFull, h_destFull, h_stFull_sz⟩ := getBytesUnchecked_full_exists state destStorage
  have h_destSlice := getBytesUnchecked_eq_extract state destRange destFinish stFull h_destFull
    destEnd (Nat.le_of_lt h_dest_lt) h_destFin_ib
  let copiedBytes := (List.replicate repeatCount.toNat srcBytes.toList).flatten.toArray
  have h_loop : forIn (m := Id) [:repeatCount.toNat] #[] (fun _ acc => pure (ForInStep.yield (acc ++ srcBytes))) = copiedBytes := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    have h_rng : List.range' [0:repeatCount.toNat].start [0:repeatCount.toNat].size [0:repeatCount.toNat].step =
        List.range' 0 repeatCount.toNat := by
      simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    rw [h_rng, replicate_append_loop srcBytes repeatCount.toNat 0 #[], Array.empty_append]
  have h_copied_sz : copiedBytes.size = destFinish.bytes.toNat - destStart.bytes.toNat := by
    rw [List.size_toArray, flatten_replicate_length, Array.length_toList, h_srcBytes_sz,
      Nat.mul_comm, ← h_mul_nat, h_destFin_nat, Nat.add_sub_cancel_left]
  have h_spliced_sz :
      (stFull.extract 0 destStart.bytes.toNat ++ copiedBytes ++
        stFull.extract destFinish.bytes.toNat stFull.size).size = state.byteSize.bytes.toNat := by
    rw [splice_size stFull copiedBytes destStart.bytes.toNat destFinish.bytes.toNat
      (Nat.le_of_lt h_dest_lt) (h_stFull_sz.symm ▸ h_destFin_ib) h_copied_sz, h_stFull_sz]
  have h_repChk : (repeatCount > 1 && !nonoverlapping) = false := by
    by_cases h_gt1 : repeatCount > 1
    · rw [decide_eq_true h_gt1, h_repMode h_gt1]; rfl
    · rw [decide_eq_false h_gt1]; rfl
  have h_rcNz : (repeatCount == 0) = false :=
    beq_false_of_ne (fun h0 => Nat.ne_of_gt h_repPos (congrArg UInt64.toNat h0))
  have h_noOvl : sameAllocation = true → nonoverlapping = true →
      ¬((sourceRange.start.bytes ≤ destStart.bytes ∧ destStart.bytes < srcFinish.bytes) ∨
        (destStart.bytes ≤ sourceRange.start.bytes ∧ sourceRange.start.bytes < destFinish.bytes)) := by
    intro h1 h2
    have hd := h_disjSame h1 h2
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, h_destFin_nat]
    omega
  obtain ⟨updated, h_cp, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_im, h_pm, h_upd_full⟩ :=
    copyRepeatedly_step_bridge source state sourceRange srcFinish destStart totalSize destFinish ptrSize
      repeatCount sameAllocation nonoverlapping srcFull stFull srcBytes _ copiedBytes
      ⟨true, #[sourceRange.size.bytes]⟩ provCopy mask1 mask2 clearedProv finalProv
      h_srcFull srcSlice h_mul h_destFull h_destSlice (h_prepProv srcFull h_srcFull) h_prep_init
      h_tot_nz destMut mask1Ok (h_clearProv stFull h_destFull) srcEnd destEnd h_noOvl h_repChk
      rfl h_rcNz h_loop h_spliced_sz h_apply_init h_applyProv
  have h_mask_get_frame : ∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
      mask2.get idx =
        if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
            idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat then
          .ok true
        else
          state.initializationMask.get idx := by
    intro idx h_idx_lt
    have h_g2 := InitMask.WriteProof.set_range_get mask1 mask2 destRange destFinish idx true
      mask1WF destEnd h_dest_lt (mask1Len.symm ▸ destMaskLen.symm ▸ h_destFin_ib)
      (mask1Len.symm ▸ destMaskLen.symm ▸ h_idx_lt) mask2Ok
    have h_g1 := InitMask.WriteProof.set_range_get state.initializationMask mask1
      destRange destFinish idx true destMaskWF destEnd h_dest_lt
      (destMaskLen.symm ▸ h_destFin_ib) (destMaskLen.symm ▸ h_idx_lt) mask1Ok
    have h_dr_start : destRange.start = destStart := rfl
    rw [h_dr_start, h_destFin_nat] at h_g2 h_g1
    by_cases h_in : destStart.bytes.toNat ≤ idx.bytes.toNat ∧
        idx.bytes.toNat < destStart.bytes.toNat + totalSize.bytes.toNat
    · rw [ite_eq_left h_in] at h_g2 ⊢; exact h_g2
    · rw [ite_eq_right h_in] at h_g2 h_g1 ⊢; exact h_g2.trans h_g1
  have h_mask_range_frame : ∀ (qRange : AllocRange) (qFin : Size),
      qRange.endExclusive = .ok qFin →
      qRange.start.bytes.toNat < qFin.bytes.toNat →
      qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
      (destStart.bytes.toNat + totalSize.bytes.toNat ≤ qRange.start.bytes.toNat ∨
        qFin.bytes.toNat ≤ destStart.bytes.toNat) →
      (mask2.isRangeInitialized qRange = .ok (.ok ()) ↔
        state.initializationMask.isRangeInitialized qRange = .ok (.ok ())) := by
    intro qRange qFin h_qend h_qne h_qib h_disj
    have h_disj' : destFinish.bytes.toNat ≤ qRange.start.bytes.toNat ∨
        qFin.bytes.toNat ≤ destRange.start.bytes.toNat := h_destFin_nat.symm ▸ h_disj
    exact (InitMask.WriteProof.isRangeInitialized_frame mask1 mask2 destRange qRange
      destFinish qFin true mask1WF destEnd h_qend h_dest_lt h_qne
      (mask1Len.symm ▸ destMaskLen.symm ▸ h_destFin_ib)
      (mask1Len.symm ▸ destMaskLen.symm ▸ h_qib) h_disj' mask2Ok).trans
      (InitMask.WriteProof.isRangeInitialized_frame state.initializationMask mask1 destRange qRange
        destFinish qFin true destMaskWF destEnd h_qend h_dest_lt h_qne
        (destMaskLen.symm ▸ h_destFin_ib) (destMaskLen.symm ▸ h_qib) h_disj' mask1Ok)
  refine ⟨updated, h_cp, h_bs, h_len, h_mut, h_al, h_ex, h_nb,
    h_im ▸ mask2Len.trans mask1Len, h_im ▸ mask2WF, h_im ▸ h_mask2_isInit,
    h_im ▸ h_mask_get_frame, h_im ▸ h_mask_range_frame, h_pm, ?_, ?_⟩
  · rw [getBytesUnchecked_eq_extract updated destRange destFinish _ h_upd_full destEnd
      (Nat.le_of_lt h_dest_lt) (h_bs.symm ▸ h_destFin_ib)]
    exact congrArg Except.ok (splice_extract_exact stFull copiedBytes _ _
      (Nat.le_of_lt h_dest_lt) (h_stFull_sz.symm ▸ h_destFin_ib) h_copied_sz)
  · intro qRange qFin h_qend h_qlo h_qib h_disj
    rw [getBytesUnchecked_eq_extract updated qRange qFin _ h_upd_full h_qend h_qlo (h_bs.symm ▸ h_qib),
      getBytesUnchecked_eq_extract state qRange qFin stFull h_destFull h_qend h_qlo h_qib]
    exact congrArg Except.ok (splice_extract_disjoint stFull copiedBytes destStart.bytes.toNat
      destFinish.bytes.toNat qRange.start.bytes.toNat qFin.bytes.toNat
      (Nat.le_of_lt h_dest_lt) (h_stFull_sz.symm ▸ h_destFin_ib) h_qlo (h_stFull_sz.symm ▸ h_qib)
      h_copied_sz (h_destFin_nat.symm ▸ h_disj))

/-- One-copy specialization (`repeatCount = 1`) of
`copyRepeatedly_initialized_spec` for `Allocation.copy`. -/
theorem copy_initialized_spec
    (source state : Allocation P E)
    (sourceRange : AllocRange) (srcFinish destStart ptrSize : Size)
    (sameAllocation nonoverlapping : Bool)
    (srcBytes : Array UInt8) (provCopy : ProvenanceCopy P)
    (clearedProv finalProv : ProvenanceMap P)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok srcFinish)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok srcBytes)
    (srcInBounds : srcFinish.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (h_prepProv : ∀ srcFull : Array UInt8,
      source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok srcFull →
      source.provenanceMap.prepareCopy sourceRange srcFull ptrSize = .ok provCopy)
    (h_disjSame : sameAllocation = true → nonoverlapping = true →
      srcFinish.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : state.len = state.byteSize.bytes.toNat)
    (destMut : state.mutability = .Mut)
    (destMaskLen : state.initializationMask.len = state.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed state.initializationMask)
    (destInBounds : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ state.byteSize.bytes.toNat)
    (h_clearProv : ∀ stFull : Array UInt8,
      state.getBytesUnchecked (allocRange Size.ZERO state.byteSize) = .ok stFull →
      state.provenanceMap.clear (allocRange destStart sourceRange.size) stFull ptrSize =
        .ok () clearedProv)
    (h_applyProv : clearedProv.applyCopy provCopy
      (allocRange destStart sourceRange.size) 1 = .ok () finalProv) :
    ∃ updated,
      Allocation.copy source sourceRange destStart ptrSize
        sameAllocation nonoverlapping state = .ok () updated ∧
      updated.byteSize = state.byteSize ∧
      updated.len = state.len ∧
      updated.mutability = state.mutability ∧
      updated.align = state.align ∧
      updated.extra = state.extra ∧
      updated.nativeBuffer = state.nativeBuffer ∧
      updated.initializationMask.len = state.initializationMask.len ∧
      InitMask.WriteProof.WellFormed updated.initializationMask ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart sourceRange.size) = .ok (.ok ()) ∧
      (∀ (idx : Size), idx.bytes.toNat < state.byteSize.bytes.toNat →
        updated.initializationMask.get idx =
          if destStart.bytes.toNat ≤ idx.bytes.toNat ∧
              idx.bytes.toNat < destStart.bytes.toNat + sourceRange.size.bytes.toNat then
            .ok true
          else
            state.initializationMask.get idx) ∧
      (∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat < qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        (updated.initializationMask.isRangeInitialized qRange = .ok (.ok ()) ↔
          state.initializationMask.isRangeInitialized qRange = .ok (.ok ()))) ∧
      updated.provenanceMap = finalProv ∧
      updated.getBytesUnchecked (allocRange destStart sourceRange.size) = .ok srcBytes ∧
      ∀ (qRange : AllocRange) (qFin : Size),
        qRange.endExclusive = .ok qFin →
        qRange.start.bytes.toNat ≤ qFin.bytes.toNat →
        qFin.bytes.toNat ≤ state.byteSize.bytes.toNat →
        (destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ qRange.start.bytes.toNat ∨
          qFin.bytes.toNat ≤ destStart.bytes.toNat) →
        updated.getBytesUnchecked qRange = state.getBytesUnchecked qRange := by
  have h_mul1 : Size.mul sourceRange.size 1 = .ok sourceRange.size := by
    cases sourceRange.size
    unfold Size.mul
    simp only [UInt64.mul_one, UInt64.div_one, bne_self_eq_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Size.ofBytes]
  obtain ⟨updated, h_ok, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_ml, h_mwf,
      h_isInit, h_mget, h_mframe, h_prov, h_bytes, h_frame⟩ :=
    copyRepeatedly_initialized_spec source state sourceRange srcFinish destStart sourceRange.size ptrSize
      1 sameAllocation nonoverlapping srcBytes provCopy clearedProv finalProv
      srcStorage srcEnd srcNonzero srcMaskLen srcMaskWF srcInit srcSlice srcInBounds h_prepProv
      (by decide) h_mul1 (fun h => absurd h (by decide)) h_disjSame
      destStorage destMut destMaskLen destMaskWF destInBounds h_clearProv h_applyProv
  have h_flat1 : (List.replicate (1 : UInt64).toNat srcBytes.toList).flatten.toArray = srcBytes := by
    have h1 : (1 : UInt64).toNat = 1 := rfl
    simp only [h1, List.replicate_one, List.flatten_cons, List.flatten_nil, List.append_nil,
      Array.toArray_toList]
  rw [h_flat1] at h_bytes
  exact ⟨updated, h_ok, h_bs, h_len, h_mut, h_al, h_ex, h_nb, h_ml, h_mwf,
    h_isInit, h_mget, h_mframe, h_prov, h_bytes, h_frame⟩

end Miri.Memory.Allocation

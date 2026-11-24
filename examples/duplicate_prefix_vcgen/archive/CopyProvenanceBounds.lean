import duplicate_prefix.InitMaskCopy
import duplicate_prefix.S04ReturnProvenanceClear
import duplicate_prefix.CopySortMembership

namespace DuplicatePrefix.CopyProvenanceBounds

open Miri.ABI Miri.Memory ProvenanceCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- All complete pointer encodings in the production provenance snapshot
fit their originating byte range. Partial encodings are copied as fragments. -/
theorem preparedPointers (self : ProvenanceMap P) (range : AllocRange) (finish : Size)
    (data : Array UInt8) (snapshot : ProvenanceCopy P)
    (endpoint : range.endExclusive = .ok finish)
    (finishNat : finish.bytes.toNat = range.start.bytes.toNat+range.size.bytes.toNat)
    (prepared : self.prepareCopy range data (Size.ofBytes 8) = .ok snapshot) :
    ∀ entry ∈ snapshot.ptrs, entry.1.bytes.toNat+8 ≤ range.size.bytes.toNat := by
  have pointers : snapshot.ptrs = shift_entries range.start
      (whole_entries self range.start finish range.size.bytes) := by
    rw [prepare_stages_exact] at prepared
    unfold prepare_stages at prepared
    simp only [endpoint,Except.mapError,Bind.bind,Except.bind] at prepared
    rw [whole_stage_exact self range.start finish range.size.bytes finishNat] at prepared
    simp only [Bind.bind,Except.bind] at prepared
    cases beg : self.rangePtrs (allocRange range.start Size.ZERO) (Size.ofBytes 8) with
    | error error => simp [beg] at prepared
    | ok first =>
      simp only [beg] at prepared
      cases en : self.rangePtrs (allocRange finish Size.ZERO) (Size.ofBytes 8) with
      | error error => simp [en] at prepared
      | ok last =>
        simp only [en] at prepared
        split at prepared
        · cases a : begin_stage range.start finish first[0]? data with
          | error error => simp [a] at prepared
          | ok initial =>
            simp only [a] at prepared
            cases b : self.rangeBytes range with
            | error error => simp [b] at prepared
            | ok old =>
              simp only [b] at prepared
              cases c : collect_entries range.start old initial with
              | error error => simp [c] at prepared
              | ok middle =>
                simp only [c] at prepared
                cases d : end_stage range.start finish first[0]? last[0]? data middle with
                | error error => simp [d] at prepared
                | ok bytes =>
                  simp only [d,Pure.pure,Except.pure] at prepared
                  cases prepared
                  rfl
        · simp only [Pure.pure,Except.pure] at prepared
          cases prepared
          rfl
  rw [pointers]
  intro entry member
  obtain ⟨before, original, rfl⟩ := Array.mem_map.mp member
  unfold whole_entries at original
  split at original
  · rename_i large
    obtain ⟨_, lower, upper⟩ := by simpa only [Array.mem_filter, Bool.and_eq_true, decide_eq_true_eq] using original
    rw [shift_nat range.start before lower]
    have enough : (7 : UInt64) ≤ finish.bytes := by
      have eight := UInt64.le_iff_toNat_le.mp large
      change 8 ≤ range.size.bytes.toNat at eight
      exact UInt64.le_iff_toNat_le.mpr (by change 7 ≤ finish.bytes.toNat; omega)
    have stop := UInt64.lt_iff_toNat_lt.mp upper
    rw [UInt64.toNat_sub_of_le _ _ enough] at stop
    change before.1.bytes.toNat < finish.bytes.toNat-7 at stop
    have start := UInt64.le_iff_toNat_le.mp lower
    omega
  · simp at original

def PointerBounds (capacity : Nat) (state : ProvenanceMap P) : Prop :=
  ∀ entry ∈ state.ptrs, entry.1.bytes.toNat + 8 ≤ capacity

/-- Backing invariants needed by a later physical scalar store. -/
structure AllocationBacking (allocation : Allocation P E) : Prop where
  mutable : allocation.mutability = .Mut
  mask : InitMaskCopy.WellFormed allocation.initializationMask
  maskLength : allocation.initializationMask.len = allocation.byteSize
  pointers : PointerBounds allocation.len allocation.provenanceMap

private theorem wholeStep (range : AllocRange) (row : Size × P) (capacity : Nat)
    (fit : row.1.bytes.toNat+range.start.bytes.toNat+8 ≤ capacity) (small : capacity < 2^64)
    (before after : ProvenanceMap P) (bounds : PointerBounds capacity before)
    (equation : insert_whole_action range row before = .ok () after) : PointerBounds capacity after := by
  have fits : row.1.bytes.toNat+range.start.bytes.toNat < 2^64 := by omega
  unfold insert_whole_action at equation
  rw [shifted_copy_zero range row.1 fits] at equation
  unfold checkedResult at equation
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at equation
  simp only [Bind.bind,EStateM.bind,EStateM.get,EStateM.set] at equation
  cases equation
  intro entry member
  change entry ∈ insertEntry before.ptrs (Size.ofBytes (row.1.bytes+range.start.bytes)) row.2 at member
  unfold insertEntry at member
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.insertEntry" at member
  have inserted := CopySortMembership.subset _ _ _ member
  rcases Array.mem_push.mp inserted with old | same
  · exact bounds entry (Array.mem_filter.mp old).1
  · subst entry
    change (row.1.bytes+range.start.bytes).toNat+8 ≤ capacity
    simpa only [UInt64.toNat_add,Nat.mod_eq_of_lt fits] using fit

private theorem fragmentStep (range : AllocRange) (row : Size × PointerFrag P) (capacity : Nat)
    (before after : ProvenanceMap P) (bounds : PointerBounds capacity before)
    (equation : insert_fragment_action range row before = .ok () after) : PointerBounds capacity after := by
  unfold insert_fragment_action checkedResult at equation
  unfold_provenance_at ".Miri.Memory.ProvenanceMap.checked" at equation
  cases shift : shiftedCopyOffset range 0 row.1 <;>
    simp only [shift,Bind.bind,EStateM.bind,EStateM.get,EStateM.set] at equation
  · cases equation
  · cases equation
    exact bounds

private theorem loop (action : α → ProvenanceMap.Mutation P Unit) (capacity : Nat)
    (rows : List α) (before after : ProvenanceMap P)
    (step : ∀ row ∈ rows, ∀ prior next, PointerBounds capacity prior →
      action row prior = .ok () next → PointerBounds capacity next)
    (initial : PointerBounds capacity before)
    (equation : (forIn rows PUnit.unit (fun row _ => do
      action row
      pure (.yield PUnit.unit)) : ProvenanceMap.Mutation P PUnit) before = .ok PUnit.unit after) :
    PointerBounds capacity after := by
  induction rows generalizing before with
  | nil =>
    simp [List.forIn_nil,Pure.pure,EStateM.pure] at equation
    cases equation
    exact initial
  | cons row rest ih =>
    rw [List.forIn_cons] at equation
    cases ran : action row before with
    | error error state =>
      simp [Bind.bind,EStateM.bind,ran] at equation
    | ok value state =>
      cases value
      simp only [Bind.bind,EStateM.bind,ran,Pure.pure,EStateM.pure] at equation
      exact ih state (fun next mem => step next (List.mem_cons_of_mem _ mem))
        (step row (List.mem_cons_self) before state initial ran) equation

private theorem fromUnit (act : ProvenanceMap.Mutation P PUnit) (before after : ProvenanceMap P)
    (ran : (EStateM.bind act (fun _ => EStateM.pure ())) before = .ok () after) :
    act before = .ok PUnit.unit after := by
  simp only [EStateM.bind] at ran
  cases run : act before with
  | error error state => simp [run] at ran
  | ok token state =>
    cases token
    simp only [run,EStateM.pure] at ran
    cases ran
    rfl

theorem applyOnce (copy : ProvenanceCopy P) (range : AllocRange) (capacity : Nat)
    (small : capacity < 2^64)
    (pointerCountFits : copy.ptrs.size < 2^64)
    (fragmentCountFits : copy.byteFragments.size < 2^64)
    (geometry : ∀ entry ∈ copy.ptrs, entry.1.bytes.toNat+range.start.bytes.toNat+8 ≤ capacity)
    (before after : ProvenanceMap P) (initial : PointerBounds capacity before)
    (equation : ProvenanceMap.applyCopy copy range 1 before = .ok () after) :
    PointerBounds capacity after := by
  have whole (old new : ProvenanceMap P) (bounds : PointerBounds capacity old)
      (ok : whole_loop range copy.ptrs old = .ok () new) : PointerBounds capacity new := by
    unfold whole_loop at ok
    simp only [Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] at ok
    have retained := fromUnit (forIn copy.ptrs PUnit.unit (fun row _ =>
      EStateM.bind (insert_whole_action range row) (fun _ => EStateM.pure (.yield PUnit.unit)))) old new ok
    refine loop (insert_whole_action range) capacity copy.ptrs.toList old new ?_ bounds ?_
    · intro row member
      exact wholeStep range row capacity (geometry row (by simpa using member)) small
    · simpa only [Array.forIn_toList,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] using retained
  have fragments (old new : ProvenanceMap P) (bounds : PointerBounds capacity old)
      (ok : fragment_loop range copy.byteFragments old = .ok () new) : PointerBounds capacity new := by
    unfold fragment_loop at ok
    simp only [Bind.bind,EStateM.bind,EStateM.get,EStateM.set,Pure.pure,EStateM.pure] at ok
    let materialized := mkMap old.ptrs (some (old.byteFragments.getD #[]))
    have retained := fromUnit (forIn copy.byteFragments PUnit.unit (fun row _ =>
      EStateM.bind (insert_fragment_action range row) (fun _ => EStateM.pure (.yield PUnit.unit)))) materialized new ok
    refine loop (insert_fragment_action range) capacity copy.byteFragments.toList materialized new ?_ bounds ?_
    · intro row _
      exact fragmentStep range row capacity
    · simpa only [Array.forIn_toList,Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] using retained
  rw [apply_copy_once_reduces copy range pointerCountFits fragmentCountFits] at equation
  unfold apply_once at equation
  by_cases noPtr : copy.ptrs.isEmpty = true <;> by_cases noFrag : copy.byteFragments.isEmpty = true <;>
    simp only [noPtr,noFrag,Bool.not_true,Bool.not_false,Bool.false_eq_true,↓reduceIte,
      Bind.bind,EStateM.bind,Pure.pure,EStateM.pure] at equation
  · cases equation
    exact initial
  · exact fragments before after initial equation
  · cases run : whole_loop range copy.ptrs before with
    | error error state => simp [run] at equation
    | ok result state =>
      cases result
      rw [run] at equation
      cases equation
      exact whole before after initial run
  · cases run : whole_loop range copy.ptrs before with
    | error error state => simp [run] at equation
    | ok result state =>
      cases result
      rw [run] at equation
      exact fragments state after (whole before state initial run) equation

/-- The actual copy's clear and apply stages retain pointer bounds after
relocation into an adjacent in-bounds interval. -/
theorem interval (initial cleared updated : ProvenanceMap P) (base : Size) (count : UInt64)
    (data : Array UInt8) (valid : WellFormed initial data.size)
    (small : data.size+16 < 2^64)
    (fits : base.bytes.toNat+count.toNat+count.toNat ≤ data.size)
    (snapshot : ProvenanceCopy P)
    (prepared : initial.prepareCopy (allocRange base (Size.ofBytes count)) data (Size.ofBytes 8) = .ok snapshot)
    (removed : ProvenanceMap.clear (allocRange (Size.ofBytes (base.bytes+count)) (Size.ofBytes count))
      data (Size.ofBytes 8) initial = .ok () cleared)
    (applied : ProvenanceMap.applyCopy snapshot (allocRange (Size.ofBytes (base.bytes+count)) (Size.ofBytes count))
      1 cleared = .ok () updated) :
    PointerBounds data.size updated := by
  let middle := Size.ofBytes (base.bytes+count)
  have firstFits : base.bytes.toNat+count.toNat < 2^64 := by omega
  have middleNat : middle.bytes.toNat = base.bytes.toNat+count.toNat := by
    change (base.bytes+count).toNat = _
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt firstFits]
  have endFits : middle.bytes.toNat+count.toNat < 2^64 := by omega
  have first := DuplicatePrefix.source_end base count firstFits
  have second := DuplicatePrefix.source_end middle count endFits
  obtain ⟨same,ready,_,_,ptrs,fragments⟩ :=
    prepare_interval_with_bounds initial base middle count data valid (by omega) first middleNat
  have equal : same = snapshot := Except.ok.inj (ready.symm.trans prepared)
  subst same
  have maxPtr := WellFormed.pointer_count valid
  have maxFrag := WellFormed.fragment_count valid
  have whole := preparedPointers initial (allocRange base (Size.ofBytes count)) middle data snapshot first middleNat prepared
  have survive := S04ReturnProvenanceClear.clear_pointer_subset initial cleared _ _ data second removed
  apply applyOnce snapshot (allocRange middle (Size.ofBytes count)) data.size (by omega) (by omega) (by omega) _ cleared updated _ applied
  · intro row mem
    have bound := whole row mem
    change row.1.bytes.toNat+8 ≤ count.toNat at bound
    change row.1.bytes.toNat+middle.bytes.toNat+8 ≤ data.size
    omega
  · exact fun row mem => WellFormed.pointerBounds valid row (survive row mem)

#print axioms interval
#print axioms preparedPointers
#print axioms applyOnce
end DuplicatePrefix.CopyProvenanceBounds

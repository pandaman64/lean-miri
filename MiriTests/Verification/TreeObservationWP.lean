import Miri.Verification.TreeObservationWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeObservationWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open Miri.Verification Miri.Verification.TreeObservationWP

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def child : BorTag := ⟨2, by decide⟩
private def root := BorrowTree.new BorTag.one (Size.ofBytes 3)
private def tree :=
  (root.newChild Size.ZERO (.concrete BorTag.one) child
    (DedupRangeMap.new (Size.ofBytes 3) ⟨.Unique, true, .None⟩) (.ReservedFrz false) false).tree

private def read : Access := ⟨.concrete BorTag.one, Size.ZERO, Size.ofBytes 1, {}, .VisitChildrenOfAccessed⟩
private def write : Access := ⟨.concrete BorTag.one, Size.ofBytes 1, Size.ofBytes 1, {}, .VisitChildrenOfAccessed⟩
private def observe : Access := ⟨.concrete child, Size.ofBytes 2, Size.ofBytes 1, {}, .VisitChildrenOfAccessed⟩
private def rejected := { observe with offset := Size.ofBytes 1 }

private def permission (loc : LocationTree) := (loc.perms.get ⟨1⟩).map (·.permission)

private def frozenAtZero (locations : ByteLocations) : Prop :=
  ∃ loc, locations 0 loc ∧ permission loc = some .Frozen

private def plan : List PlannedAccess :=
  [⟨read, .Read, Size.ofBytes 1⟩, ⟨write, .Write, Size.ofBytes 2⟩, ⟨observe, .Read, Size.ofBytes 3⟩]

private def initial : LocationTree := (tree.locations.entries[0]?.map (·.data)).getD {}
private theorem entries : tree.locations.entries = #[⟨⟨0, 3⟩, initial⟩] := by cbv
private theorem formed : tree.locations.WellFormed := by
  change (⟨tree.locations.entries⟩ : DedupRangeMap LocationTree).WellFormed
  rw [entries]
  exact DedupRangeMap.new_wellFormed (Size.ofBytes 3) initial

private theorem endpoints (access : PlannedAccess) (member : access ∈ plan) :
    access.offset.add access.length = .ok access.finish := by
  simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cbv

private theorem bounds (access : PlannedAccess) (member : access ∈ plan) :
    access.finish.bytes ≤ tree.locations.size.bytes := by
  simp only [plan, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cbv

/-- The third read uses the untouched byte. The earlier read froze the child
at byte zero and the earlier write disabled it at byte one. -/
theorem disjoint_success :
    wp (readWriteObserve read write observe .Read)
      (fun traces after =>
        traces.2.map (·.range) = #[⟨2, 3⟩] ∧
        (after.locations.entries.map fun segment => permission segment.data) =
          #[some .Frozen, some .Disabled, some .Unique]) (fun _ _ => False) tree := by
  miri_tree_range_wp observe
  cbv

/-- Reading through the child at the byte just written by its parent fails
with the third access's trace and with the earlier changes still committed. -/
theorem overlap_rejected :
    wp (readWriteObserve read write rejected .Read) (fun _ _ => False)
      (fun (status, trace) after =>
        status = .AccessFailure ⟨1, 2⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)) ∧
        trace.map (·.range) = #[⟨1, 2⟩] ∧
        (after.locations.entries.map fun segment => permission segment.data) =
          #[some .Frozen, some .Disabled, some .Unique]) tree := by
  miri_tree_range_wp observe
  cbv

private theorem initial_at {byte : UInt64} {loc : LocationTree}
    (found : tree.locations.MapAt byte loc) : loc = initial := by
  obtain ⟨position, segment, entry, _, value⟩ := found
  rw [entries] at entry
  have inside := (Array.getElem?_eq_some_iff.mp entry).choose
  have same : position = 0 := by simp at inside; omega
  subst position
  simp at entry
  subst segment
  exact value.symm

open Miri.Verification.TreeOverlapWP in
/-- The folded rule proves the final observation from initial bytes and three
local permission checks. The write and third read use different bytes. -/
theorem initial_byte_observed :
    wp (runPlan plan) (fun _ after => frozenAtZero after.locations.MapAt) (fun _ _ => False) tree := by
  have wellFormed := formed
  have checked := endpoints
  have inRange := bounds
  simp (disch := assumption) only [miri_initial_wp]
  simp only [plan, planBytePre, byteChecks, Access.observeBytes]
  refine ⟨⟨by cbv, ?_⟩, ⟨by cbv, ?_⟩, ⟨by cbv, ?_⟩, ?_⟩
  · intro byte loc found _
    rw [initial_at found]
    cbv
  · rintro byte loc ⟨before, found, _, unchanged⟩ writes
    have outside (reads : ByteRange.Contains ⟨0, 1⟩ byte) : False :=
      UInt64.not_lt.mpr writes.1 reads.2
    rw [← unchanged outside, initial_at found]
    cbv
  · rintro byte loc ⟨afterRead, ⟨before, found, _, stillInitial⟩, _, stillRead⟩ observes
    have outsideRead (reads : ByteRange.Contains ⟨0, 1⟩ byte) : False :=
      UInt64.not_lt.mpr (UInt64.le_trans (by decide : (1 : UInt64) ≤ 2) observes.1) reads.2
    have outsideWrite (writes : ByteRange.Contains ⟨1, 2⟩ byte) : False :=
      UInt64.not_lt.mpr observes.1 writes.2
    rw [← stillRead outsideWrite, ← stillInitial outsideRead, initial_at found]
    cbv
  · have startsAtZero : tree.locations.MapAt 0 initial :=
      ⟨0, ⟨⟨0, 3⟩, initial⟩, by rw [entries]; rfl, by cbv, rfl⟩
    have insideRead : ByteRange.Contains ⟨0, 1⟩ 0 := by cbv
    have outsideWrite : ¬ ByteRange.Contains ⟨1, 2⟩ 0 := by cbv
    have outsideObserve : ¬ ByteRange.Contains ⟨2, 3⟩ 0 := by cbv
    refine ⟨_, ⟨_, ⟨_, ⟨initial, startsAtZero, fun _ => rfl, fun outside => (outside insideRead).elim⟩,
      fun inside => (outsideWrite inside).elim, fun _ => rfl⟩,
      fun inside => (outsideObserve inside).elim, fun _ => rfl⟩, ?_⟩
    cbv

/-- Ordinary do notation needs no hand-written plan or trace-packaging action. -/
theorem ordinary_access_sequence :
    wp (do
      let _ ← TreeBorrowsWP.access read.provenance read.offset read.length .Read read.tags read.mode
      let _ ← TreeBorrowsWP.access write.provenance write.offset write.length .Write write.tags write.mode
      TreeBorrowsWP.access observe.provenance observe.offset observe.length .Read observe.tags observe.mode)
      (fun _ after => frozenAtZero after.locations.MapAt) (fun _ _ => False) tree := by
  have wellFormed := formed
  have readEnd : read.offset.add read.length = .ok (Size.ofBytes 1) := by cbv
  have writeEnd : write.offset.add write.length = .ok (Size.ofBytes 2) := by cbv
  have observeEnd : observe.offset.add observe.length = .ok (Size.ofBytes 3) := by cbv
  have readBound : (Size.ofBytes 1).bytes ≤ tree.locations.size.bytes := by cbv
  have writeBound : (Size.ofBytes 2).bytes ≤ tree.locations.size.bytes := by cbv
  have observeBound : (Size.ofBytes 3).bytes ≤ tree.locations.size.bytes := by cbv
  miri_tree_range_wp observe
  exact (wp_plan_bytes_iff tree plan formed endpoints bounds frozenAtZero).mp initial_byte_observed

/-- Generated nested access continuations use the same initial byte predicate. -/
theorem nested_access_sequence :
    TreeBorrowsWP.accessPre tree read.provenance read.offset read.length .Read read.tags read.mode
      (fun afterRead _ =>
        TreeBorrowsWP.accessPre afterRead write.provenance write.offset write.length .Write write.tags write.mode
          (fun afterWrite _ =>
            TreeBorrowsWP.accessPre afterWrite observe.provenance observe.offset observe.length .Read observe.tags
              observe.mode (fun after _ => frozenAtZero after.locations.MapAt) (fun _ _ _ => False))
          (fun _ _ _ => False)) (fun _ _ _ => False) := by
  have wellFormed := formed
  have readEnd : read.offset.add read.length = .ok (Size.ofBytes 1) := by cbv
  have writeEnd : write.offset.add write.length = .ok (Size.ofBytes 2) := by cbv
  have observeEnd : observe.offset.add observe.length = .ok (Size.ofBytes 3) := by cbv
  have readBound : (Size.ofBytes 1).bytes ≤ tree.locations.size.bytes := by cbv
  have writeBound : (Size.ofBytes 2).bytes ≤ tree.locations.size.bytes := by cbv
  have observeBound : (Size.ofBytes 3).bytes ≤ tree.locations.size.bytes := by cbv
  simp (disch := assumption) only [miri_initial_wp]
  exact (wp_plan_bytes_iff tree plan formed endpoints bounds frozenAtZero).mp initial_byte_observed

open Miri.Verification.TreeOverlapWP in
/-- The registered one-access rule can also prove an observation without
building a one-entry plan or reconstructing the successor partition. -/
theorem single_byte_observed :
    TreeBorrowsWP.accessPre tree read.provenance read.offset read.length .Read read.tags read.mode
      (fun after _ => frozenAtZero after.locations.MapAt) (fun _ _ _ => False) := by
  have wellFormed := formed
  have checked : read.offset.add read.length = .ok (Size.ofBytes 1) := by cbv
  have inRange : (Size.ofBytes 1).bytes ≤ tree.locations.size.bytes := by cbv
  simp (disch := assumption) only [miri_initial_wp]
  unfold byteChecks
  refine ⟨⟨by cbv, ?_⟩, ?_⟩
  · intro byte loc found _
    rw [initial_at found]
    cbv
  · have startsAtZero : tree.locations.MapAt 0 initial :=
      ⟨0, ⟨⟨0, 3⟩, initial⟩, by rw [entries]; rfl, by cbv, rfl⟩
    have covered : ByteRange.Contains ⟨0, 1⟩ 0 := by cbv
    exact ⟨_, ⟨initial, startsAtZero, fun _ => rfl, fun outside => (outside covered).elim⟩, by cbv⟩

#print axioms disjoint_success
#print axioms overlap_rejected
#print axioms initial_byte_observed
#print axioms single_byte_observed
#print axioms ordinary_access_sequence
#print axioms nested_access_sequence
#print axioms wp_readWriteObserve_bytes_iff

end MiriTests.Verification.TreeObservationWP

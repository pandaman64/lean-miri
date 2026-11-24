import Miri.Verification.TreeOverlapWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeOverlapWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open Miri.Verification.TreeBorrowsWP Miri.Verification.TreeOverlapWP Miri.Verification.TreeRangeOutcomeWP

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def initial := BorrowTree.new BorTag.one (Size.ofBytes 6)
private def root : ProvenanceExtra := .concrete BorTag.one
private abbrev visit := Tree.ChildrenVisitMode.VisitChildrenOfAccessed
private def readOffset := Size.ofBytes 1
private def readLength := Size.ofBytes 3
private def readRange : ByteRange := ⟨1, 4⟩
private def overlapOffset := Size.ofBytes 2
private def overlapLength := Size.ofBytes 4
private def overlapRange : ByteRange := ⟨2, 6⟩
private def separateOffset := Size.ofBytes 4
private def separateLength := Size.ofBytes 2
private def separateRange : ByteRange := ⟨4, 6⟩

private def rootLocation : LocationTree :=
  { perms := ({} : UniValMap Tree.LocationState).insert ⟨0⟩ ⟨Permission.newUnique, true, .None⟩ }

private theorem initialLocation {byte : UInt64} {location : LocationTree}
    (member : initial.locations.MapAt byte location) : location = rootLocation := by
  obtain ⟨position, segment, entry, _, value⟩ := member
  have entries : initial.locations.entries = #[⟨⟨0, 6⟩, rootLocation⟩] := by cbv
  rw [entries] at entry
  have inside := (Array.getElem?_eq_some_iff.mp entry).choose
  have same : position = 0 := by simp at inside; omega
  subst position
  simp at entry
  subst segment
  exact value.symm

private theorem readRoot :
    localPre initial rootLocation root .Read {} visit (fun _ => True) := by cbv

private theorem writeRoot :
    localPre initial rootLocation root .Write {} visit (fun _ => True) := by cbv

private theorem readThenWriteRoot :
    localPre initial rootLocation root .Read {} visit
      (fun retained => localPre initial retained root .Write {} visit (fun _ => True)) := by cbv

private theorem freshBytePre (reads writes : ByteRange) :
    readWritePre initial root root reads writes {} {} visit visit := by
  refine ⟨by cbv, by cbv, ?_, ?_⟩
  · intro byte location member _
    rw [initialLocation member]
    exact readRoot
  · intro byte location member _
    rw [initialLocation member]
    exact ⟨fun _ => readThenWriteRoot, fun _ => writeRoot⟩

private def child : BorTag := ⟨2, by decide⟩
private def childTree :=
  (initial.newChild Size.ZERO root child
    (DedupRangeMap.new (Size.ofBytes 6) ⟨.Unique, true, .None⟩) (.ReservedFrz false) false).tree
private def childLocation : LocationTree :=
  (childTree.locations.entries[0]?.map (·.data)).getD {}

private theorem childEntries :
    childTree.locations.entries = #[⟨⟨0, 6⟩, childLocation⟩] := by cbv

private theorem childLocation_at {byte : UInt64} {location : LocationTree}
    (member : childTree.locations.MapAt byte location) : location = childLocation := by
  obtain ⟨position, segment, entry, _, value⟩ := member
  rw [childEntries] at entry
  have inside := (Array.getElem?_eq_some_iff.mp entry).choose
  have same : position = 0 := by simp at inside; omega
  subst position
  simp at entry
  subst segment
  exact value.symm

/-- Reading through the parent changes the child's Unique permission on the
read bytes. A write through the child still succeeds on adjacent bytes. -/
private theorem separateAllowed :
    readWritePre childTree root (.concrete child) readRange separateRange
      {} {} visit visit := by
  refine ⟨by cbv, by cbv, ?_, ?_⟩
  · intro byte location member _
    rw [childLocation_at member]
    cbv
  · intro byte location member writes
    rw [childLocation_at member]
    refine ⟨?_, fun _ => by cbv⟩
    intro reads
    have lower : (4 : UInt64) ≤ byte := writes.1
    have upper : byte < (4 : UInt64) := reads.2
    exact False.elim ((UInt64.not_lt.mpr lower) upper)

/-- Byte 2 is in both intervals. The foreign parent read freezes the child
there, so the local child write is forbidden. -/
private theorem overlapDenied :
    ¬ readWritePre childTree root (.concrete child) readRange overlapRange
      {} {} visit visit := by
  rintro ⟨_, _, _, writes⟩
  have member : childTree.locations.MapAt 2 childLocation :=
    ⟨0, ⟨⟨0, 6⟩, childLocation⟩, by rw [childEntries]; rfl, by cbv, rfl⟩
  have paired := (writes 2 childLocation member (by cbv)).1 (by cbv)
  cbv at paired
  cases paired.1

private def repeatedBytes : DedupRangeMap Nat :=
  ⟨#[⟨⟨0, 2⟩, 7⟩, ⟨⟨2, 3⟩, 7⟩, ⟨⟨3, 6⟩, 7⟩]⟩

private theorem repeatedWellFormed : repeatedBytes.WellFormed := by
  unfold DedupRangeMap.WellFormed
  have nonempty : repeatedBytes.entries.size ≠ 0 := by decide
  rw [dite_eq_right nonempty]
  refine ⟨rfl, ?_, ?_⟩
  · intro i inside
    have count : repeatedBytes.entries.size = 3 := rfl
    rw [count] at inside
    have possible : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases possible with rfl | rfl | rfl <;> cbv
  · intro i inside
    have count : repeatedBytes.entries.size = 3 := rfl
    rw [count] at inside
    have possible : i = 0 ∨ i = 1 := by omega
    rcases possible with rfl | rfl <;> rfl

private def splitAndMerge := repeatedBytes.iterMut readOffset readLength

/-- Preparing [1,4) splits two boundary segments and merges the equal
interior run into one selected slot, preserving every byte's initial data. -/
example :
    splitAndMerge.PreparedFor readRange repeatedBytes.MapAt ∧
    splitAndMerge.positions = #[1] ∧
    splitAndMerge.state.entries = #[⟨⟨0, 1⟩, 7⟩, ⟨⟨1, 4⟩, 7⟩, ⟨⟨4, 6⟩, 7⟩] := by
  have geometry := DedupRangeMap.iterMut_preparedFor repeatedBytes readOffset readLength (Size.ofBytes 4)
    repeatedWellFormed (by cbv) (by cbv)
  exact ⟨geometry.1, by cbv, by cbv⟩

private theorem childWellFormed : childTree.locations.WellFormed := by
  change (⟨childTree.locations.entries⟩ : DedupRangeMap LocationTree).WellFormed
  rw [childEntries]
  exact DedupRangeMap.new_wellFormed (Size.ofBytes 6) childLocation

private theorem readEnd : readOffset.add readLength = .ok (Size.ofBytes 4) := by cbv
private theorem overlapEnd : overlapOffset.add overlapLength = .ok (Size.ofBytes 6) := by cbv
private theorem separateEnd : separateOffset.add separateLength = .ok (Size.ofBytes 6) := by cbv
private theorem childReadBound : (Size.ofBytes 4).bytes ≤ childTree.locations.size.bytes := by cbv
private theorem childWriteBound : (Size.ofBytes 6).bytes ≤ childTree.locations.size.bytes := by cbv

/-- The ordinary range operations agree with the byte obligations when their
endpoints are checked on the initial tree. -/
example :
    ¬ wp ((do
      let reads ← access root readOffset readLength .Read {} visit
      let writes ← access (.concrete child) overlapOffset overlapLength .Write {} visit
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => True) (fun _ _ => False) childTree := by
  miri_tree_range_wp bytes using childWellFormed, readEnd, overlapEnd, childReadBound, childWriteBound
  exact overlapDenied

example :
    wp ((do
      let reads ← access root readOffset readLength .Read {} visit
      let writes ← access (.concrete child) separateOffset separateLength .Write {} visit
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => True) (fun _ _ => False) childTree := by
  have formed := childWellFormed
  have readChecked := readEnd
  have writeChecked := separateEnd
  have readInside := childReadBound
  have writeInside := childWriteBound
  miri_tree_range_wp bytes
  exact separateAllowed

private theorem initialWellFormed : initial.locations.WellFormed :=
  DedupRangeMap.new_wellFormed (Size.ofBytes 6) rootLocation

set_option experimental.vcgen true in
/-- Verification condition generation exposes the byte obligations for a
read of [1,4) followed by a write of [2,6). -/
example :
    Triple ((do
      let reads ← access root readOffset readLength .Read {} visit
      let writes ← access root overlapOffset overlapLength .Write {} visit
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun current => current = initial) (fun _ _ => True) (fun _ _ => False) := by
  vcgen
  rename_i current atEntry
  subst current
  have initialReadBound : (Size.ofBytes 4).bytes ≤ initial.locations.size.bytes := by cbv
  have initialWriteBound : (Size.ofBytes 6).bytes ≤ initial.locations.size.bytes := by cbv
  miri_tree_range_wp bytes using initialWellFormed, readEnd, overlapEnd, initialReadBound, initialWriteBound
  exact freshBytePre readRange overlapRange


end MiriTests.Verification.TreeOverlapWP

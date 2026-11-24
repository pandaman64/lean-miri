import MutableSliceRetag
import duplicate_prefix.RetagLocationFrame
import duplicate_prefix.RetagFrozenChild
import duplicate_prefix.ActiveReleaseExclusive

namespace DuplicatePrefix.RetagReleaseFootprint

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open Miri.Verification.MutableRetagFootprint Miri.Verification.RangeModifyLaw
open GeneralRangeMapOrigins RetagLocationFrame SourceDomain

/-- Every materialized byte of the selected tag lies within its reborrow
extent. Lazy default states do not trigger a protector-end access. -/
def MaterializedWithin (tree : BorrowTree) (source : UniIndex) (lower upper : UInt64) : Prop :=
  EachByte tree.locations fun point row => ∀ state, row.perms.get source = some state →
    lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat

/-- A vacant sparse node has no saved permission in any materialized row. -/
def VacantRows (tree : BorrowTree) : Prop :=
  ∀ index, tree.nodeAt index = none → ∀ position (inside : position < tree.locations.entries.size),
    tree.locations.entries[position].data.perms.get index = none

theorem finish_from [DecidableEq α] (offset start : Size) (rows : DedupRangeMap α)
    (range : ByteRange) (ordered : range.start ≤ range.stop)
    (span : offset.bytes.toNat + range.stop.toNat ≤ rows.size.bytes.toNat)
    (added : Size.add (Size.ofBytes range.start) offset = .ok start) :
    start.bytes.toNat = offset.bytes.toNat + range.start.toNat ∧
      start.bytes.toNat + (range.stop - range.start).toNat = offset.bytes.toNat + range.stop.toNat := by
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  have noOverflow : range.start.toNat + offset.bytes.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (by omega) rows.size.bytes.toNat_lt
  have sumNat : (range.start + offset.bytes).toNat = range.start.toNat + offset.bytes.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt noOverflow]
  have ordinary : ¬ range.start + offset.bytes < range.start := by
    intro impossible
    have less := UInt64.lt_iff_toNat_lt.mp impossible
    omega
  have actual : Size.add (Size.ofBytes range.start) offset = .ok (Size.ofBytes (range.start + offset.bytes)) := by
    simp [Size.add, Size.ofBytes, ordinary]
  have startEq := Except.ok.inj (actual.symm.trans added)
  rw [← startEq]
  simp only [Size.ofBytes, sumNat, UInt64.toNat_sub_of_le _ _ ordered]
  omega

/-- The actual bounded child installation leaves absent slots vacant and
materializes the new tag only inside the selected reborrow extent. -/
theorem materialized_and_vacant (tree : BorrowTree) (offset length : Size) (parentTag tag : BorTag)
    (parent child : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
    (coherent : CoherentForest tree)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (vacantRows : VacantRows tree)
    (allocationBounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (span : ∀ seg ∈ inside.iterAll.toList, seg.range.start ≤ seg.range.stop ∧
      seg.range.stop.toNat ≤ length.bytes.toNat)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ()) :
    let after := (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
    MaterializedWithin after child offset.bytes (offset.bytes + length.bytes) ∧ VacantRows after := by
  let after := (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
  let grant := fun (point : UInt64) (_ : LocationState) =>
    offset.bytes.toNat ≤ point.toNat ∧ point.toNat < (offset.bytes + length.bytes).toNat
  have frame : FramedAt grant tree.locations child after := by
    apply newChild_framed_at (fun _ _ _ _ _ h => h) tree offset parentTag tag parent child
      mapping inside outside held mapped parentFound parentNode present vacant
      coherent.ranges (vacantRows child vacant) _ _ complete
    · intro segment inSegments start checked
      obtain ⟨ordered, upper⟩ := span segment inSegments
      have ends := finish_from offset start tree.locations segment.range ordered (by omega) checked
      omega
    · intro segment inSegments start checked point lo hi
      obtain ⟨ordered, upper⟩ := span segment inSegments
      have ends := finish_from offset start tree.locations segment.range ordered (by omega) checked
      have noOverflow : offset.bytes.toNat + length.bytes.toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt allocationBounds tree.locations.size.bytes.toNat_lt
      have add : (offset.bytes + length.bytes).toNat = offset.bytes.toNat + length.bytes.toNat := by
        simp [UInt64.toNat_add, Nat.mod_eq_of_lt noOverflow]
      have lastFits : start.bytes.toNat + (segment.range.stop - segment.range.start).toNat < 2 ^ 64 := by omega
      have endPoint : (start.bytes + (segment.range.stop - segment.range.start)).toNat =
          start.bytes.toNat + (segment.range.stop - segment.range.start).toNat := by
        simp [UInt64.toNat_add, Nat.mod_eq_of_lt lastFits]
      unfold grant
      rw [add]
      omega
  have attached := (MutableSliceRetag.attachment tree offset parentTag tag parent child mapping inside outside held
    coherent mapped parentFound parentNode present vacant complete).1
  refine ⟨fun point position bounded lo hi => (frame.2.2 point position bounded lo hi).2, ?_⟩
  intro query absent position bounded
  have childPresent : ∃ node, after.nodeAt child = some node ∧ node.parent = some parent := attached.childParent
  have distinct : query ≠ child := by
    intro same
    obtain ⟨node, found, _⟩ := childPresent
    rw [same, found] at absent
    contradiction
  have priorAbsent : tree.nodeAt query = none := by
    cases found : tree.nodeAt query with
    | none => rfl
    | some node =>
      obtain ⟨next, stored, _⟩ := attached.oldEdges query node found
      rw [stored] at absent
      contradiction
  have nonempty : after.locations.entries.size ≠ 0 := by
    change position < after.locations.entries.size at bounded
    omega
  have partition := frame.2.1
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at partition
  let point := after.locations.entries[position].range.start
  obtain ⟨⟨previous, atPoint, retained⟩, _⟩ := frame.2.2 point position bounded (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _))
    (partition.2.1 position bounded)
  obtain ⟨i, valid, _, _, same⟩ := atPoint
  have oldMissing : previous.perms.get query = none := by
    rw [← same]
    exact vacantRows query priorAbsent i valid
  have saved := retained query distinct
  unfold storedPermission at saved
  rw [oldMissing] at saved
  cases lookup : after.locations.entries[position].data.perms.get query with
  | none => rfl
  | some state => simp [lookup] at saved

/-- Every materialized release visit is covered by the formed borrow's
scope and its exclusive per-byte grant. -/
theorem active_of_footprint (tree : BorrowTree) (tags : ProtectedTags) (source : UniIndex)
    (lower upper : UInt64) (coherent : CoherentForest tree)
    (materialized : MaterializedWithin tree source lower upper) (vacant : VacantRows tree)
    (owned : OwnedOn (fun row => ArchiveForestProjection.LocationRights tree row tags source)
      lower upper tree.locations) :
    GeneralRangeMapState.Every (RetagReleaseRights.ActiveByteRights tree tags source) tree.locations := by
  intro position inside state kind present _ _
  let row := tree.locations.entries[position]
  have nonempty : tree.locations.entries.size ≠ 0 := by omega
  have valid := coherent.ranges
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at valid
  have positive : row.range.start < row.range.stop := valid.2.1 position inside
  obtain ⟨lowerBound, upperBound⟩ :=
    materialized row.range.start position inside (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) positive state present
  have rowRights := owned position inside (by omega) upperBound
    (Nat.lt_of_le_of_lt lowerBound (UInt64.lt_iff_toNat_lt.mp positive))
  exact ⟨rowRights, fun query empty => vacant query empty position inside⟩

#print axioms materialized_and_vacant

end DuplicatePrefix.RetagReleaseFootprint

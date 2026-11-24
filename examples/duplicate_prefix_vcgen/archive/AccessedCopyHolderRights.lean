import duplicate_prefix.CopyHolderRights

namespace DuplicatePrefix.AccessedCopyHolderRights

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection RetagReleaseRights
open GeneralBorrowExposure GeneralBorrowProjection GeneralBorrowPresence BorrowRangeAccess GeneralRangeMapOrigins
open GeneralBorrowPermissions GeneralBorrowRangePreserves
open Miri.Verification.RangeModifyLaw RetagReleaseFootprint

set_option maxRecDepth 65536
set_option maxHeartbeats 1800000

private theorem ancestor_frame {before after : BorrowTree} (same : before.nodes = after.nodes)
    {index source : UniIndex} (path : Ancestor before index source) : Ancestor after index source := by
  induction path with
  | self => exact .self _
  | parent _ node found edge ih =>
    exact .parent ih node (by simpa only [BorrowTree.nodeAt, ← same] using found) edge

open CopyHolderRights

private theorem positive_row (table : DedupRangeMap LocationTree) (well : table.WellFormed)
    (position : Nat) (valid : position < table.entries.size) :
    table.entries[position].range.start.toNat < table.entries[position].range.stop.toNat := by
  have nonempty : table.entries.size ≠ 0 := by omega
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at well
  exact UInt64.lt_iff_toNat_lt.mp (well.2.1 position valid)

/-- Rights over the caller's slice and the global release footprint survive
both raw accesses of the copy. -/
structure Footprint (tree : BorrowTree) (tags : ProtectedTags)
    (source holder : UniIndex) (lower upper : UInt64) : Prop where
  sourceRights : OwnedOn (fun row => LocationRights tree row tags source) lower upper tree.locations
  holderRights : OwnedOn (fun row => LocationRights tree row tags holder) lower upper tree.locations
  accessed : EachByte tree.locations (fun point row =>
    ∀ saved, row.perms.get holder = some saved → saved.accessed = true →
      lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat)
  vacant : VacantRows tree

theorem accessRange_retains_holder (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (source holder root : UniIndex) (kind : AccessKind) (offset length : Size)
    (lower upper : UInt64)
    (coherent : CoherentForest tree) (node : TreeNode) (present : tree.nodeAt source = some node)
    (roots : tree.roots = #[root]) (found : tree.indexOfTag tag = some source)
    (lineage : Ancestor tree holder source)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index source → ¬ Ancestor tree index holder → tags.contains data.tag = false)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (left : lower.toNat ≤ offset.bytes.toNat)
    (right : (offset.bytes + length.bytes).toNat ≤ upper.toNat)
    (before : Footprint tree tags source holder lower upper) :
    let access := tree.performBorrowAccessRange (.concrete tag) offset length kind tags .VisitChildrenOfAccessed
    access.status = .Completed ∧ access.tree = {tree with locations := access.tree.locations} ∧
      CoherentForest access.tree ∧ access.tree.locations.size = tree.locations.size ∧
      Footprint access.tree tags source holder lower upper := by
  obtain ⟨rank,bounded,decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank,bounded,by
    intro index data present previous edge
    obtain ⟨parent, parentFound⟩ := coherent.parentPresent index data previous present edge
    exact ⟨parent,parentFound,decreases index data previous present edge⟩⟩
  have childData := forest_children tree coherent
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index data present next member
    obtain ⟨child, known, _⟩ := (childData index data present).2.1 next member
    exact ⟨child,known⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data present edge
    simpa using (coherent.rootEdges index data present).mp edge
  have selected : OwnedOn (fun row => LocationRights tree row tags source)
      offset.bytes (offset.bytes + length.bytes) tree.locations := by
    intro position valid positive lo hi
    exact before.sourceRights position valid (by omega) (by omega) (by omega)
  have authorized := bounded_slots tree tags source root kind offset length coherent node present roots bounds selected
  let byteProperty (point : UInt64) (row : LocationTree) :=
    (∀ index, tree.nodeAt index = none → row.perms.get index = none) ∧
      (∀ state, row.perms.get holder = some state → state.accessed = true → lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat) ∧
      (lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
        LocationRights tree row tags source ∧ LocationRights tree row tags holder)
  have byteBefore : EachByte tree.locations byteProperty := by
    intro point position valid lo hi
    have loNat := UInt64.le_iff_toNat_le.mp lo
    have hiNat := UInt64.lt_iff_toNat_lt.mp hi
    refine ⟨fun index empty => before.vacant index empty position valid,
      before.accessed point position valid lo hi, ?_⟩
    intro leftPoint rightPoint
    exact ⟨before.sourceRights position valid (by omega) (by omega) (by omega),
      before.holderRights position valid (by omega) (by omega) (by omega)⟩
  have byteStable : ∀ (segment : RangeMapSegment LocationTree) (point : UInt64),
      offset.bytes.toNat ≤ point.toNat → point.toNat < (offset.bytes + length.bytes).toNat →
      segment.range.start ≤ point → point < segment.range.stop → byteProperty point segment.data →
      byteProperty point (tree.performTreeAccessAt segment.data (some source) kind tags
        .VisitChildrenOfAccessed segment.range).location := by
    intro segment point start stop _ _ prior
    have graph := forest tree segment.data tags coherent.indexFits depth childData
    have rights := access_retains_holder tree segment.data tags source holder root kind .VisitChildrenOfAccessed
      segment.range node present depth coherent.indexFits children roots covered graph lineage unheld
      prior.1 (prior.2.2 (by omega) (by omega)).1
    refine ⟨?_, fun _ _ _ => ⟨by omega,by omega⟩, fun _ _ => rights⟩
    intro index empty
    rw [single_root_location tree segment.data tags source root kind segment.range coherent node present roots]
    exact normal_no_stale tree segment.data tags source index kind .VisitChildrenOfAccessed
      depth children node present empty (prior.1 index empty)
  have run := preserve_range_property_with_byte_frame tree tag source tags kind .VisitChildrenOfAccessed
    offset length lower upper (fun _ => True) found coherent.ranges bounds
    (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ _ => True.intro)
    byteProperty byteBefore byteStable authorized
  let after := tree.performBorrowAccessRange (.concrete tag) offset length kind tags .VisitChildrenOfAccessed
  obtain ⟨complete, _, well, sameSize, same, framed⟩ := run
  refine ⟨complete,same,?_,sameSize,?_⟩
  · rw [same]
    exact {coherent with ranges := well}
  · have occupied := positive_row after.tree.locations well
    have both : OwnedOn (fun row => LocationRights tree row tags source ∧ LocationRights tree row tags holder)
        lower upper after.tree.locations := by
      intro position valid positive lo hi
      let segment := after.tree.locations.entries[position]
      have ordered := occupied position valid
      by_cases starts : lower.toNat ≤ segment.range.start.toNat
      · exact (framed segment.range.start position valid (UInt64.le_refl _)
          (UInt64.lt_iff_toNat_lt.mpr ordered)).2.2 starts lo
      · exact (framed lower position valid (UInt64.le_iff_toNat_le.mpr (by change segment.range.start.toNat ≤ _; omega))
          (UInt64.lt_iff_toNat_lt.mpr hi)).2.2 (Nat.le_refl _) positive
    have nodes : tree.nodes = after.tree.nodes := (congrArg BorrowTree.nodes same).symm
    constructor
    · intro position valid positive lo hi
      exact rights_frame nodes _ tags source (both position valid positive lo hi).1
    · intro position valid positive lo hi
      exact rights_frame nodes _ tags holder (both position valid positive lo hi).2
    · intro point position valid lo hi
      exact (framed point position valid lo hi).2.1
    · intro index empty position valid
      have original := congrArg (fun t : BorrowTree => t.nodeAt index) same
      have missing : tree.nodeAt index = none := original.symm.trans empty
      let start := after.tree.locations.entries[position].range.start
      exact (framed start position valid (UInt64.le_refl _)
        (UInt64.lt_iff_toNat_lt.mpr (occupied position valid))).1 index missing

/-- The actual read/write pair of a prefix copy retains the caller holder's
scoped release premises over the full slice. -/
theorem prefixCopy_retains_holder (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (source holder root : UniIndex) (offset : Size) (count length : UInt64)
    (canonical : count.toNat + count.toNat ≤ length.toNat)
    (coherent : CoherentForest tree) (node : TreeNode) (present : tree.nodeAt source = some node)
    (roots : tree.roots = #[root]) (found : tree.indexOfTag tag = some source)
    (lineage : Ancestor tree holder source)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index source → ¬ Ancestor tree index holder → tags.contains data.tag = false)
    (fits : offset.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat)
    (before : Footprint tree tags source holder offset.bytes (offset.bytes + length)) :
    let read := tree.performBorrowAccessRange (.concrete tag) offset (Size.ofBytes count)
      .Read tags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset.bytes+count))
      (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      write.tree = {tree with locations := write.tree.locations} ∧
      CoherentForest write.tree ∧ write.tree.locations.size = tree.locations.size ∧
      Footprint write.tree tags source holder offset.bytes (offset.bytes + length) := by
  let middle := offset.bytes + count
  let upper := offset.bytes + length
  let read := tree.performBorrowAccessRange (.concrete tag) offset (Size.ofBytes count)
    .Read tags .VisitChildrenOfAccessed
  have firstBound : offset.bytes.toNat + count.toNat ≤ tree.locations.size.bytes.toNat := by omega
  have middleNat : middle.toNat = offset.bytes.toNat + count.toNat := by
    have noWrap := Nat.lt_of_le_of_lt firstBound tree.locations.size.bytes.toNat_lt
    simp only [middle,UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  have upperNat : upper.toNat = offset.bytes.toNat + length.toNat := by
    have noWrap := Nat.lt_of_le_of_lt fits tree.locations.size.bytes.toNat_lt
    simp only [upper,UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  have first := accessRange_retains_holder tree tags tag source holder root .Read offset
    (Size.ofBytes count) offset.bytes upper coherent node present roots found lineage unheld firstBound
    (Nat.le_refl _) (show middle.toNat ≤ upper.toNat by omega) before
  obtain ⟨firstDone, firstShape, firstForest, firstSize, firstFootprint⟩ := first
  change read.tree = {tree with locations := read.tree.locations} at firstShape
  have nodes : tree.nodes = read.tree.nodes := (congrArg BorrowTree.nodes firstShape).symm
  have readPresent : read.tree.nodeAt source = some node := by
    simpa only [BorrowTree.nodeAt,← nodes] using present
  have readRoots : read.tree.roots = #[root] := (congrArg BorrowTree.roots firstShape).trans roots
  have readFound : read.tree.indexOfTag tag = some source :=
    (congrArg (fun t : BorrowTree => t.indexOfTag tag) firstShape).trans found
  have readUnheld : ∀ index data, read.tree.nodeAt index = some data →
      Ancestor read.tree index source → ¬ Ancestor read.tree index holder → tags.contains data.tag = false := by
    intro index data lookup childPath noHolder
    apply unheld index data _ (ancestor_frame nodes.symm childPath)
      (fun path => noHolder (ancestor_frame nodes path))
    simpa only [BorrowTree.nodeAt,nodes] using lookup
  have secondBound : middle.toNat + count.toNat ≤ read.tree.locations.size.bytes.toNat := by
    change read.tree.locations.size = tree.locations.size at firstSize
    rw [firstSize]
    omega
  have secondHigh : (middle + count).toNat ≤ upper.toNat := by
    have noWrap := Nat.lt_of_le_of_lt secondBound read.tree.locations.size.bytes.toNat_lt
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
    omega
  have second := accessRange_retains_holder read.tree tags tag source holder root .Write
    (Size.ofBytes middle) (Size.ofBytes count) offset.bytes upper firstForest node readPresent readRoots readFound
    (ancestor_frame nodes lineage) readUnheld secondBound (show offset.bytes.toNat ≤ middle.toNat by omega)
    secondHigh firstFootprint
  obtain ⟨secondDone, secondShape, secondForest, secondSize, secondFootprint⟩ := second
  refine ⟨firstDone, secondDone, ?_, secondForest, secondSize.trans firstSize, secondFootprint⟩
  rw [secondShape]
  have framed := congrArg (fun chosen : BorrowTree => {chosen with locations :=
    (read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes middle)
      (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed).tree.locations}) firstShape
  exact framed

end DuplicatePrefix.AccessedCopyHolderRights

#print axioms DuplicatePrefix.AccessedCopyHolderRights.prefixCopy_retains_holder

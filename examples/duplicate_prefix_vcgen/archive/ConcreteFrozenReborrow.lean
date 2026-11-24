import duplicate_prefix.RetagGraphFrame
import duplicate_prefix.VacantRetagRead
import duplicate_prefix.ExclusiveRetagRead
import duplicate_prefix.ExclusiveFrozenEntry

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain MutableSliceRights GeneralRangeMapOrigins
open RetagFrozenChild

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

private theorem all_entries_of_owned {A : Type} (table : DedupRangeMap A)
    (well : table.WellFormed) (predicate : A → Prop)
    (owned : OwnedOn predicate 0 table.size.bytes table) :
    ∀ position (valid : position < table.entries.size), predicate table.entries[position].data := by
  intro position valid
  have notEmpty : 0 < table.entries.size := by omega
  let last := table.entries.size - 1
  have lastValid : last < table.entries.size := by dsimp [last]; omega
  have final := congrArg UInt64.toNat (GeneralRangeMapGeometry.size_last table notEmpty)
  change table.size.bytes.toNat = (table.entries[last]'lastValid).range.stop.toNat at final
  have positive := (GeneralRangeMapGeometry.facts table well (by omega)).2.1
  refine owned position valid ?_ ?_ ?_
  · change 0 < table.size.bytes.toNat
    have lastNonempty := positive last lastValid
    omega
  · by_cases isLast : position = last
    · subst position
      have lastNonempty := positive last lastValid
      omega
    · have before : position < last := by dsimp [last] at *; omega
      have ordered := GeneralRangeMapGeometry.stop_le_start table well position last before lastValid
      have rowNonempty := positive position valid
      have lastNonempty := positive last lastValid
      omega
  · change 0 < table.entries[position].range.stop.toNat
    have rowNonempty := positive position valid
    omega

private theorem owned_byte {tree : BorrowTree} {protectors : ProtectedTags} {source : UniIndex}
    {lower upper point : UInt64} {location : LocationTree}
    (ownership : OwnedOn (fun row => LocationRights tree row protectors source) lower upper tree.locations)
    (start : lower.toNat ≤ point.toNat) (stop : point.toNat < upper.toNat)
    (contains : ValueAt tree.locations point location) : OwnsByte tree location protectors source := by
  obtain ⟨position, valid, before, after, exact⟩ := contains
  have rights := ownership position valid (by omega) (by omega) (by omega)
  rw [exact] at rights
  intro index node found
  obtain ⟨state, current, localRights, foreignRights⟩ := rights index node found
  exact ⟨state, current, fun lineage => (localOwns_iff _ _).mp (localRights lineage),
    fun unrelated => (foreignCompatible_iff _ _).mp (foreignRights unrelated)⟩

/-- Execute the real read and new-child operations of a frozen mutable
reborrow, from the same original allocation ownership and vacancy invariant.
The returned grant concerns the fresh child under the requested protector mode. -/
theorem coherent_frozen_reborrow_with_mode
    (tree : BorrowTree) (protectors : ProtectedTags)
    (parentTag tag : BorTag) (parent root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (coherent : CoherentForest tree) (parentNode : TreeNode)
    (parentStored : tree.nodeAt parent = some parentNode)
    (roots : tree.roots = #[root]) (parentFound : tree.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes) (rank : depth.depth parent < tree.nodes.size)
    (tagFresh : tree.indexOfTag tag = none)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (clean : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationRights tree location protectors parent)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held
    read.status = .Completed ∧ result.outcome = .ok () ∧
      result.tree.locations.size = tree.locations.size ∧ CoherentForest result.tree ∧ result.tree.roots = #[root] ∧
      ∃ child, result.tree.indexOfTag tag = some child ∧
        (∃ node, result.tree.nodeAt child = some node ∧ node.tag = tag) ∧
        ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
          point.toNat < (offset.bytes + length.bytes).toNat →
          ∀ location, ValueAt result.tree.locations point location →
            OwnsByte result.tree location (childProtections protectors tag held) child := by
  let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
  let archivedDepth : GeneralBorrowExposure.ParentDepth tree.nodes :=
    ⟨depth.depth, depth.bounded, depth.parent⟩
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index node known child member
    have fromChild : child ∈ node.children := by simpa using member
    obtain ⟨node, found, _⟩ := (coherent.childEdges index node known).2.1 child fromChild
    exact ⟨node, found⟩
  have scopedClean : OwnedOn
      (fun row => ∀ index, tree.nodeAt index = none → row.perms.get index = none)
      offset.bytes (offset.bytes + length.bytes) tree.locations := by
    intro pos valid _ _ _ index vacant
    exact clean index vacant pos valid
  have fullClean : OwnedOn
      (fun row => ∀ index, tree.nodeAt index = none → row.perms.get index = none)
      0 tree.locations.size.bytes tree.locations := by
    intro pos valid _ _ _ index vacant
    exact clean index vacant pos valid
  obtain ⟨readOk, readCoherent, readHead, readFound, readRoots, readSize, readOwners⟩ :=
    retag_read_ownership tree protectors parentTag parent root offset length offset.bytes
      (offset.bytes + length.bytes) coherent parentNode parentStored roots parentFound owners scopedClean
      bounds (Nat.le_refl _) (Nat.le_refl _)
  have readClean := read_preserves_vacant tree protectors parentTag parent root offset length coherent
    parentNode parentStored roots parentFound archivedDepth children bounds owners 0 tree.locations.size.bytes fullClean
  rw [← readSize] at readClean
  have cleanAll := all_entries_of_owned read.tree.locations readCoherent.ranges _ readClean
  have frame : read.tree = {tree with locations := read.tree.locations} :=
    GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) offset length .Read protectors .VisitChildrenOfAccessed
  have sameNodes : read.tree.nodes = tree.nodes := by
    have equality := congrArg BorrowTree.nodes frame
    exact equality
  have sameMap : read.tree.tagMapping = tree.tagMapping := by
    have equality := congrArg BorrowTree.tagMapping frame
    exact equality
  let readDepth : BorrowTree.ZeroProtection.ParentDepth read.tree.nodes := {
    depth := depth.depth
    bounded := by
      intro index node found
      rw [sameNodes] at found ⊢
      exact depth.bounded index node found
    parent := by
      intro index node found parent edge
      rw [sameNodes] at found ⊢
      exact depth.parent index node found parent edge }
  have readRank : readDepth.depth parent < read.tree.nodes.size := by
    change depth.depth parent < read.tree.nodes.size
    rwa [sameNodes]
  have readTagFresh : read.tree.indexOfTag tag = none := by
    unfold BorrowTree.indexOfTag
    rwa [sameMap]
  have readFresh : ∀ index node, read.tree.nodeAt index = some node → node.tag ≠ tag := by
    intro index node known
    apply fresh index node
    unfold BorrowTree.nodeAt at known
    rwa [sameNodes] at known
  have reuseRead : ∀ index, read.tree.tagMapping.deassigned.back? = some index →
      index.toNat < read.tree.nodes.size ∧ read.tree.nodeAt index = none := by
    intro index selected
    rw [sameMap] at selected
    simpa only [sameNodes, BorrowTree.nodeAt] using reuse index selected
  obtain ⟨mapping, child, inserted, done, key, stored, capacity, partition, rights⟩ :=
    install_frozen_entry_with_mode read.tree offset protectors parentTag tag parent parentNode inside held readCoherent
      readFound readHead readTagFresh readFresh (by simpa only [sameMap] using room)
      (by simpa only [sameMap, sameNodes] using aligned) reuseRead readDepth readRank
      (fun index vacant position valid => cleanAll position valid index vacant)
      (by
        have exactSize : read.tree.locations.size = tree.locations.size := readSize
        rw [exactSize]
        exact span) frozen offset.bytes (offset.bytes + length.bytes)
      (fun _ start stop _ inside => owned_byte readOwners start stop inside)
  obtain ⟨selectedMap, selected, selectedTag, selectedBound, selectedVacant⟩ :=
    select_slot read.tree tag readTagFresh (by simpa only [sameMap] using room)
      (by simpa only [sameMap, sameNodes] using aligned) reuseRead
  obtain ⟨childCoherent, childRoots⟩ :=
    frozen_child_coherent_with_mode read.tree offset parentTag tag parent selected selectedMap inside held
      selectedTag readFound parentNode readHead selectedVacant selectedBound readCoherent readDepth readRank
      done partition
  exact ⟨readOk, done, capacity.trans readSize, childCoherent, childRoots.trans readRoots,
    child, key, stored, rights⟩

/-- Frozen constructors preserve the range partition and transfer byte grants. -/
theorem concrete_frozen_reborrow_with_mode
    (tree : BorrowTree) (protectors : ProtectedTags)
    (parentTag tag : BorTag) (parent root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (coherent : CoherentForest tree) (parentNode : TreeNode)
    (parentStored : tree.nodeAt parent = some parentNode)
    (roots : tree.roots = #[root]) (parentFound : tree.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes) (rank : depth.depth parent < tree.nodes.size)
    (tagFresh : tree.indexOfTag tag = none)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (clean : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationRights tree location protectors parent)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held
    read.status = .Completed ∧ result.outcome = .ok () ∧
      result.tree.locations.size = tree.locations.size ∧ result.tree.locations.WellFormed ∧
      ∃ child, result.tree.indexOfTag tag = some child ∧
        (∃ node, result.tree.nodeAt child = some node ∧ node.tag = tag) ∧
        ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
          point.toNat < (offset.bytes + length.bytes).toNat →
          ∀ location, ValueAt result.tree.locations point location →
            OwnsByte result.tree location (childProtections protectors tag held) child := by
  obtain ⟨readOk, done, capacity, forest, _, child, key, node, rights⟩ :=
    coherent_frozen_reborrow_with_mode tree protectors parentTag tag parent root offset length inside held
      coherent parentNode parentStored roots parentFound depth rank tagFresh fresh room aligned reuse
      clean span frozen bounds owners
  exact ⟨readOk, done, capacity, forest.ranges, child, key, node, rights⟩

theorem concrete_frozen_reborrow
    (tree : BorrowTree) (protectors : ProtectedTags)
    (parentTag tag : BorTag) (parent root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState)
    (coherent : CoherentForest tree) (parentNode : TreeNode)
    (parentStored : tree.nodeAt parent = some parentNode)
    (roots : tree.roots = #[root]) (parentFound : tree.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes) (rank : depth.depth parent < tree.nodes.size)
    (tagFresh : tree.indexOfTag tag = none)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (clean : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenEntryState segment.data)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationRights tree location protectors parent)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) true
    read.status = .Completed ∧ result.outcome = .ok () ∧
      result.tree.locations.size = tree.locations.size ∧ result.tree.locations.WellFormed ∧
      ∃ child, result.tree.indexOfTag tag = some child ∧
        (∃ node, result.tree.nodeAt child = some node ∧ node.tag = tag) ∧
        ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
          point.toNat < (offset.bytes + length.bytes).toNat →
          ∀ location, ValueAt result.tree.locations point location →
            OwnsByte result.tree location (protectors.insert tag .StrongProtector) child :=
  concrete_frozen_reborrow_with_mode tree protectors parentTag tag parent root offset length inside true
    coherent parentNode parentStored roots parentFound depth rank tagFresh fresh room aligned reuse clean
    span frozen bounds owners

#print axioms concrete_frozen_reborrow
end DuplicatePrefix.ArchiveForestProjection

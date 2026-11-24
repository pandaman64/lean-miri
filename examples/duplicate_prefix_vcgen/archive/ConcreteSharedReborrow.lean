import duplicate_prefix.VacantRetagRead
import duplicate_prefix.ExclusiveRetagRead
import duplicate_prefix.RetagFrozenChild
import duplicate_prefix.RetagSharedChild
import duplicate_prefix.RetagKeyFrame
import Miri.Verification.MutableRetagFootprint

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain GeneralRangeMapOrigins
open RetagFrozenChild RetagSharedChild RetagLocationFrame
open Miri.Verification.MutableRetagFootprint

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

theorem concrete_shared_reborrow
    (tree : BorrowTree) (protectors : ProtectedTags)
    (parentTag tag : BorTag) (parent root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (coherent : CoherentForest tree) (parentNode : TreeNode)
    (parentStored : tree.nodeAt parent = some parentNode)
    (roots : tree.roots = #[root]) (parentFound : tree.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes) (rank : depth.depth parent < tree.nodes.size)
    (tagFresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (clean : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, segment.data = sharedState)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationRights tree location protectors parent)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) tag inside .Frozen held
    read.status = .Completed ∧ result.outcome = .ok () ∧
      result.tree.locations.size = tree.locations.size ∧
      ∃ child, result.tree.indexOfTag tag = some child ∧
        (∃ node, result.tree.nodeAt child = some node ∧
          node.tag = tag ∧ node.parent = some parent ∧ node.defaultInitialPermission = .Frozen) ∧
        FramedWith (fun state => state.permission = .Frozen ∧ state.accessed = true)
          read.tree.locations child result.tree := by
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
  obtain ⟨readOk, readCoherent, readHead, readFound, _, readSize, readOwners⟩ :=
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
  have reuseRead : ∀ index, read.tree.tagMapping.deassigned.back? = some index →
      index.toNat < read.tree.nodes.size ∧ read.tree.nodeAt index = none := by
    intro index selected
    rw [sameMap] at selected
    simpa only [sameNodes, BorrowTree.nodeAt] using reuse index selected
  obtain ⟨mapping, child, selected, slot, vacant⟩ :=
    select_slot read.tree tag readTagFresh (by simpa only [sameMap] using room)
      (by simpa only [sameMap, sameNodes] using aligned) reuseRead
  have readSpan : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ read.tree.locations.size.bytes.toNat := by
    rw [readSize]
    exact span
  have complete := newChild_shared_completes read.tree offset parentTag tag parent child mapping
    inside held selected readFound parentNode readHead vacant slot readCoherent.ranges readDepth
    readRank readSpan frozen
  let result := read.tree.newChild offset (.concrete parentTag) tag inside .Frozen held
  have key : result.tree.indexOfTag tag = some child :=
    newChild_selected_key read.tree offset (.concrete parentTag) tag inside .Frozen held mapping child selected
  have metadata := newChild_nodeMetadata read.tree offset parentTag tag parent child mapping inside
    .Frozen held selected readFound parentNode readHead vacant complete child
  have childStored : ∃ node, result.tree.nodeAt child = some node ∧
      node.tag = tag ∧ node.parent = some parent ∧ node.defaultInitialPermission = .Frozen := by
    simp only [ite_eq_left rfl] at metadata
    change nodeMetadata result.tree child = some (tag, some parent, .Frozen) at metadata
    unfold nodeMetadata at metadata
    cases found : result.tree.nodeAt child with
    | none => simp [found] at metadata
    | some node =>
      simp only [found, Option.map_some] at metadata
      exact ⟨node, rfl, congrArg Prod.fst (Option.some.inj metadata),
        congrArg (fun x => x.2.1) (Option.some.inj metadata),
        congrArg (fun x => x.2.2) (Option.some.inj metadata)⟩
  have frameWith : FramedWith (fun state => state.permission = .Frozen ∧ state.accessed = true)
        read.tree.locations child result.tree := by
    refine newChild_framed_with ?_ read.tree offset parentTag tag parent child mapping inside .Frozen
      held selected readFound parentNode readHead vacant readCoherent.ranges
      (fun position valid => cleanAll position valid child vacant) ?_ ?_ complete
    · intro old new permission accessed h
      exact ⟨permission.symm.trans h.1, accessed.symm.trans h.2⟩
    · intro segment member start checked
      obtain ⟨ordered, bounded⟩ := readSpan segment member
      obtain ⟨other, found, exactBounds⟩ := selected_size offset segment.range _ ordered bounded
      have same := Except.ok.inj (found.symm.trans checked)
      subst start
      exact exactBounds
    · intro segment member
      rw [frozen segment member]
      exact ⟨rfl, rfl⟩
  exact ⟨readOk, complete, frameWith.1.trans readSize, child, key, childStored, frameWith⟩

#print axioms concrete_shared_reborrow
end DuplicatePrefix.ArchiveForestProjection

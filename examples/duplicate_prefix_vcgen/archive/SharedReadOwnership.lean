import duplicate_prefix.ReadAccessRange
import duplicate_prefix.ExclusiveRetagRead
import duplicate_prefix.VacantRetagRead

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposure GeneralBorrowProjection GeneralRangeMapOrigins SourceDomain
open Miri.DataStructures

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- A retag read of the whole or a bounded part of the admitted byte window
preserves the same read grant at all bytes admitted by the caller. -/
theorem retag_readable_ownership
    (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (source root : UniIndex)
    (offset length : Size) (lower upper : UInt64)
    (coherent : CoherentForest tree)
    (head : TreeNode) (headFound : tree.nodeAt source = some head)
    (roots : tree.roots = #[root]) (tagFound : tree.indexOfTag tag = some source)
    (owners : OwnedOn (fun location => LocationAccessRights tree location protections source .Read) lower upper tree.locations)
    (clean : OwnedOn (fun location => ∀ index, tree.nodeAt index = none → location.perms.get index = none)
      lower upper tree.locations)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes + length.bytes).toNat ≤ upper.toNat) :
    let result := tree.performNormalAccessRange tag offset length .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ CoherentForest result.tree ∧
      result.tree.nodeAt source = some head ∧ result.tree.indexOfTag tag = some source ∧
      result.tree.roots = #[root] ∧ result.tree.locations.size = tree.locations.size ∧
      OwnedOn (fun location => LocationAccessRights result.tree location protections source .Read) lower upper result.tree.locations := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index node present parent edge
    obtain ⟨parentNode, found⟩ := coherent.parentPresent index node parent present edge
    exact ⟨parentNode, found, decreases index node parent present edge⟩⟩
  have childData : ∀ index node, tree.nodeAt index = some node →
      node.children.toList.Nodup ∧
        (∀ child ∈ node.children.toList, ∃ childNode,
          tree.nodeAt child = some childNode ∧ childNode.parent = some index) ∧
        (∀ child childNode, tree.nodeAt child = some childNode →
          childNode.parent = some index → child ∈ node.children.toList) := by
    intro index node present
    simpa using coherent.childEdges index node present
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro index node present child member
    obtain ⟨childNode, found, _⟩ := (childData index node present).2.1 child member
    exact ⟨childNode, found⟩
  have coverage : GeneralBorrowGraph.RootsCover tree := by
    intro index node present noParent
    simpa using (coherent.rootEdges index node present).mp noParent
  have normal : OwnedOn (GeneralBorrowRange.LocationOwned tree protections source .Read)
      lower upper tree.locations := by
    intro position valid positive start stop
    exact ⟨⟨forest tree _ protections coherent.indexFits depth childData⟩,
      normal_access_owned tree _ protections source .Read depth head headFound coherent.indexFits
        (clean position valid positive start stop) (owners position valid positive start stop)⟩
  let result := tree.performNormalAccessRange tag offset length .Read protections .VisitChildrenOfAccessed
  have checked := GeneralBorrowRangeLocal.access tree protections tag source root offset length .Read .Read
    .VisitChildrenOfAccessed (fun _ => rfl) coherent.indexFits depth childNodes head headFound roots coverage
    tagFound coherent.ranges lower upper normal bounds requestLower requestUpper
  have frame : result.tree = {tree with locations := result.tree.locations} :=
    GeneralBorrowFreshReadFrame.frame tree (.concrete tag) offset length .Read protections .VisitChildrenOfAccessed
  have next : CoherentForest result.tree := by
    rw [frame]
    exact {coherent with ranges := checked.2.2.1}
  have exactNode : result.tree.nodeAt source = some head :=
    (congrArg (fun tree : BorrowTree => tree.nodeAt source) frame).trans headFound
  have exactTag : result.tree.indexOfTag tag = some source :=
    (congrArg (fun tree : BorrowTree => tree.indexOfTag tag) frame).trans tagFound
  refine ⟨checked.1, next, exactNode, exactTag, (congrArg BorrowTree.roots frame).trans roots,
    checked.2.2.2, ?_⟩
  intro position valid positive start stop
  have sameNodes : result.tree.nodes = tree.nodes := by
    have equality := congrArg BorrowTree.nodes frame
    exact equality
  have resultDepth : ParentDepth result.tree.nodes := sameNodes.symm ▸ depth
  exact normal_access_owned_to_location result.tree _ protections source .Read resultDepth head exactNode
    (checked.2.1 position valid positive start stop).2

theorem readable_preserves_vacant
    (tree : BorrowTree) (protectors : ProtectedTags) (tag : BorTag) (source root : UniIndex)
    (offset length : Size) (coherent : CoherentForest tree)
    (head : TreeNode) (present : tree.nodeAt source = some head)
    (roots : tree.roots = #[root]) (found : tree.indexOfTag tag = some source)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (rights : OwnedOn (fun location => LocationAccessRights tree location protectors source .Read)
      offset.bytes (offset.bytes + length.bytes) tree.locations)
    (lower upper : UInt64)
    (clean : OwnedOn (fun location => ∀ index, tree.nodeAt index = none → location.perms.get index = none)
      lower upper tree.locations) :
    let run := tree.performBorrowAccessRange (.concrete tag) offset length .Read protectors .VisitChildrenOfAccessed
    OwnedOn (fun location => ∀ index, run.tree.nodeAt index = none → location.perms.get index = none)
      lower upper run.tree.locations := by
  have auth := bounded_slots_from_rights tree protectors source root .Read offset length
    coherent head present roots bounds rights
  have result := preserve_range_property tree tag source protectors .Read .VisitChildrenOfAccessed
    offset length lower upper _ found coherent.ranges bounds clean (by
      intro segment _ _ _ _ checked query vacant
      rw [single_root_location tree segment.data protectors source root .Read segment.range coherent head present roots]
      exact GeneralBorrowRangePreserves.normal_no_stale tree segment.data protectors source query .Read
        .VisitChildrenOfAccessed depth children head present vacant (checked query vacant)) auth
  dsimp only
  intro position valid positive start stop query vacant
  have before : tree.nodeAt query = none := by
    have same := congrArg (fun tree : BorrowTree => tree.nodeAt query) result.2.2.2.2
    exact same.symm.trans vacant
  exact result.2.1 position valid positive start stop query before

#print axioms retag_readable_ownership
#print axioms readable_preserves_vacant
end DuplicatePrefix.ArchiveForestProjection

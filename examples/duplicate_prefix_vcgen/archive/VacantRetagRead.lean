import duplicate_prefix.ExclusiveCopyRanges
import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain GeneralRangeMapOrigins GeneralBorrowExposure

/-- The same bounded normal read that prepares a frozen reborrow cannot
materialize stale entries at a vacant allocation slot. The invariant is
retained at later bytes and preserved across splits of the selected window. -/
theorem read_preserves_vacant
    (tree : BorrowTree) (protectors : ProtectedTags) (tag : BorTag) (source root : UniIndex)
    (offset length : Size) (coherent : CoherentForest tree)
    (head : TreeNode) (present : tree.nodeAt source = some head)
    (roots : tree.roots = #[root]) (found : tree.indexOfTag tag = some source)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (rights : OwnedOn (fun location => LocationRights tree location protectors source)
      offset.bytes (offset.bytes + length.bytes) tree.locations)
    (lower upper : UInt64)
    (clean : OwnedOn (fun location => ∀ index, tree.nodeAt index = none → location.perms.get index = none)
      lower upper tree.locations) :
    let run := tree.performBorrowAccessRange (.concrete tag) offset length .Read protectors .VisitChildrenOfAccessed
    OwnedOn (fun location => ∀ index, run.tree.nodeAt index = none → location.perms.get index = none)
      lower upper run.tree.locations := by
  have auth := bounded_slots tree protectors source root .Read offset length
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

#print axioms read_preserves_vacant
end DuplicatePrefix.ArchiveForestProjection

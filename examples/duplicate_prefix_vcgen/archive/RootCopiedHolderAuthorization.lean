import duplicate_prefix.CopyHolderRights
import duplicate_prefix.ReleaseFromHolderRights

namespace DuplicatePrefix.RootCopiedHolderAuthorization

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Verification
open SourceDomain CopyHolderRights ArchiveForestProjection GeneralBorrowExposure

set_option maxRecDepth 65536

/-- The exact tree produced by the two concrete copy accesses still permits
the enclosing mutable argument's own protector release. -/
theorem authorize (tree : BorrowTree) (tags : ProtectedTags) (copyTag holderTag : BorTag)
    (source holder root : UniIndex) (offset : Size) (count length : UInt64)
    (canonical : count.toNat + count.toNat ≤ length.toNat)
    (coherent : CoherentForest tree)
    (sourceNode holderNode : TreeNode)
    (atSource : tree.nodeAt source = some sourceNode)
    (atHolder : tree.nodeAt holder = some holderNode)
    (unexposed : holderNode.isExposed = false)
    (roots : tree.roots = #[root]) (found : tree.indexOfTag copyTag = some source)
    (holderFound : tree.indexOfTag holderTag = some holder)
    (lineage : Ancestor tree holder source)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index source → ¬ Ancestor tree index holder → tags.contains data.tag = false)
    (fits : offset.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat)
    (before : Footprint tree tags source holder offset.bytes (offset.bytes + length)) :
    let read := tree.performBorrowAccessRange (.concrete copyTag) offset (Size.ofBytes count)
      .Read tags .VisitChildrenOfAccessed
    let written := read.tree.performBorrowAccessRange (.concrete copyTag) (Size.ofBytes (offset.bytes+count))
      (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed
    written.tree.indexOfTag holderTag = some holder ∧
    written.tree.roots = #[root] ∧
    Nonempty (ParentDepth written.tree.nodes) ∧
    GeneralBorrowGraph.ChildNodes written.tree ∧
    written.tree.nodeAt holder = some holderNode ∧
    holderNode.isExposed = false ∧
    (∀ position < written.tree.locations.entries.size, ∃ slot,
      written.tree.locations.index position = .ok slot ∧
      ActiveRelease.ReleaseOwnership written.tree holder root tags slot) := by
  dsimp only
  obtain ⟨_, _, shape, valid, _, footprint⟩ :=
    prefixCopy_retains_holder tree tags copyTag source holder root offset count length
      canonical coherent sourceNode atSource roots found lineage unheld fits before
  let read := tree.performBorrowAccessRange (.concrete copyTag) offset (Size.ofBytes count)
    .Read tags .VisitChildrenOfAccessed
  let written := read.tree.performBorrowAccessRange (.concrete copyTag) (Size.ofBytes (offset.bytes+count))
    (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed
  change written.tree = {tree with locations := written.tree.locations} at shape
  have holderIndex : written.tree.indexOfTag holderTag = some holder := by rw [shape]; exact holderFound
  have holderPresent : written.tree.nodeAt holder = some holderNode := by rw [shape]; exact atHolder
  have rootIndex : written.tree.roots = #[root] := by rw [shape]; exact roots
  obtain ⟨rank, bound, smaller⟩ := valid.parentDepth
  let depth : ParentDepth written.tree.nodes := ⟨rank,bound,by
    intro index node present parent edge
    obtain ⟨data, found⟩ := valid.parentPresent index node parent present edge
    exact ⟨data,found,smaller index node parent present edge⟩⟩
  have children : GeneralBorrowGraph.ChildNodes written.tree := by
    intro index data present child childMem
    obtain ⟨childNode, found, _⟩ :=
      (RetagReleaseRights.forest_children written.tree valid index data present).2.1 child childMem
    exact ⟨childNode,found⟩
  have owned := ReleaseFromHolderRights.releaseOwnership written.tree tags holder root holderNode holderPresent
    valid rootIndex offset.bytes (offset.bytes+length) footprint.materialized footprint.vacant footprint.holderRights
  exact ⟨holderIndex,rootIndex,⟨depth⟩,children,holderPresent,unexposed,owned⟩

#print axioms authorize
end DuplicatePrefix.RootCopiedHolderAuthorization

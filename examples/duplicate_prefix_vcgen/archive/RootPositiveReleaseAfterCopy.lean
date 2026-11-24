import duplicate_prefix.RootPositiveTwoRelease
import duplicate_prefix.RootCopiedHolderRelease

namespace DuplicatePrefix.RootPositiveReleaseAfterCopy

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open SourceDomain CopyHolderRights

set_option maxRecDepth 65536
set_option maxHeartbeats 9500000

/-- Establish both releases on the exact copy result. The argument
allocation was updated by the two ranges. The disjoint physical
return allocation was unchanged until its own release visit. -/
theorem plan
    {K : Type} {initial copied : MemoryState Provenance BorrowTree K}
    {bufferId slotId : AllocId} {copyTag bufferTag slotTag : BorTag}
    {buffer slot : LocalAllocation Provenance BorrowTree K}
    (tracker : MachineHooks.BorrowState) (frame : FrameState)
    (ledger : frame.protectedTags = #[(bufferId, bufferTag), (slotId, slotTag)])
    (separate : slotId ≠ bufferId)
    (bufferLive : copied.live[bufferId]? = some buffer)
    (slotLive : initial.live[slotId]? = some slot)
    (unchanged : ∀ id, id ≠ bufferId → copied.live[id]? = initial.live[id]?)
    (tree : BorrowTree) (source holder root : UniIndex) (offset : Size) (count length : UInt64)
    (canonical : count.toNat + count.toNat ≤ length.toNat)
    (coherent : CoherentForest tree) (sourceNode holderNode : TreeNode)
    (atSource : tree.nodeAt source = some sourceNode)
    (atHolder : tree.nodeAt holder = some holderNode)
    (unexposed : holderNode.isExposed = false) (roots : tree.roots = #[root])
    (sourceTag : tree.indexOfTag copyTag = some source)
    (holderTag : tree.indexOfTag bufferTag = some holder)
    (lineage : Ancestor tree holder source)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index source → ¬ Ancestor tree index holder → tracker.global.protectedTags.contains data.tag = false)
    (fits : offset.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat)
    (before : Footprint tree tracker.global.protectedTags source holder offset.bytes (offset.bytes + length))
    (copiedTree :
      let read := tree.performBorrowAccessRange (.concrete copyTag) offset (Size.ofBytes count)
        .Read tracker.global.protectedTags .VisitChildrenOfAccessed
      buffer.allocation.extra = (read.tree.performBorrowAccessRange (.concrete copyTag)
        (Size.ofBytes (offset.bytes+count)) (Size.ofBytes count)
        .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree)
    (slotTree : BorrowTree)
    (slotRelease : slot.allocation.extra.releaseProtector slotTag tracker.global.protectedTags =
      ⟨slotTree, .Released⟩) :
    ∃ released,
      StackPopRelease.Plan tracker.global.protectedTags frame.protectedTags.toList copied released ∧
      released.live[slotId]? = some {slot with allocation := slot.allocation.setExtra slotTree} ∧
      (tracker.global.endCall frame).protectedTags.contains slotTag = false := by
  obtain ⟨bufferTree, bufferRelease⟩ := RootCopiedHolderRelease.release tree tracker.global.protectedTags copyTag bufferTag
    source holder root offset count length canonical coherent sourceNode holderNode atSource atHolder unexposed roots
    sourceTag holderTag lineage unheld fits before
  have release : buffer.allocation.extra.releaseProtector bufferTag tracker.global.protectedTags =
      ⟨bufferTree, .Released⟩ := by
    rw [copiedTree]
    exact bufferRelease
  obtain ⟨steps, _, slotStillLive, _, unprotected⟩ := RootPositiveTwoRelease.plan tracker frame ledger separate bufferLive
    ((unchanged slotId separate).trans slotLive) release slotRelease
  exact ⟨_,steps,slotStillLive,unprotected⟩

#print axioms plan
end DuplicatePrefix.RootPositiveReleaseAfterCopy

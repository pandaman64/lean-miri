import RejectionEntryAfterLength
import duplicate_prefix.ReleaseFromHolderRights

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.DataStructures Miri.Concurrency
open SourceDomain ArchiveForestProjection RetagReleaseFootprint
open GeneralBorrowExposure GeneralRangeMapOrigins

/-- Recover the root's active-return contract from its retained tree rights. -/
noncomputable def RetainedRootBorrow.ofRights
    (older : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (initial final : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (root : ActiveCaller older caller frame initial)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : final.memory.live[root.id]? = some entry)
    (tracker : MachineHooks.BorrowState) (tracked : final.borrowTracker = some tracker)
    (indexed : entry.allocation.extra.indexOfTag root.tag = some root.source)
    (roots : entry.allocation.extra.roots = #[root.root])
    (node : TreeNode) (found : entry.allocation.extra.nodeAt root.source = some node)
    (unexposed : node.isExposed = false)
    (coherent : CoherentForest entry.allocation.extra)
    (lower upper : UInt64) (extent : MaterializedWithin entry.allocation.extra root.source lower upper)
    (vacant : VacantRows entry.allocation.extra)
    (rights : OwnedOn (fun row => LocationRights entry.allocation.extra row tracker.global.protectedTags root.source)
      lower upper entry.allocation.extra.locations) :
    RetainedRootBorrow older caller frame initial final root := by
  let tree := entry.allocation.extra
  have depth : ParentDepth tree.nodes := by
    let rank := Classical.choose coherent.parentDepth
    have ⟨bounded, decreases⟩ := Classical.choose_spec coherent.parentDepth
    refine ⟨rank, bounded, ?_⟩
    intro index data saved parent edge
    obtain ⟨up, held⟩ := coherent.parentPresent index data parent saved edge
    exact ⟨up, held, by first | exact decreases index data parent saved edge | exact decreases index data parent edge⟩
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index data saved child member
    obtain ⟨childNode, childSaved, _⟩ := (coherent.childEdges index data saved).2.1 child (by simpa using member)
    exact ⟨childNode, childSaved⟩
  exact ⟨entry, present, tracker, tracked, indexed, roots, depth, children, node, found, unexposed,
    ReleaseFromHolderRights.releaseOwnership tree tracker.global.protectedTags root.source root.root node
      found coherent roots lower upper extent vacant rights⟩

#print axioms RetainedRootBorrow.ofRights
end DuplicatePrefix.RootZeroShallowReturn

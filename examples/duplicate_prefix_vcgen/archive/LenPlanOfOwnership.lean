import duplicate_prefix.ActiveReleaseRange
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.ActiveRelease
open Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Verification

/-- Per-slot ownership supplies the checked release plan for one live
protected allocation. The plan's output is the actual keyed heap update. -/
theorem planSingleOwned {K : Type}
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live[id]? = some entry)
    (tag : BorTag) (source root : UniIndex) (tags : ProtectedTags)
    (tagIndex : entry.allocation.extra.indexOfTag tag = some source)
    (roots : entry.allocation.extra.roots = #[root])
    (depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (node : TreeNode) (found : entry.allocation.extra.nodeAt source = some node)
    (unexposed : node.isExposed = false)
    (owned : ∀ position < entry.allocation.extra.locations.entries.size, ∃ slot,
      entry.allocation.extra.locations.index position = .ok slot ∧
        ReleaseOwnership entry.allocation.extra source root tags slot) :
    ∃ final, StackPopRelease.Plan tags [(id, tag)] memory final := by
  obtain ⟨after, exactRelease⟩ := releaseAll entry.allocation.extra tag source root tags
    tagIndex roots depth children node found unexposed owned
  have checked := (ProtectorReleaseWP.releasePre_iff tag tags (· = after) (fun _ _ => False)
    entry.allocation.extra).mp ((exactRelease (· = after) (fun _ _ => False)).mpr rfl)
  cases ran : entry.allocation.extra.releaseProtector tag tags with
  | mk output status =>
    rw [ran] at checked
    cases status with
    | Released =>
      refine ⟨StackPopRelease.commitTree memory id entry output, ?_⟩
      exact .live id tag entry output [] memory _ present ran (.nil _)
    | _ => exact (show False from checked).elim

#print axioms planSingleOwned
end DuplicatePrefix.ActiveRelease

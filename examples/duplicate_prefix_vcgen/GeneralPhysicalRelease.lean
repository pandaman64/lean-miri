import CanonicalCallRelease
import duplicate_prefix.ReleaseFromHolderRights

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification
open SourceDomain GeneralRangeMapOrigins RetagReleaseRights ArchiveForestProjection

/-- A live physical Bool return slot can release its protector inside an
arbitrary allocation. The premise describes the holder's existing range
permissions with the pre-pop protection set. After the pop, the caller's
saved pointer can require different permissions for the return write. -/
theorem physicalSlotReleaseOfRights
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : memory.live[id]? = some entry)
    (tag : BorTag) (holder : UniIndex) (node : TreeNode) (tags : ProtectedTags) (start : Size)
    (known : entry.allocation.extra.indexOfTag tag = some holder)
    (found : entry.allocation.extra.nodeAt holder = some node) (unexposed : node.isExposed = false)
    (coherent : CoherentForest entry.allocation.extra)
    (extent : ReleaseRange entry.allocation.extra holder start 1)
    (rights : OwnedOn (fun row => LocationRights entry.allocation.extra row tags holder)
      start.bytes (start.bytes + 1) entry.allocation.extra.locations) :
    ∃ final, StackPopRelease.Plan tags [(id, tag)] memory final := by
  let tree := entry.allocation.extra
  obtain ⟨root, roots⟩ := extent.root
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : GeneralBorrowExposure.ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index child atIndex parent edge
    obtain ⟨up, held⟩ := coherent.parentPresent index child parent atIndex edge
    exact ⟨up, held, decreases index child parent atIndex edge⟩⟩
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index data atIndex child listed
    obtain ⟨childNode, childKnown, _⟩ := (coherent.childEdges index data atIndex).2.1 child (by simpa using listed)
    exact ⟨childNode, childKnown⟩
  have allowed := ReleaseFromHolderRights.releaseOwnership tree tags holder root node found coherent roots
    start.bytes (start.bytes + 1) extent.materializedWithin
    (fun _ vacant _ inside => extent.vacantAt vacant inside) rights
  obtain ⟨after, releaseWP⟩ :=
    ActiveRelease.releaseAll tree tag holder root tags known roots depth children node found unexposed allowed
  have success := (releaseWP (· = after) (fun _ _ => False)).mpr rfl
  have result := (ProtectorReleaseWP.releasePre_iff tag tags (· = after) (fun _ _ => False) tree).mp success
  have exactRelease : tree.releaseProtector tag tags = ⟨after, .Released⟩ := by
    cases release : tree.releaseProtector tag tags with
    | mk final status =>
      rw [release] at result
      cases status <;> first | exact congrArg (fun output => BorrowTree.ProtectorReleaseResult.mk output .Released) result | contradiction
  refine ⟨StackPopRelease.commitTree memory id entry after, ?_⟩
  exact .live id tag entry after [] memory _ present exactRelease (.nil _)

#print axioms physicalSlotReleaseOfRights
end DuplicatePrefix.CanonicalCallDomain

import CanonicalCallDomain
import ZeroProtector
import duplicate_prefix.GeneralRangeMapState
import duplicate_prefix.StackPopRelease
import duplicate_prefix.RootPhysicalReturnPlan

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification

/-- A dormant, unexposed tag has no recorded location to visit on release. -/
theorem releaseDormant {tree : BorrowTree} {holder : UniIndex} {tag : BorTag}
    (dormant : ∀ position (inside : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get holder = none)
    {node : TreeNode} (tagAt : tree.indexOfTag tag = some holder)
    (nodeAt : tree.nodeAt holder = some node) (unexposed : node.isExposed = false)
    (tags : ProtectedTags) :
    tree.releaseProtector tag tags = ⟨tree, .Released⟩ := by
  have unused : ∀ position < tree.locations.entries.size, ZeroTail.protectorUnused tree holder position := by
    intro position inside
    refine ⟨tree.locations.entries[position], ?_, ?_⟩
    · exact GeneralRangeMapState.index_exact tree.locations position inside
    · intro state found
      rw [dormant position inside] at found
      contradiction
  have exactWP := (ZeroTail.release_unused tree tag tags holder tagAt node nodeAt unexposed unused
    (· = tree) (fun _ _ => False)).mpr rfl
  have result := (ProtectorReleaseWP.releasePre_iff tag tags (· = tree) (fun _ _ => False) tree).mp exactWP
  cases release : tree.releaseProtector tag tags with
  | mk final status =>
    rw [release] at result
    cases status <;> first | exact congrArg (fun output => BorrowTree.ProtectorReleaseResult.mk output .Released) result | contradiction

theorem ReleaseRange.releaseEmpty {tree holder start tag}
    (range : ReleaseRange tree holder start 0) (formed : tree.locations.WellFormed)
    {node : TreeNode} (tagAt : tree.indexOfTag tag = some holder)
    (nodeAt : tree.nodeAt holder = some node) (unexposed : node.isExposed = false)
    (tags : ProtectedTags) :
    tree.releaseProtector tag tags = ⟨tree, .Released⟩ :=
  releaseDormant (fun _ inside => range.noEmptyMaterialization formed inside) tagAt nodeAt unexposed tags

/-- Prefix the ordered release plan with a dormant protector. The exact tree
and keyed memory are preserved, including when the next protector belongs
to the same allocation. -/
theorem prependDormantRelease
    (memory final : MemoryState Provenance BorrowTree MiriMemoryKind)
    {id : AllocId} {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
    (present : memory.live[id]? = some entry) {tag : BorTag} {holder : UniIndex}
    {node : TreeNode}
    (dormant : ∀ position (inside : position < entry.allocation.extra.locations.entries.size),
      entry.allocation.extra.locations.entries[position].data.perms.get holder = none)
    (tagAt : entry.allocation.extra.indexOfTag tag = some holder)
    (nodeAt : entry.allocation.extra.nodeAt holder = some node)
    (unexposed : node.isExposed = false)
    (tags : ProtectedTags) (rows : List (AllocId × BorTag))
    (tail : StackPopRelease.Plan tags rows memory final) :
    StackPopRelease.Plan tags ((id, tag) :: rows) memory final := by
  have sameExtra : entry.allocation.setExtra entry.allocation.extra = entry.allocation := by
    cases entry.allocation
    rfl
  have sameMemory : StackPopRelease.commitTree memory id entry entry.allocation.extra = memory := by
    have sameLive : memory.live.insert id entry = memory.live := by
      apply Std.ExtTreeMap.ext_getElem?
      intro key
      by_cases equal : key = id
      · subst key
        simp [present]
      · simp [Std.ExtTreeMap.getElem?_insert, Ne.symm equal]
    simp [StackPopRelease.commitTree, sameExtra, sameLive]
  exact .live id tag entry entry.allocation.extra rows memory final present
    (releaseDormant dormant tagAt nodeAt unexposed tags) (sameMemory.symm ▸ tail)

theorem ReleaseRange.prependEmptyRelease
    (memory final : MemoryState Provenance BorrowTree MiriMemoryKind)
    {id : AllocId} {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
    (present : memory.live[id]? = some entry) {tag : BorTag} {holder : UniIndex}
    {start : ABI.Size} {node : TreeNode}
    (range : ReleaseRange entry.allocation.extra holder start 0)
    (formed : entry.allocation.extra.locations.WellFormed)
    (tagAt : entry.allocation.extra.indexOfTag tag = some holder)
    (nodeAt : entry.allocation.extra.nodeAt holder = some node)
    (unexposed : node.isExposed = false)
    (tags : ProtectedTags) (rows : List (AllocId × BorTag))
    (tail : StackPopRelease.Plan tags rows memory final) :
    StackPopRelease.Plan tags ((id, tag) :: rows) memory final :=
  prependDormantRelease memory final present (fun _ inside => range.noEmptyMaterialization formed inside)
    tagAt nodeAt unexposed tags rows tail

/-- A dedicated physical Bool slot is a specific return-place representation.
General in-bounds Bool destinations in `CanonicalCallDomain` can have a
larger allocation and a different borrow tree. -/
theorem dedicatedPhysicalSlotRelease
    {memory : MemoryState Provenance BorrowTree MiriMemoryKind} {id : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind}
    (present : memory.live[id]? = some entry) {root child : BorTag} {written : Bool}
    (tree : entry.allocation.extra = PhysicalMachineWrite.slotTree root child 1 written)
    (tags : ProtectedTags) (rootFree : tags.contains root = false)
    (childHeld : tags.contains child = true) (distinct : root ≠ child) :
    StackPopRelease.Plan tags [(id, child)] memory
      (StackPopRelease.commitTree memory id entry entry.allocation.extra) :=
  RootPhysicalReturnPlan.to_plan
    (.slot id root child 1 written entry [] memory
      (StackPopRelease.commitTree memory id entry entry.allocation.extra)
      present tree rootFree childHeld distinct (by decide) (.nil _))

/-- The admitted empty argument adds its release row only for concrete
provenance. The tail plan starts with exactly the same memory. -/
theorem Admitted.prependEmptyArgumentRelease {program options remaining tagHeadroom span before frame pointer count}
    (admitted : Admitted program options remaining tagHeadroom span before frame pointer 0 count)
    (tags : ProtectedTags) {rows : List (AllocId × BorTag)}
    {final : MemoryState Provenance BorrowTree MiriMemoryKind}
    (tail : StackPopRelease.Plan tags rows before.machine.memory final) :
    StackPopRelease.Plan tags ((argumentLedger pointer).toList ++ rows) before.machine.memory final := by
  cases provenance : pointer.provenance with
  | none => simpa [argumentLedger, provenance] using tail
  | some value =>
    cases value with
    | wildcard => simpa [argumentLedger, provenance] using tail
    | concrete id tag =>
      have empty := admitted.emptyProtector rfl
      rw [provenance] at empty
      obtain ⟨entry, holder, nodeData, tracker, base, start, present, tracked, strong,
        atTag, atNode, unexposed, coherent, cached, address, range⟩ := empty
      simpa [argumentLedger, provenance] using range.prependEmptyRelease before.machine.memory final
        present coherent.ranges atTag atNode unexposed tags rows tail

#print axioms Admitted.prependEmptyArgumentRelease
#print axioms dedicatedPhysicalSlotRelease
#print axioms prependDormantRelease
#print axioms ReleaseRange.prependEmptyRelease
#print axioms ReleaseRange.releaseEmpty
end DuplicatePrefix.CanonicalCallDomain

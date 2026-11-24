import CanonicalCallRelease
import duplicate_prefix.ReleaseFromHolderRights

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification
open SourceDomain GeneralRangeMapOrigins RetagReleaseRights ArchiveForestProjection

private theorem ByteWriteGrant.ownedOn {tree : BorrowTree} {start : Size} {source : UniIndex}
    {tags : ProtectedTags} (grant : ByteWriteGrant tree start.bytes source tags)
    (extent : ReleaseRange tree source start 1) :
    OwnedOn (fun row => LocationRights tree row tags source)
      start.bytes (start.bytes + 1) tree.locations := by
  have fits : start.bytes.toNat + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt extent.extent tree.locations.size.bytes.toNat_lt
  have endByte : (start.bytes + 1).toNat = start.bytes.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  intro position inside _ starts stops
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  have below : segment.range.start ≤ start.bytes := by
    rw [UInt64.le_iff_toNat_le]
    change segment.range.start.toNat < (start.bytes + 1).toNat at starts
    omega
  exact grant segment member below (UInt64.lt_iff_toNat_lt.mpr stops)

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

/-- The saved physical output contributes one call-owned protector. Its
actual release is derived from its grant under the pre-pop protection set.
The rest of the frame's ordered ledger is handled separately. -/
theorem PhysicalBoolDestination.outputRelease {before frame pointer length}
    (destination : PhysicalBoolDestination before frame pointer length) :
    ∃ tracker owned id tag final,
      before.machine.borrowTracker = some tracker ∧ frame.extra.borrowTracker = some owned ∧
      owned.protectedTags = (argumentLedger pointer).push (id, tag) ∧
      StackPopRelease.Plan tracker.global.protectedTags [(id, tag)] before.machine.memory final := by
  obtain ⟨place, id, entry, start, parent, base, tracker, owned, source, tag, holder,
    saved, layout, aligned, present, mutable, storage, mask, maskLength, provenance,
    fits, ptr, nonnull, address, addressFits, cache, tracked, frameTracker, ledger,
    protection, coherent, sourceIndex, sourceNode, tagIndex, tagNode, extent, grant, _⟩ :=
    destination.storage
  obtain ⟨node, found, _, _, unexposed⟩ := tagNode
  obtain ⟨final, release⟩ := physicalSlotReleaseOfRights before.machine.memory id entry present
    tag holder node tracker.global.protectedTags start tagIndex found unexposed coherent extent
    (grant.ownedOn extent)
  exact ⟨tracker, owned, id, tag, final, tracked, frameTracker, ledger, release⟩

/-- For an empty input, the complete ordered physical-root release plan
follows from the admitted initial state. The optional dormant slice row
preserves memory before releasing the independently owned output. -/
theorem Admitted.emptyPhysicalRelease {program options remaining headroom span before frame pointer count}
    (admitted : Admitted program options remaining headroom span before frame pointer 0 count)
    (destination : PhysicalBoolDestination before frame pointer 0) :
    ∃ tracker owned final,
      before.machine.borrowTracker = some tracker ∧ frame.extra.borrowTracker = some owned ∧
      StackPopRelease.Plan tracker.global.protectedTags owned.protectedTags.toList before.machine.memory final := by
  obtain ⟨tracker, owned, id, tag, final, tracked, frameTracker, ledger, output⟩ := destination.outputRelease
  refine ⟨tracker, owned, final, tracked, frameTracker, ?_⟩
  simpa [ledger] using admitted.prependEmptyArgumentRelease tracker.global.protectedTags output

#print axioms physicalSlotReleaseOfRights
#print axioms PhysicalBoolDestination.outputRelease
#print axioms Admitted.emptyPhysicalRelease
end DuplicatePrefix.CanonicalCallDomain

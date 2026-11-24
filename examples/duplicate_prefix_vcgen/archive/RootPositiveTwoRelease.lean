import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.RootPositiveTwoRelease
open Miri Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows

/-- The physical return emits the argument-holder release first. Lookup of
the disjoint return allocation survives that tree write. Global protection
is unchanged until both source release visits have completed. -/
theorem plan
    {K : Type} {memory : MemoryState Provenance BorrowTree K}
    {bufferId slotId : AllocId} {bufferTag slotTag : BorTag}
    {buffer slot : LocalAllocation Provenance BorrowTree K}
    {bufferTree slotTree : BorrowTree}
    (tracker : MachineHooks.BorrowState) (frame : FrameState)
    (ledger : frame.protectedTags = #[(bufferId, bufferTag), (slotId, slotTag)])
    (different : slotId ≠ bufferId)
    (bufferLive : memory.live[bufferId]? = some buffer)
    (slotLive : memory.live[slotId]? = some slot)
    (bufferRelease : buffer.allocation.extra.releaseProtector bufferTag tracker.global.protectedTags =
      ⟨bufferTree, .Released⟩)
    (slotRelease : slot.allocation.extra.releaseProtector slotTag tracker.global.protectedTags =
      ⟨slotTree, .Released⟩) :
    let afterBuffer := StackPopRelease.commitTree memory bufferId buffer bufferTree
    let released := StackPopRelease.commitTree afterBuffer slotId slot slotTree
    StackPopRelease.Plan tracker.global.protectedTags frame.protectedTags.toList memory released ∧
    released.live[bufferId]? = some {buffer with allocation := buffer.allocation.setExtra bufferTree} ∧
    released.live[slotId]? = some {slot with allocation := slot.allocation.setExtra slotTree} ∧
    (tracker.global.endCall frame).protectedTags.contains bufferTag = false ∧
    (tracker.global.endCall frame).protectedTags.contains slotTag = false := by
  dsimp only
  let afterBuffer := StackPopRelease.commitTree memory bufferId buffer bufferTree
  let released := StackPopRelease.commitTree afterBuffer slotId slot slotTree
  have slotAfterBuffer := StackPopRelease.lookup_commit_other memory bufferId slotId buffer slot
    bufferTree different slotLive
  constructor
  · rw [ledger]
    exact .live bufferId bufferTag buffer bufferTree [(slotId,slotTag)] memory released bufferLive bufferRelease
      (.live slotId slotTag slot slotTree [] afterBuffer released slotAfterBuffer slotRelease (.nil released))
  refine ⟨?_, StackPopRelease.lookup_commit_same afterBuffer slotId slot slotTree, ?_, ?_⟩
  · exact StackPopRelease.lookup_commit_other afterBuffer slotId bufferId slot
      {buffer with allocation := buffer.allocation.setExtra bufferTree} slotTree (Ne.symm different)
      (StackPopRelease.lookup_commit_same memory bufferId buffer bufferTree)
  · simp [StackPopRelease.end_call_contains, ledger]
  · simp [StackPopRelease.end_call_contains, ledger]

#print axioms plan
end DuplicatePrefix.RootPositiveTwoRelease

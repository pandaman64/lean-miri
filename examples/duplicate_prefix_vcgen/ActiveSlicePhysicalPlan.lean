import OrderedAliasReturnRelease

namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.Interpreter
open SourceDomain ArchiveForestProjection ScopedPhysicalRelease RetagReleaseFootprint RetagReleaseRights GeneralRangeMapOrigins

set_option maxRecDepth 65536

/-- A separated return still uses the exact source release, including when
the source tree has stored inactive permission entries. -/
theorem RetainedSlice.physicalActivePlanDistinct
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (source : RetainedSlice machine) (owned : FrameState) (slotId : AllocId) (slotTag : BorTag)
    (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind) (afterSlot : BorrowTree)
    (ledger : owned.protectedTags = #[(source.id,source.tag),(slotId,slotTag)])
    (apart : source.id ≠ slotId) (present : machine.memory.live[slotId]? = some slot)
    (slotReleased : slot.allocation.extra.releaseProtector slotTag source.tracker.global.protectedTags =
      ⟨afterSlot,.Released⟩)
    (coherent : CoherentForest source.entry.allocation.extra)
    (lower upper : UInt64) (scope : VisitsWithin source.entry.allocation.extra source.source lower.toNat upper.toNat)
    (vacant : VacantRows source.entry.allocation.extra)
    (rights : OwnedOn (fun row => LocationRights source.entry.allocation.extra row
      source.tracker.global.protectedTags source.source) lower upper source.entry.allocation.extra.locations) :
    ∃ final : MemoryState Provenance BorrowTree MiriMemoryKind,
      StackPopRelease.Plan source.tracker.global.protectedTags owned.protectedTags.toList machine.memory final ∧
      final.live[slotId]? = some {slot with allocation := slot.allocation.setExtra afterSlot} := by
  let tree := source.entry.allocation.extra
  let tags := source.tracker.global.protectedTags
  have prepared := accessedAuthorization tree tags source.source source.root source.node source.found coherent
    source.roots lower upper scope vacant rights
  obtain ⟨after,released,_,_,_⟩ := releaseFramesRows tree source.tag source.source source.root tags source.indexed
    coherent source.roots source.node source.found source.unexposed lower.toNat upper.toNat scope prepared
    (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
  let middle := StackPopRelease.commitTree machine.memory source.id source.entry after
  let final := StackPopRelease.commitTree middle slotId slot afterSlot
  have sameSlot := StackPopRelease.lookup_commit_other machine.memory source.id slotId source.entry slot after
    (Ne.symm apart) present
  have tail : StackPopRelease.Plan tags [(slotId,slotTag)] middle final :=
    .live slotId slotTag slot afterSlot [] middle final sameSlot slotReleased (.nil final)
  have all : StackPopRelease.Plan tags [(source.id,source.tag),(slotId,slotTag)] machine.memory final :=
    .live source.id source.tag source.entry after [(slotId,slotTag)] machine.memory final source.present released tail
  exact ⟨final,by simpa [ledger] using all,StackPopRelease.lookup_commit_same middle slotId slot afterSlot⟩

#print axioms RetainedSlice.physicalActivePlanDistinct
end DuplicatePrefix.RootZeroShallowReturn

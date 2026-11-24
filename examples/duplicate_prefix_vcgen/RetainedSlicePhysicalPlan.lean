import RetainedSlice
import duplicate_prefix.StackPopRelease
import duplicate_prefix.CopyHolderRelease

namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows
open SourceDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Release the two independent ledgers in their actual frame order. The
source footprint is obtained from its final tree, be it the original tree,
the length-read tree, or a tree changed by the copy. -/
theorem RetainedSlice.physicalPlan
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser} (source : RetainedSlice machine)
    (owned : FrameState) (slotId : AllocId) (slotTag : BorTag)
    (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind) (afterSlot : BorrowTree)
    (ledger : owned.protectedTags = #[(source.id,source.tag),(slotId,slotTag)])
    (apart : source.id ≠ slotId) (present : machine.memory.live[slotId]? = some slot)
    (slotReleased : slot.allocation.extra.releaseProtector slotTag source.tracker.global.protectedTags =
      ⟨afterSlot,.Released⟩)
    (coherent : CoherentForest source.entry.allocation.extra)
    (lower upper : UInt64)
    (footprint : CopyHolderRights.Footprint source.entry.allocation.extra source.tracker.global.protectedTags
      source.source source.source lower upper) :
    ∃ final : MemoryState Provenance BorrowTree MiriMemoryKind,
      StackPopRelease.Plan source.tracker.global.protectedTags owned.protectedTags.toList machine.memory final ∧
      final.live[slotId]? = some {slot with allocation := slot.allocation.setExtra afterSlot} := by
  obtain ⟨afterSource, sourceRelease⟩ := CopyHolderRelease.release source.entry.allocation.extra
    source.tracker.global.protectedTags source.tag source.source source.source source.root lower upper
    coherent source.roots source.node source.found source.unexposed source.indexed footprint
  let updated := StackPopRelease.commitTree machine.memory source.id source.entry afterSource
  let final := StackPopRelease.commitTree updated slotId slot afterSlot
  have stillLive : updated.live[slotId]? = some slot :=
    StackPopRelease.lookup_commit_other machine.memory source.id slotId source.entry slot afterSource
      (Ne.symm apart) present
  have tail : StackPopRelease.Plan source.tracker.global.protectedTags [(slotId,slotTag)] updated final :=
    .live slotId slotTag slot afterSlot [] updated final stillLive slotReleased (.nil final)
  have both : StackPopRelease.Plan source.tracker.global.protectedTags
      [(source.id,source.tag),(slotId,slotTag)] machine.memory final :=
    .live source.id source.tag source.entry afterSource [(slotId,slotTag)] machine.memory final
      source.present sourceRelease tail
  refine ⟨final, ?_, StackPopRelease.lookup_commit_same updated slotId slot afterSlot⟩
  simpa [ledger] using both

#print axioms RetainedSlice.physicalPlan
end DuplicatePrefix.RootZeroShallowReturn

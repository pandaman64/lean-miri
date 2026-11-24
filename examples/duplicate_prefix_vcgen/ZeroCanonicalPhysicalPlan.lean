import CanonicalCachedReturn
import PhysicalEndCall
import duplicate_prefix.CopyHolderRelease
import duplicate_prefix.RootWindowPhysicalReturn

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Verification Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open PreparedArguments SourceDomain ArchiveForestProjection RetagReleaseFootprint GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame
local notation "Heap" => MemoryState Provenance BorrowTree MiriMemoryKind
local notation "Entry" => LocalAllocation Provenance BorrowTree MiriMemoryKind

/-- For count zero the data allocation has not been accessed by the source.
Its live or dormant protector is released before the independent output row. -/
theorem Admitted.zeroPhysicalPlan {program options remaining headroom span before frame pointer length}
    (admitted : Admitted program options remaining headroom span before frame pointer length 0)
    (tracker : MachineHooks.BorrowState) (tracked : before.machine.borrowTracker = some tracker)
    (owned : FrameState) (ledger : frame.extra.borrowTracker = some owned)
    (slotId : AllocId) (slotTag : BorTag) (slot : Entry) (afterSlot : BorrowTree)
    (ledgerRows : owned.protectedTags = (argumentLedger pointer).push (slotId,slotTag))
    (present : before.machine.memory.live[slotId]? = some slot)
    (separate : length ≠ 0 → ∀ id tag, pointer.provenance = some (.concrete id tag) → id ≠ slotId)
    (slotReleased : slot.allocation.extra.releaseProtector slotTag tracker.global.protectedTags = ⟨afterSlot,.Released⟩) :
    ∃ final : Heap,
      StackPopRelease.Plan tracker.global.protectedTags owned.protectedTags.toList before.machine.memory final ∧
      final.live[slotId]? = some {slot with allocation := slot.allocation.setExtra afterSlot} := by
  by_cases empty : length = 0
  · subst length
    let final := StackPopRelease.commitTree before.machine.memory slotId slot afterSlot
    have output : StackPopRelease.Plan tracker.global.protectedTags [(slotId,slotTag)] before.machine.memory final :=
      .live slotId slotTag slot afterSlot [] before.machine.memory final present slotReleased (.nil final)
    have all := admitted.prependEmptyArgumentRelease tracker.global.protectedTags output
    refine ⟨final, ?_, StackPopRelease.lookup_commit_same before.machine.memory slotId slot afterSlot⟩
    simpa [ledgerRows] using all
  · obtain ⟨storage, tag, _, region, scopeOwner, provenance, _, _, scopeLedger, _, _, source, extent⟩ :=
      admitted.sliceProtector empty
    have sameTracker : region.tracker = tracker := Option.some.inj (region.tracked.symm.trans tracked)
    obtain ⟨holderNode, found, hidden⟩ := source
    obtain ⟨root, roots⟩ := extent.root
    let tree := storage.entry.allocation.extra
    have owners := ExclusiveRegion.ownsRows region extent
    rw [sameTracker] at owners
    have footprint : CopyHolderRights.Footprint tree tracker.global.protectedTags region.source region.source
        storage.relativeStart.bytes (storage.relativeStart.bytes+length) :=
      ⟨owners,owners,extent.materializedWithin,fun _ absent _ valid => extent.vacantAt absent valid⟩
    obtain ⟨afterSource, sourceRelease⟩ := CopyHolderRelease.release tree tracker.global.protectedTags tag
      region.source region.source root storage.relativeStart.bytes (storage.relativeStart.bytes+length)
      region.coherent roots holderNode found hidden region.tagKnown footprint
    have apart := separate empty storage.id tag provenance
    let updated := StackPopRelease.commitTree before.machine.memory storage.id storage.entry afterSource
    let final := StackPopRelease.commitTree updated slotId slot afterSlot
    have stillLive : updated.live[slotId]? = some slot :=
      (StackPopRelease.lookup_commit_other before.machine.memory storage.id slotId storage.entry slot afterSource
        (Ne.symm apart) present)
    have tail : StackPopRelease.Plan tracker.global.protectedTags [(slotId,slotTag)] updated final :=
      .live slotId slotTag slot afterSlot [] updated final stillLive slotReleased (.nil final)
    have steps : StackPopRelease.Plan tracker.global.protectedTags
        [(storage.id,tag),(slotId,slotTag)] before.machine.memory final :=
      .live storage.id tag storage.entry afterSource [(slotId,slotTag)] before.machine.memory final
        storage.live sourceRelease tail
    refine ⟨final, ?_, StackPopRelease.lookup_commit_same updated slotId slot afterSlot⟩
    simpa [ledgerRows, argumentLedger, provenance] using steps

#print axioms Admitted.zeroPhysicalPlan
end DuplicatePrefix.CanonicalCallDomain

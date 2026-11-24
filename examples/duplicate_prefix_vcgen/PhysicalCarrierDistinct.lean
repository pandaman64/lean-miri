import CanonicalCallDomain
import duplicate_prefix.AllocationBacktrace

namespace DuplicatePrefix.RootPhysicalCarrierTransport

open Miri Miri.ABI Miri.Memory Miri.Input Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalCallDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- Preparing the copy does not alter a disjoint saved result allocation.
Reframe only its original window and protector grants across the prefix. -/
theorem transportDistinct
    (before after : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (entry current : CompilerFrameContext.ActualFrame)
    (pointer : Pointer (Option Provenance)) (length : UInt64)
    (argument : AllocId)
    (disjoint : ∀ place id tag, entry.returnPlace = .memory place →
      place.mplace.ptr.provenance = some (.concrete id tag) → id ≠ argument)
    (tracker retained : MachineHooks.BorrowState)
    (tracked : before.machine.borrowTracker = some tracker)
    (enabled : after.machine.borrowTracker = some retained)
    (protections : retained.global.protectedTags = tracker.global.protectedTags)
    (samePlace : current.returnPlace = entry.returnPlace)
    (sameLedger : current.extra.borrowTracker = entry.extra.borrowTracker)
    (addresses : after.machine.user.addresses = before.machine.user.addresses)
    (unrelated : ∀ key, key ≠ argument → after.machine.memory.live[key]? = before.machine.memory.live[key]?)
    (destination : PhysicalBoolDestination before entry pointer length) :
    PhysicalBoolDestination after current pointer length := by
  obtain ⟨place,id,row,start,tag,base,recovered,owned,parent,child,childIndex,
    saved,layout,alignment,live,mutable,bytes,mask,maskLen,provenance,fits,ptr,nonnull,address,capacity,cached,
    active,ownership,ledger,held,coherent,parentKey,parentData,childKey,childData,extent,grant,retainedGrant⟩ :=
    destination.storage
  have same : recovered = tracker := Option.some.inj (active.symm.trans tracked)
  subst recovered
  have endCall : (retained.global.endCall owned).protectedTags = (tracker.global.endCall owned).protectedTags := by
    unfold GlobalState.endCall
    rw [protections]
  have different : length ≠ 0 → ∀ sourceId srcTag,
      pointer.provenance = some (.concrete sourceId srcTag) → sourceId ≠ id := by
    first | exact retainedGrant | exact retainedGrant.2
  constructor
  refine ⟨place,id,row,start,tag,base,retained,owned,parent,child,childIndex,
    samePlace.trans saved,layout,alignment,(unrelated id (disjoint place id tag saved ptr)).trans live,
    mutable,bytes,mask,maskLen,provenance,fits,ptr,nonnull,address,capacity,(by rw [addresses]; exact cached),
    enabled,sameLedger.trans ownership,ledger,(by rw [protections];exact held),coherent,parentKey,parentData,childKey,
    childData,extent,(by first | rw [protections]; exact grant | rw [endCall]; exact grant),?_⟩
  first
  | exact different
  | exact ⟨by rw [endCall]; exact retainedGrant.1, different⟩

#print axioms transportDistinct
end DuplicatePrefix.RootPhysicalCarrierTransport

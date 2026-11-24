import CanonicalCallDomain
import duplicate_prefix.AllocationBacktrace

namespace DuplicatePrefix.RootPhysicalCarrierTransport

open Miri Miri.ABI Miri.Memory Miri.Input Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalCallDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- Preparing the copy does not alter a disjoint saved result allocation.
Reframe only its original window and protector grants across the prefix. -/
theorem transport
    (before after : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (entry current : CompilerFrameContext.ActualFrame)
    (pointer : Pointer (Option Provenance)) (length : UInt64)
    (argument : AllocId) (holder : BorTag) (nonempty : length ≠ 0)
    (concrete : pointer.provenance = some (.concrete argument holder))
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
    samePlace.trans saved,layout,alignment,(unrelated id (different nonempty argument holder concrete).symm).trans live,
    mutable,bytes,mask,maskLen,provenance,fits,ptr,nonnull,address,capacity,(by rw [addresses]; exact cached),
    enabled,sameLedger.trans ownership,ledger,(by rw [protections];exact held),coherent,parentKey,parentData,childKey,
    childData,extent,(by first | rw [protections]; exact grant | rw [endCall]; exact grant),?_⟩
  first
  | exact different
  | exact ⟨by rw [endCall]; exact retainedGrant.1, different⟩

/-- The stock extras record for a live disjoint row survives preparation.
The diagnostic backtrace is recovered from the same saved extras lookup. -/
theorem backing
    (before after : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (headroom : Nat)
    (profile : AllocationProfile before frame headroom)
    (argument : AllocId)
    (unrelated : ∀ key, key ≠ argument → after.machine.memory.live[key]? = before.machine.memory.live[key]?)
    (same : after.machine.user.payload.payload.user.runtime.extras =
      before.machine.user.payload.payload.user.runtime.extras)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (different : id ≠ argument) (present : after.machine.memory.live[id]? = some entry) :
    (after.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id)) =
      some (id,{weakMemory := none,backtrace := (AllocationBacktrace.get
        after.machine.user.payload.payload.user.runtime.extras.allocations id)}) := by
  have initial : before.machine.memory.live[id]? = some entry := (unrelated id different).symm.trans present
  have mem : before.machine.memory.live.contains id = true := by
    simp [Std.ExtTreeMap.contains_eq_isSome_getElem?, initial]
  obtain ⟨extra, found, weak, sync⟩ := profile.extras id mem
  have backtrace := AllocationBacktrace.of_lookup found
  rw [same,backtrace,found]
  congr 2
  cases extra
  simp_all

#print axioms backing
#print axioms transport
end DuplicatePrefix.RootPhysicalCarrierTransport

import CanonicalCallDomain
import duplicate_prefix.RootWindowPhysicalReturn

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows

set_option maxRecDepth 65536
set_option maxHeartbeats 2500000

local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Entry" => LocalAllocation Provenance BorrowTree MiriMemoryKind

private theorem rebuildPhysicalPointer (pointer : Pointer (Option Provenance)) :
    pointer = Pointer.new pointer.provenance (Size.ofBytes pointer.offset.bytes) := by
  cases pointer with
  | mk offset provenance => cases offset; rfl

/-- Reuse the canonical physical slot geometry after the actual release
plan has committed its Tree Borrows state without changing its byte storage. -/
def physicalWindowAfterRelease
    (machine : MachineState) (place : MPlaceTy Provenance) (id : AllocId) (tag : BorTag)
    (base : UInt64) (relative : Size) (entry : Entry) (tree : BorrowTree)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (aligned : place.mplace.misaligned = none)
    (live : machine.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra tree})
    (cached : machine.user.addresses.baseAddr.find? (·.allocId == id) = some ⟨id, base⟩)
    (mutable : entry.allocation.mutability = .Mut)
    (bytes : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (mask : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (fits : relative.bytes < entry.allocation.byteSize.bytes)
    (identity : place.mplace.ptr.provenance = some (.concrete id tag))
    (address : place.mplace.ptr.offset.bytes.toNat = base.toNat + relative.bytes.toNat)
    (capacity : base.toNat + entry.allocation.byteSize.bytes.toNat < 2^64) :
    PhysicalBoolWindowWrite.Window machine place := by
  have within := UInt64.lt_iff_toNat_lt.mp fits
  have fitAddress : base.toNat + relative.bytes.toNat < 2^64 := by omega
  have sum : (base+relative.bytes).toNat = base.toNat + relative.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fitAddress]
  have offset : place.mplace.ptr.offset.bytes = base+relative.bytes := UInt64.toNat.inj (address.trans sum.symm)
  exact {
    layout, aligned, id, tag, live, base
    entry := {entry with allocation := entry.allocation.setExtra tree}
    offset := relative.bytes
    capacity := entry.allocation.byteSize.bytes
    cachedBase := cached
    pointer := (rebuildPhysicalPointer place.mplace.ptr).trans (by rw [identity,offset])
    bounds := by omega
    size := by
      change entry.allocation.byteSize = Size.ofBytes entry.allocation.byteSize.bytes
      cases entry.allocation.byteSize
      rfl
    bytes, mutable
    maskValid := mask
    maskLength
    provenance }

theorem ordinaryPhysicalExtras
    {program options remaining headroom span before frame pointer length count}
    (admitted : Admitted program options remaining headroom span before frame pointer length count)
    (machine : MachineState) (id : AllocId) (entry : Entry)
    (live : before.machine.memory.live[id]? = some entry)
    (unchanged : machine.user.payload.payload.user.runtime.extras =
      before.machine.user.payload.payload.user.runtime.extras) :
    let context := (DuplicatePrefixPhysicalContexts.canonical options remaining span).writeContext
    (context.extras.get machine.user).allocations.find? (·.1 == id) =
      some (id,{weakMemory := none, backtrace := (AllocationBacktrace.get
        ((context.extras.get machine.user).allocations) id)}) := by
  intro context
  let rows := machine.user.payload.payload.user.runtime.extras.allocations
  change rows.find? (·.1 == id) = some (id,{weakMemory := none, backtrace := AllocationBacktrace.get rows id})
  dsimp only [rows]
  rw [unchanged]
  obtain ⟨extra, present, weak, sync⟩ := admitted.allocations.extras id
    (MemoryCopyBridge.live_any_of_present before.machine.memory id entry live)
  rw [present, AllocationBacktrace.of_lookup present]
  cases extra
  simp_all

#print axioms physicalWindowAfterRelease
#print axioms ordinaryPhysicalExtras

end DuplicatePrefix.CanonicalCallDomain

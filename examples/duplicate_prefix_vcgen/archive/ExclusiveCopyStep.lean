import duplicate_prefix.ExclusiveCopyRanges
import duplicate_prefix.GeneralBorrowScopedCopyHelperMemory

namespace DuplicatePrefix.ArchiveForestProjection

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open PreparedArguments SourceDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- Changing only the active frame retains the actual keyed storage witness. -/
def reframeStorage {K U : Type} {before after : MachineHooks.State K U}
    {length : UInt64} (storage : InitializedRegion before length)
    (sameMachine : after.machine = before.machine) : InitializedRegion after length :=
  { storage with live := by rw [sameMachine]; exact storage.live }

/-- Changing only the active frame retains the existing borrow grant. -/
def reframeRights {K U : Type} {before after : MachineHooks.State K U}
    {length : UInt64} {tag : BorTag} {storage : InitializedRegion before length}
    (rights : ExclusiveRegion before length storage tag) (sameMachine : after.machine = before.machine) :
    ExclusiveRegion after length (reframeStorage storage sameMachine) tag :=
  { rights with tracked := by rw [sameMachine]; exact rights.tracked }

/-- The exact exported helper's copy instruction copies the shifted byte
window. Both pointer operands and permission proofs refer to the same active
frame, tracker, concrete tag and keyed allocation. -/
theorem exclusive_copy_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.copyHelper.body)
    (location : frame.location = .mir ⟨7,8⟩)
    (base sliceLen n : UInt64)
    (storage : InitializedRegion (Storage.withCurrent frames frame machine) sliceLen) (tag : BorTag)
    (exclusive : ExclusiveRegion (Storage.withCurrent frames frame machine) sliceLen storage tag)
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (rangeCapacity : storage.relativeStart.bytes.toNat + sliceLen.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat)
    (positive : 0 < n)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (maskValid : InitMaskCopy.WellFormed storage.entry.allocation.initializationMask)
    (maskLen : storage.entry.allocation.initializationMask.len = storage.entry.allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn storage.entry.allocation.initializationMask
      (Size.ofBytes storage.relativeStart.bytes) (Size.ofBytes (storage.relativeStart.bytes + n)))
    (valid : ProvenanceCopy.WellFormed storage.entry.allocation.provenanceMap storage.entry.allocation.len)
    (storageFits : storage.entry.allocation.len + 64 < 18446744073709551616)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) =
      some (storage.id, { weakMemory := none, backtrace := AllocationBacktrace.get (machine.user.payload.payload.user.runtime.extras.allocations) (storage.id) }))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) =
      some ⟨storage.id, base⟩)
    (bounded : n ≤ (PreparedContracts.actualConfig options () remaining span).projection.maxSizeOfVal.bytes)
    (valid14 : (14 : MIR.LocalId) < frame.locals.size)
    (valid15 : (15 : MIR.LocalId) < frame.locals.size)
    (valid16 : (16 : MIR.LocalId) < frame.locals.size)
    (live14 : frame.locals[14].value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes)))))))
    (live15 : frame.locals[15].value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+(storage.relativeStart.bytes+n))))))))
    (live16 : frame.locals[16].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache14 : frame.locals[14].layout = some CopyCompilerFacts.sourcePointerLayout)
    (cache15 : frame.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (cache16 : frame.locals[16].layout = some RootCompilerFacts.usizeLayout)
    (localClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    let state := Storage.withCurrent frames frame machine
    let allocation := storage.entry.allocation
    let offset := storage.relativeStart.bytes
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read exclusive.tracker.global.protectedTags .VisitChildrenOfAccessed
    let readState := CanonicalCopy.replaceAllocation state storage.id storage.entry.kind (allocation.setExtra readAccess.tree)
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write exclusive.tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeState := CanonicalCopy.replaceAllocation readState storage.id storage.entry.kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
    ∃ result,
      ExecutionMachine.step config limits () state =
        (Storage.withCurrent frames {frame with location := .mir ⟨7,9⟩}
          (CanonicalCopy.replaceAllocation writeState storage.id storage.entry.kind result).machine,.ok true) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧
      result.extra = writeAccess.tree ∧
      CopyProvenanceBounds.AllocationBacking result ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len := by
  have borrow : ScopedCopyAccess.Completed storage.entry.allocation.extra
      exclusive.tracker.global.protectedTags tag storage.relativeStart.bytes n :=
    exclusive_copy_permissions storage exclusive root roots n copyBounds rangeCapacity
  exact GeneralBorrowScopedCopyHelperMemory.actual_initialized_copy_step options limits remaining span debugOff
    frames frame machine sourceBody location exclusive.tracker storage.id tag base storage.relativeStart.bytes
    sliceLen n storage.entry.kind storage.entry.allocation positive storage.fits copyBounds storage.backed maskValid
    maskLen initialized valid storageFits storage.writable noClocks noBackend exclusive.tracked extras storage.live
    cached borrow bounded valid14 valid15 valid16 live14 live15 live16 cache14 cache15 cache16 localClocks ghost

#print axioms exclusive_copy_step
end DuplicatePrefix.ArchiveForestProjection

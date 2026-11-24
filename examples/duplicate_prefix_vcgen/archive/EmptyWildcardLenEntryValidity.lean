import duplicate_prefix.EmptyWildcardLocalValidator
import duplicate_prefix.EmptyReferenceInfo
namespace DuplicatePrefix.EmptyWildcardLenEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts EmptyReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem wildcard_zero
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : EmptyReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (unresolved : EmptyWildcardLocalValidator.Unresolved machine.user.addresses machine.memory address)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false)
    (validInstance : frame.functionInstance < PreparedReflection.actual.program.input.instances.size := by
      first | assumption | (rw [callee]; with_unfolding_all decide +kernel) | (rw [function]; with_unfolding_all decide +kernel) | (rw [fnInstance]; with_unfolding_all decide +kernel) | with_unfolding_all decide +kernel) :
    let cfg := config options remaining span
    let resultMachine := EmptyReferenceAllocation.allocatedMachine machine tracker fresh
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {frame with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  have info := EmptyReferenceInfo.facts options remaining span ctx true
  have result := EmptyWildcardLocalValidator.zero_unresolved options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry info.dereference info.sized info.readable "&[u8]" info.named info.classified
    address nonzero frames frame machine tracker enabled mode fresh localId valid (by rw [CanonicalConfigFacts.actual_access_runtime options () remaining span]; exact live) cached ghost shallow metadata notConstructed
    (sharedPolicy true) info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen shared_entry_policy validInstance unresolved
  rw [CanonicalConfigFacts.actual_access_runtime options () remaining span] at result
  exact result

#print axioms wildcard_zero
end
end DuplicatePrefix.EmptyWildcardLenEntryValidity

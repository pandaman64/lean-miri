import duplicate_prefix.CopyRootCurrentReadyFacts
import duplicate_prefix.CopyOwnershipTransport
import duplicate_prefix.ExclusiveCopyCurrentCall

namespace DuplicatePrefix.CopyRootPositiveRoundtrip
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.DataStructures
open PreparedArguments SourceDomain
set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

noncomputable def fromPtr (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (id : AllocId) (tag : BorTag) (address : UInt64) : Scalar Provenance :=
  Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id tag) (Size.ofBytes address))

/-- The actual root copy call, both guards, and the actual positive copy and
return, with the same structural source grant carried into the intrinsic. -/
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length n base : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent frames caller machine) length)
    (right : ExclusiveRegion (Storage.withCurrent frames caller machine) length storage tag)
    (input : CopyRootEntry.Input options limits remaining span frames caller machine
      (fromPtr options remaining span storage.id tag (base+storage.relativeStart.bytes))
      (fromPtr options remaining span storage.id tag (base+(storage.relativeStart.bytes+n))) n)
    (statementFuel : limits.validation = input.fuel+1)
    (mode : right.tracker.retagMode = .Default)
    (positive : 0 < n)
    (copyBounds : n.toNat+n.toNat ≤ length.toNat)
    (maskLen : storage.entry.allocation.initializationMask.len = storage.entry.allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed storage.entry.allocation.initializationMask)
    (initialized : InitMaskCopy.InitializedOn storage.entry.allocation.initializationMask
      storage.relativeStart (Size.ofBytes (storage.relativeStart.bytes+n)))
    (valid : ProvenanceCopy.WellFormed storage.entry.allocation.provenanceMap storage.entry.allocation.len)
    (storageFits : storage.entry.allocation.len + 64 < 18446744073709551616)
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (rangeCapacity : storage.relativeStart.bytes.toNat + length.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat)
    (bounded : n ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id,base⟩)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) =
      some (storage.id, { weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) storage.id) })) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let callerCached := CopyUncachedCall.cachedCaller caller input.valid
    let slot : 18 < callerCached.locals.size := by
      simpa [callerCached,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using input.valid
    let resumed := {PointerAddCurrentReturn.writeFrame callerCached 18 .uninit slot with location := .mir ⟨9,0⟩}
    let offset := storage.relativeStart.bytes
    ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames resumed finalMachine) ∧
      finalMachine.memory.live[storage.id]? = some ⟨storage.entry.kind,result⟩ ∧
      result.byteSize = storage.entry.allocation.byteSize ∧ result.len = storage.entry.allocation.len ∧
      AllocationCopy.snapshot result =
        (AllocationCopy.snapshot storage.entry.allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot storage.entry.allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot storage.entry.allocation).extract (offset+n+n).toNat storage.entry.allocation.len := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let source := fromPtr options remaining span storage.id tag (base+storage.relativeStart.bytes)
  let destination := fromPtr options remaining span storage.id tag (base+(storage.relativeStart.bytes+n))
  let rootFrame := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine source destination n input
  let blocked := CopyRootCurrentGuardBody.returnedCopy options limits remaining span frames caller machine source destination n input
  have beforeSize := CopyRootCurrentGuardBody.returned_metadata options limits remaining span frames caller machine source destination n input
  have v4 : 4 < blocked.locals.size := by rw [beforeSize.2.2.2.2.1]; decide
  let ready := CopyRootCurrentGuardReach.ready blocked v4
  have equivTracker : input.tracker = right.tracker :=
    Option.some.inj (input.tracked.symm.trans right.tracked)
  have inputMode : input.tracker.retagMode = .Default := by rw [equivTracker]; exact mode
  obtain ⟨copyMachine,thread,history,preserved,active⟩ :=
    CopyRootCurrentGuardReach.from_call options limits remaining span frames caller machine source destination n input statementFuel inputMode
  have rows := CopyRootCurrentGuardBody.returned_locals options limits remaining span frames caller machine source destination n input
  have shape := CopyRootCurrentReadyFacts.ready_slots blocked v4 source destination n rows
  let owned : InitializedRegion (Storage.withCurrent (frames.push rootFrame) ready copyMachine) length :=
    CopyOwnershipTransport.storageAfter storage preserved.memory
  let rights : ExclusiveRegion (Storage.withCurrent (frames.push rootFrame) ready copyMachine) length owned tag :=
    CopyOwnershipTransport.rightsAfter right preserved.memory preserved.tracker
  have readyDirect : CopyHelperCleanup.AllImmediate ready :=
    CopyRootCurrentReadyFacts.direct blocked v4
      (CopyRootCurrentGuardBody.returned_all_immediate options limits remaining span frames caller machine source destination n input)
  obtain ⟨body,identity,callee,pc,bsize,dest,continuation,va,clocks,borrow⟩ := beforeSize
  have s0 := (Array.getElem?_eq_some_iff.mp shape.zero).2
  have s1 := (Array.getElem?_eq_some_iff.mp shape.sourceAt).2
  have s2 := (Array.getElem?_eq_some_iff.mp shape.destinationAt).2
  have s3 := (Array.getElem?_eq_some_iff.mp shape.countAt).2
  have s4 := (Array.getElem?_eq_some_iff.mp shape.unit).2
  have s5 := (Array.getElem?_eq_some_iff.mp shape.condition).2
  have s14 := (Array.getElem?_eq_some_iff.mp shape.temporarySource).2
  have s15 := (Array.getElem?_eq_some_iff.mp shape.temporaryDestination).2
  have s16 := (Array.getElem?_eq_some_iff.mp shape.temporaryCount).2
  have callerValid : 18 < rootFrame.locals.size := by
    simpa [rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
      using input.valid
  have callerLive : rootFrame.locals[18].value = .live (.immediate input.old) := by
    simpa [rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
      using input.live
  have callerCache : rootFrame.locals[18].layout = some CopyHelperUnit.layout := by
    simp [rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have physical : ready.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size rootFrame 18 CopyHelperUnit.layout := by
    change blocked.returnPlace.toRuntimePlace = _
    rw [dest]
    rfl
  have startEq : (Size.ofBytes storage.relativeStart.bytes) = storage.relativeStart := rfl
  obtain ⟨result,_,finalMachine,_,copied,present,sized,bytes,tree,_,snapshot⟩ :=
    ArchiveForestProjection.exclusive_to_caller options limits remaining span input.debug input.fuel input.validationFuel
      frames rootFrame ready copyMachine body identity callee rfl shape.size right.tracker storage.id tag
      base storage.relativeStart.bytes length n storage.entry.kind storage.entry.allocation
      positive storage.fits copyBounds storage.backed maskValid maskLen (by rw [startEq]; exact initialized)
      valid storageFits storage.writable (preserved.race.trans input.noRace) (preserved.backend.trans input.backend)
      rights.tracked (by rw [preserved.extras]; exact extras) owned.live
      (by rw [preserved.addresses]; exact address) owned rights root roots rangeCapacity rfl startEq.symm rfl
      bounded (by rw [s1]; rfl) (by rw [s2]; rfl) (by rw [s3])
      (by rw [s1]) (by rw [s2]) (by rw [s3]) (by rw [s4]) (by rw [s4]) (by rw [s5]) (by rw [s5])
      (by rw [s14]) (by rw [s14]) (by rw [s15]) (by rw [s15]) (by rw [s16]) (by rw [s16])
      readyDirect clocks mode (preserved.unchecked.trans input.unchecked) (preserved.noGc.trans input.noGc)
      (preserved.fixed.trans input.fixed) (preserved.ghost.trans input.ghost) (preserved.validation.trans input.shallow)
      (by rw [s0]) (by rw [s0]) va {} borrow rfl thread active
      18 callerValid input.old callerLive callerCache input.noClocks physical 9 .Unreachable continuation
  exact ⟨result,finalMachine,SuccessfulTrace.append history copied,present,sized,bytes,snapshot⟩

end DuplicatePrefix.CopyRootPositiveRoundtrip

#print axioms DuplicatePrefix.CopyRootPositiveRoundtrip.complete

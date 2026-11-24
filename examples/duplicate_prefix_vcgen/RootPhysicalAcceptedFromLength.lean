import RootSliceRetagResources
import duplicate_prefix.RootPositiveFromBacking
import duplicate_prefix.RootPhysicalCarrierTransport

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts SourceDomain PreparedArguments CanonicalCallDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem RootLengthOfSlice.acceptedPhysicalTrace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    {initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : RetainedSlice initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthOfSlice (PreparedContracts.actualConfig options () (remaining+1) span)
      #[] initialFrame frame initial final root allocation offset len count tracker)
    (accepted : ¬ count > len/2) (positiveCount : 0 < count.toNat)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (before : InitializedRegion (Storage.withCurrent #[] initialFrame initial) len)
    (sameId : before.id = root.id) (sameAllocation : before.entry = allocation)
    (sameStart : before.relativeStart.bytes = offset)
    (originalExtent : offset.toNat + len.toNat ≤ allocation.allocation.extra.locations.size.bytes.toNat)
    (initialKeys : RetagInsertionCapacity.Ready allocation.allocation.extra)
    (room : allocation.allocation.extra.nodes.size+2 < 2^32)
    (tagRoom : post.branch.ready.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (base : UInt64)
    (address : initial.user.addresses.baseAddr.find? (fun row => row.allocId == before.id) = some ⟨before.id,base⟩)
    (nonnull : base + offset ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] initialFrame initial)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] initialFrame initial)).entries.any
      (·.value.ty == 2) = false)
    (source : PreparedContracts.SourceComparator) (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (noRace : initial.dataRace = none) (backend : initial.user.payload.payload.user.backend = .none)
    (cmp : ProjectionMetadataFacts.NullComparator) (statementFuel : limits.validation = fuel+1)
    (rank : initialFrame.extra.userRelevance = 255)
    (track : initialFrame.trackCallerArg = none)
    (slot0 : initialFrame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (slot1 : initialFrame.locals[1]? = some ⟨.live (.immediate (.scalarPair
      (.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete before.id root.tag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.sliceLayout⟩)
    (slot2 : initialFrame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (dead : ∀ i, 15 ≤ i → i ≤ 24 → initialFrame.locals[i]? = some ⟨.dead,none⟩)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < initialFrame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < initialFrame.extra.userRelevance)
    (maskLen : allocation.allocation.initializationMask.len = allocation.allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed allocation.allocation.initializationMask)
    (provenance : ProvenanceCopy.WellFormed allocation.allocation.provenanceMap allocation.allocation.len)
    (storageFits : allocation.allocation.len+64 < 18446744073709551616)
    (extras : initial.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == before.id) =
      some (before.id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (initial.user.payload.payload.user.runtime.extras.allocations) before.id)}))
    (space : allocation.allocation.extra.nodes.size+3 < 2^32)
    (tagBudget : tracker.global.nextPointerTag.value.toNat+4 < 2^64)
    (protectedAge : ∀ tag, tracker.global.protectedTags.contains tag = true →
      tag.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (initialTracked : initial.borrowTracker = some tracker)
    (pointer : Pointer (Option Provenance))
    (concrete : pointer.provenance = some (.concrete before.id root.tag))
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] initialFrame initial) initialFrame pointer len)
    (headroom : Nat)
    (profile : AllocationProfile (Storage.withCurrent #[] initialFrame initial) initialFrame headroom)
    (noVarargs : initialFrame.vaList = #[]) (continues : initialFrame.returnContinuation = .stop true) :
    ∃ done, SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent #[] frame final) done ∧ done.stack.frames = #[] ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () done = (done,.ok false) := by
  obtain ⟨storage, id, start, entry, loan, sourceEq, trackerEq⟩ :=
    post.sourceRegion before sameId sameAllocation sameStart originalExtent initialKeys room
  have startEq : storage.relativeStart = Size.ofBytes offset := by
    cases fields : storage.relativeStart
    have bytes := congrArg Size.bytes start
    rw [fields,sameStart] at bytes
    cases bytes
    rfl
  have allocationData := entry.trans post.branch.allocationData
  have storageId : storage.id = post.branch.ready.id := id.trans (sameId.trans post.branch.id.symm)
  obtain ⟨thread, active, top⟩ := post.rootCache rank
  have relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ 0 := by
    intro i h
    have equal := Option.some.inj (h.symm.trans top)
    change i = 0 at equal
    omega
  have valid : 16 < frame.locals.size := by rw [post.branch.guard.size]; decide
  have field1 : frame.locals[1]? = _ := (post.bystanders 1 (.inl (by decide))).trans slot1
  have value1 := Option.some.inj ((Array.getElem?_eq_getElem (show 1 < frame.locals.size by omega)).symm.trans field1)
  let ready := post.branch.ready
  have capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source
      ready.root loan.tracker.global.nextPointerTag := by
    rw [entry,sourceEq,trackerEq]
    exact post.insertionCapacity initialKeys room
  have range : storage.relativeStart.bytes.toNat + len.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,entry,post.branch.rangeCapacity]
    exact originalExtent
  have metadataFinal : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame final)).metadata =
      PreparedReflection.actual.runtime := by
    change final.user.payload.payload.user.types.metadata = _
    rw [post.branch.stable.types]
    exact metadata
  have noAliasFinal : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame final)).entries.any
      (·.value.ty == 2) = false := by
    change final.user.payload.payload.user.types.entries.any _ = _
    rw [post.branch.stable.types]
    exact noAlias
  have concreteFinal : pointer.provenance = some (.concrete storage.id ready.tag) := by
    rw [id,post.branch.tag]
    exact concrete
  have distinct : ∀ key, key ≠ storage.id → final.memory.live[key]? = initial.memory.live[key]? := by
    intro key different
    exact post.branch.unrelated key (by rwa [storageId,post.branch.id] at different)
  have stored := RootPhysicalCarrierTransport.transport
    (Storage.withCurrent #[] initialFrame initial) (Storage.withCurrent #[] frame final)
    initialFrame frame pointer len storage.id ready.tag
    (by intro zero; rw [zero] at positive; exact (UInt64.lt_irrefl _ positive))
    concreteFinal tracker ready.tracker initialTracked ready.tracked post.protectors
    post.place (congrArg (·.borrowTracker) post.frameExtra) post.branch.stable.addresses distinct destination
  have outputBacking := RootPhysicalCarrierTransport.backing
    (Storage.withCurrent #[] initialFrame initial) (Storage.withCurrent #[] frame final)
    initialFrame headroom profile storage.id distinct post.branch.stable.extras
  have ordered : ∀ tag, ready.tracker.global.protectedTags.contains tag = true →
      tag.value.toNat < ready.tracker.global.nextPointerTag.value.toNat := by
    intro tag held
    have old := protectedAge tag (by simpa only [ready,post.protectors] using held)
    change tag.value.toNat < post.branch.ready.tracker.global.nextPointerTag.value.toNat
    rw [post.nextTag]
    omega
  have run := RootPositiveFromBacking.physicalOfBacking options limits remaining fuel sizeFuel span
    budget sizeBudget debugOff preciseOff implicitOff
    frame final len base ready.tag positive bounded valid count accepted post.branch.guard post.uncached7
    ((post.bystanders 15 (.inr (by decide))).trans (dead 15 (by decide) (by decide)))
    ((post.bystanders 16 (.inr (by decide))).trans (dead 16 (by decide) (by decide)))
    (congrArg (·.layout) value1) (post.branch.stable.race.trans noRace) storage loan ready.root capacity
    (by rw [trackerEq]; exact tagRoom) range
    (by rw [post.branch.stable.addresses,id]; exact address) (by rw [startEq]; exact nonnull)
    metadataFinal noAliasFinal source dispatch dispatchFuel (by rw [trackerEq]; exact post.branch.defaultMode)
    (post.branch.stable.backend.trans backend) post.branch.unchecked post.branch.gc thread active relevant
    (by rw [entry,trackerEq,sourceEq,startEq]; exact post.reservationStage initialKeys room originalExtent)
    (by rw [entry]; exact post.keys initialKeys room)
    (by rw [entry,post.nodes]; omega)
    (by rw [entry,trackerEq]; exact post.tagAge)
    (by rw [trackerEq]; exact ordered)
    (by rw [trackerEq,post.nextTag]; omega)
    (by rw [entry,sourceEq,ready.found]; exact congrArg some ready.unexposed)
    cmp statementFuel positiveCount
    (by rw [post.frameExtra]; exact rank) top (post.trackCallerArg.trans track)
    ((post.bystanders 2 (.inl (by decide))).trans slot2)
    (fun i lower upper => (post.bystanders i (.inr (by omega))).trans (dead i (by omega) upper))
    (by rw [post.frameExtra]; exact outerRank) (by rw [post.frameExtra]; exact innerRank)
    (by rw [allocationData]; exact maskLen) (by rw [allocationData]; exact maskValid)
    (by rw [allocationData]; exact provenance) (by rw [allocationData]; exact storageFits)
    (by rw [post.branch.stable.extras,id]; exact extras)
    ((post.bystanders 0 (.inl (by decide))).trans slot0)
    pointer concreteFinal stored outputBacking (post.varargs.trans noVarargs) (post.continuation.trans continues)
  have original := congrArg (·.value) value1
  apply run
  change frame.locals[1].value = .live (.immediate
    (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete storage.id ready.tag) (Size.ofBytes (base+storage.relativeStart.bytes)))
      len RootCompilerFacts.sliceLayout).imm)
  rw [startEq,id,show ready.tag = root.tag from post.branch.tag]
  exact original

#print axioms RootLengthOfSlice.acceptedPhysicalTrace
end DuplicatePrefix.RootZeroShallowReturn

import RootLengthRegion
import duplicate_prefix.RootPositiveFromLength

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts SourceDomain PreparedArguments RootPositiveCachedReturn

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

theorem RootLengthState.acceptedTrace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    {older : Array CompilerFrameContext.ActualFrame}
    {outside initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : ActiveCaller older outside initialFrame initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthState (PreparedContracts.actualConfig options () (remaining+1) span)
      older outside initialFrame frame initial final root allocation offset len count tracker)
    (accepted : ¬ count > len/2) (positiveCount : 0 < count.toNat)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (before : InitializedRegion (Storage.withCurrent (older.push outside) initialFrame initial) len)
    (sameId : before.id = root.id) (sameAllocation : before.entry = allocation)
    (sameStart : before.relativeStart.bytes = offset)
    (originalExtent : offset.toNat + len.toNat ≤ allocation.allocation.extra.locations.size.bytes.toNat)
    (initialKeys : RetagInsertionCapacity.Ready allocation.allocation.extra)
    (room : allocation.allocation.extra.nodes.size+2 < 2^32)
    (tagRoom : post.branch.ready.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (base : UInt64)
    (address : initial.user.addresses.baseAddr.find? (fun row => row.allocId == before.id) = some ⟨before.id,base⟩)
    (nonnull : base + offset ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) initialFrame initial)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) initialFrame initial)).entries.any
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
    (readyFuture : let tree := post.branch.ready.entry.allocation.extra
      let newTag := post.branch.ready.tracker.global.nextPointerTag
      let global := post.branch.ready.tracker.global
      ∀ (advanced : TreeBorrows.GlobalState) (child : UniIndex),
      global.newPointerTag = .ok (advanced,newTag) →
      (ExclusiveTwoPhaseRetag.reservationTree tree post.branch.ready.tag newTag (Size.ofBytes offset)
        (Size.ofBytes len) global.protectedTags).indexOfTag newTag = some child →
      advanced.nextPointerTag.value ≠ 18446744073709551615 ∧
      CurrentTwoPhaseStructural.InsertionCapacity
        (ExclusiveTwoPhaseRetag.reservationTree tree post.branch.ready.tag newTag (Size.ofBytes offset)
          (Size.ofBytes len) global.protectedTags) child post.branch.ready.root advanced.nextPointerTag)
    (image : let tree := post.branch.ready.entry.allocation.extra
      let reservationTag := post.branch.ready.tracker.global.nextPointerTag
      let finalTag := reservationTag.succ.getD reservationTag
      let tags := post.branch.ready.tracker.global.protectedTags
      let reservation := ExclusiveTwoPhaseRetag.reservationTree tree post.branch.ready.tag reservationTag
        (Size.ofBytes offset) (Size.ofBytes len) tags
      let active := ExclusiveTypedRetag.protectedFrozenTree reservation tags reservationTag finalTag
        (Size.ofBytes offset) (Size.ofBytes len)
      let released := (active.releaseProtector finalTag (tags.insert finalTag .StrongProtector)).tree
      ∀ i, released.indexOfTag finalTag = some i →
        RootPositiveFromLength.HolderImage released ((tags.insert finalTag .StrongProtector).remove finalTag)
          post.branch.ready.source i post.branch.ready.tag (Size.ofBytes offset) len) :
    ∃ done, SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent (older.push outside) frame final) done ∧
      done.stack.frames.size < (Storage.withCurrent (older.push outside) frame final).stack.frames.size := by
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
  have relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ (older.push outside).size := by
    intro i h
    have equal := Option.some.inj (h.symm.trans top)
    omega
  have valid : 16 < frame.locals.size := by rw [post.branch.guard.size]; decide
  have field1 : frame.locals[1]? = _ := (post.bystanders 1 (.inl (by decide))).trans slot1
  have value1 := Option.some.inj ((Array.getElem?_eq_getElem (show 1 < frame.locals.size by omega)).symm.trans field1)
  let ready := post.branch.ready
  let slot : CallerSlot older outside frame :=
    ⟨ready.target,ready.unwind,ready.destinationIndex,ready.destinationBound,ready.destinationSlot,
      ready.destinationLive,ready.destinationCached,ready.callerClocks,ready.continuation,ready.destination⟩
  have capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source
      ready.root loan.tracker.global.nextPointerTag := by
    rw [entry,sourceEq,trackerEq]
    exact post.insertionCapacity initialKeys room
  have range : storage.relativeStart.bytes.toNat + len.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,entry,post.branch.rangeCapacity]
    exact originalExtent
  have metadataFinal : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) frame final)).metadata =
      PreparedReflection.actual.runtime := by
    change final.user.payload.payload.user.types.metadata = _
    rw [post.branch.stable.types]
    exact metadata
  have noAliasFinal : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) frame final)).entries.any
      (·.value.ty == 2) = false := by
    change final.user.payload.payload.user.types.entries.any _ = _
    rw [post.branch.stable.types]
    exact noAlias
  have run := RootPositiveFromLength.cached options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
    older outside frame final len base ready.tag positive bounded valid count accepted post.branch.guard post.uncached7
    ((post.bystanders 15 (.inr (by decide))).trans (dead 15 (by decide) (by decide)))
    ((post.bystanders 16 (.inr (by decide))).trans (dead 16 (by decide) (by decide)))
    (congrArg (·.layout) value1) (post.branch.stable.race.trans noRace) storage loan ready.root capacity
    (by rw [trackerEq]; exact tagRoom) range
    (by rw [post.branch.stable.addresses,id]; exact address) (by rw [startEq]; exact nonnull)
    metadataFinal noAliasFinal source dispatch dispatchFuel (by rw [trackerEq]; exact post.branch.defaultMode)
    (post.branch.stable.backend.trans backend) post.branch.unchecked post.branch.gc thread active relevant
    (by rw [entry,trackerEq,startEq]; exact readyFuture) cmp statementFuel positiveCount
    (by rw [post.frameExtra]; exact rank) top (post.trackCallerArg.trans track)
    ((post.bystanders 2 (.inl (by decide))).trans slot2)
    (fun i lower upper => (post.bystanders i (.inr (by omega))).trans (dead i (by omega) upper))
    (by rw [post.frameExtra]; exact outerRank) (by rw [post.frameExtra]; exact innerRank)
    (by rw [allocationData]; exact maskLen) (by rw [allocationData]; exact maskValid)
    (by rw [allocationData]; exact provenance) (by rw [allocationData]; exact storageFits)
    (by rw [post.branch.stable.extras,id]; exact extras)
    ((post.bystanders 0 (.inl (by decide))).trans slot0)
    slot ready.owned ready.ownership (by rw [storageId]; exact ready.ownedTags) ready.varargs
    (by rw [entry,trackerEq,startEq,sourceEq]; exact image)
  have original := congrArg (·.value) value1
  obtain ⟨popped,trace⟩ := run (by
    rw [startEq,id,post.branch.tag]
    exact original)
  exact ⟨_,trace,by simp [Storage.withCurrent]⟩

#print axioms RootLengthState.acceptedTrace
end DuplicatePrefix.RootZeroShallowReturn

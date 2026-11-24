import duplicate_prefix.RootTwoPhaseComplete
import duplicate_prefix.AsMutRootRoundtrip

namespace DuplicatePrefix.RootAsMutReservation
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem completes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length base : UInt64) (parentTag : BorTag)
    (positive : 0 < length) (bounded : length ≤ 9223372036854775807)
    (valid : 16 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨6,7⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (destLive : frame.locals[16].value = .live (.immediate .uninit))
    (destUncached : frame.locals[16].layout = none)
    (noClocks : frame.extra.dataRace = none) (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (storage : InitializedRegion (Storage.withCurrent older frame machine) length)
    (loan : ExclusiveRegion (Storage.withCurrent older frame machine) length storage parentTag)
    (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id, base⟩)
    (nonnull : base + storage.relativeStart.bytes ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).entries.any
      (·.value.ty == 2) = false)
    (source : PreparedContracts.SourceComparator)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch + 1)
    (destLive15 : (frame.locals[15]'(by omega)).value = .live (.immediate .uninit))
    (destUncached15 : (frame.locals[15]'(by omega)).layout = none)
    (defaultMode : loan.tracker.retagMode = .Default)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ older.size)
    (future : ∀ (global : TreeBorrows.GlobalState) (child : UniIndex),
      let parentTree := storage.entry.allocation.extra
      let newTag := loan.tracker.global.nextPointerTag
      let nextTree := ExclusiveTwoPhaseRetag.reservationTree parentTree parentTag newTag
        storage.relativeStart (Size.ofBytes length) loan.tracker.global.protectedTags
      loan.tracker.global.newPointerTag = .ok (global,newTag) →
      nextTree.indexOfTag newTag = some child →
      global.nextPointerTag.value ≠ 18446744073709551615 ∧
        CurrentTwoPhaseStructural.InsertionCapacity nextTree child root global.nextPointerTag)
    (cmp : ProjectionMetadataFacts.NullComparator) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let oldPointer := Pointer.new (.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))
    let oldValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base oldPointer length RootCompilerFacts.sliceLayout).imm
    let newTag := loan.tracker.global.nextPointerTag
    let newPointer := Pointer.new (.concrete storage.id newTag) oldPointer.offset
    let newValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base newPointer length RootCompilerFacts.sliceLayout).imm
    (frame.locals[1]'(by omega)).value = .live (.immediate oldValue) →
    let finalTag := loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag
    let tags := loan.tracker.global.protectedTags
    let reservation := ExclusiveTwoPhaseRetag.reservationTree storage.entry.allocation.extra parentTag newTag
      storage.relativeStart (Size.ofBytes length) tags
    let installed := ExclusiveTypedRetag.protectedFrozenTree reservation tags newTag finalTag
      storage.relativeStart (Size.ofBytes length)
    let release := installed.releaseProtector finalTag (tags.insert finalTag .StrongProtector)

    ∃ (afterFrame : CompilerFrameContext.ActualFrame)
        (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
        (next : InitializedRegion (Storage.withCurrent older afterFrame afterMachine) length)
        (rights : ExclusiveRegion (Storage.withCurrent older afterFrame afterMachine) length next
          (loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag)),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent older frame machine)
        (Storage.withCurrent older afterFrame afterMachine) ∧
      afterFrame.location = .mir ⟨7,0⟩ ∧
      afterFrame.body = frame.body ∧ afterFrame.bodyIdentity = frame.bodyIdentity ∧
      afterFrame.functionInstance = frame.functionInstance ∧ afterFrame.extra = frame.extra ∧
      afterFrame.trackCallerArg = frame.trackCallerArg ∧
      afterFrame.returnPlace = frame.returnPlace ∧ afterFrame.returnContinuation = frame.returnContinuation ∧
      afterFrame.vaList = frame.vaList ∧ afterFrame.localsIdentity = frame.localsIdentity ∧
      next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
      next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } ∧
      next.entry.allocation.extra.roots = #[root] ∧
      next.relativeStart.bytes.toNat + length.toNat ≤ next.entry.allocation.extra.locations.size.bytes.toNat ∧
      rights.tracker.retagMode = .Default ∧
      next.entry.allocation.extra = release.tree ∧
      rights.tracker.global.protectedTags = (tags.insert finalTag .StrongProtector).remove finalTag ∧
      afterFrame.locals.size = frame.locals.size ∧
      afterFrame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base
        (.new (.concrete storage.id (loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag))
          (Size.ofBytes (base+storage.relativeStart.bytes)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      (∀ i, i ≠ 15 → i ≠ 16 → afterFrame.locals[i]? = frame.locals[i]?) ∧
      afterFrame.locals[16]? = some ⟨.live (.immediate newValue),some RootCompilerFacts.sliceLayout⟩ ∧
      afterMachine.user.addresses = machine.user.addresses ∧ afterMachine.dataRace = none ∧
      afterMachine.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl afterMachine.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl afterMachine.user).gcInterval = 0 ∧
      afterMachine.user.payload.payload.user.backend = .none ∧
      afterMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∀ key, key ≠ storage.id → afterMachine.memory.live[key]? = machine.memory.live[key]?) ∧
      afterMachine.user.payload.ghost = false ∧ afterMachine.user.payload.validation = .Shallow ∧
      (frame.extra.userRelevance = 255 → thread.topUserRelevantFrame = some older.size →
        ∃ reported, afterMachine.threads.activeThread? = some reported ∧ reported.topUserRelevantFrame = some older.size) := by
  intro cfg oldPointer oldValue newTag newPointer newValue original finalTag tags reservation installed release
  obtain ⟨prepared, advanced, assigned, loc, stagedArg, stillBody, stillIdentity, stillCallee, stillExtra,
    size, saved, user, race, threads, assignedUnrelated, ⟨next, child, idEq, offsetEq, _, extentEq, mode, counter, exactTree, beforePhysical⟩,
    trackCaller, returnPlace, continuation, varargs, localsIdentity⟩ :=
    RootTwoPhaseComplete.assigned options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
      older frame machine length base parentTag positive bounded valid body identity callee located sourceCached destLive destUncached
      noClocks noRace ghost shallow storage loan root capacity tagRoom extent address nonnull metadata noAlias cmp original
  have preparedBound : 16 < prepared.locals.size := by rwa [size]
  have value : prepared.locals[16].value = .live (.immediate
      (RetagReferencePlace.sliceValue cfg.access.runtime.base (.new (.concrete next.id newTag)
        (Size.ofBytes (base + next.relativeStart.bytes))) length RootCompilerFacts.sliceLayout).imm) := by
    have slot := stagedArg
    rw [Array.getElem?_eq_getElem preparedBound] at slot
    rw [idEq,offsetEq]
    exact congrArg (·.value) (Option.some.inj slot)
  have argLayout : prepared.locals[16].layout = some RootCompilerFacts.sliceLayout := by
    have slot := stagedArg
    rw [Array.getElem?_eq_getElem preparedBound] at slot
    exact congrArg (·.layout) (Option.some.inj slot)
  have kept15 : prepared.locals[15]'(by omega) = frame.locals[15]'(by omega) := by
    have out := saved 15 (by decide)
    rw [Array.getElem?_eq_getElem (show 15 < prepared.locals.size by omega),
      Array.getElem?_eq_getElem (show 15 < frame.locals.size by omega)] at out
    exact Option.some.inj out
  have nextExtent : next.relativeStart.bytes.toNat + length.toNat ≤ next.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [offsetEq,extentEq]
    exact extent
  obtain ⟨futureRoom, futureCap⟩ := future child.tracker.global child.source counter (by rw [← exactTree]; exact child.tagKnown)
  have newCapacity : CurrentTwoPhaseStructural.InsertionCapacity next.entry.allocation.extra child.source root child.tracker.global.nextPointerTag := by
    rw [exactTree]
    exact futureCap
  have returned := AsMutRootRoundtrip.completes options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
    older prepared advanced length base newTag positive bounded
    (race.trans noRace) (by rw [user]; exact ghost) (by rw [user]; exact shallow) next child root newCapacity futureRoom
    (mode.trans defaultMode) nextExtent (by rw [user,idEq]; exact address) (by rw [offsetEq]; exact nonnull)
    (by change (EvalProjectionMachine.arrays.get (Storage.withCurrent older prepared advanced)).metadata = _; simp only [Storage.withCurrent,EvalProjectionMachine.arrays,user]; exact metadata)
    (by change (EvalProjectionMachine.arrays.get (Storage.withCurrent older prepared advanced)).entries.any _ = _; simp only [Storage.withCurrent,EvalProjectionMachine.arrays,user]; exact noAlias)
    cmp source dispatch dispatchFuel loc (stillBody.trans body) (stillIdentity.trans identity) (stillCallee.trans callee)
    preparedBound value argLayout (by rw [kept15]; exact destLive15) (by rw [kept15]; exact destUncached15)
    (by rw [stillExtra]; exact noClocks) (by rw [user]; exact backend)
    (by rw [threads]; exact fixed) (by rw [user]; exact unchecked) (by rw [user]; exact noGc)
    thread (by rw [threads]; exact active) relevant
  have counterValue : child.tracker.global.nextPointerTag =
      loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag := by
    unfold TreeBorrows.GlobalState.newPointerTag at counter
    split at counter
    · contradiction
    · rename_i nextValue successor
      simp [successor]
      exact congrArg (fun pair : TreeBorrows.GlobalState × BorTag => pair.1.nextPointerTag) (Except.ok.inj counter).symm
  have beforeTags : child.tracker.global.protectedTags = loan.tracker.global.protectedTags := by
    unfold TreeBorrows.GlobalState.newPointerTag at counter
    split at counter
    · contradiction
    · exact congrArg (fun pair : TreeBorrows.GlobalState × BorTag => pair.1.protectedTags) (Except.ok.inj counter).symm
  rw [counterValue] at returned
  obtain ⟨machineAfter, run, addr, noRaceAfter, fixedAfter, checkedAfter, gcAfter, backendAfter, extrasAfter, helperUnrelated, ghostAfter,
    shallowAfter, _, cacheAfter, preparedNext, ready, newId, newOffset, afterPhysical, finalRoots, finalSize, newMode, releaseImage, protectedAfter⟩ := returned
  refine ⟨_,machineAfter,preparedNext,ready,.next assigned run,rfl,stillBody,stillIdentity,stillCallee,stillExtra,
    trackCaller,returnPlace,continuation,varargs,localsIdentity,newId.trans idEq,newOffset.trans offsetEq,?_,finalRoots,?_,newMode,?_,?_,?_,?_,?_,?_,?_,noRaceAfter,fixedAfter,checkedAfter,gcAfter,
    backendAfter,?_,?_,ghostAfter,shallowAfter,?_⟩
  · rw [afterPhysical,beforePhysical]
    rfl
  · rw [newOffset, finalSize]
    exact nextExtent
  · rw [releaseImage,exactTree,beforeTags,offsetEq]
  · rw [protectedAfter,beforeTags]
  · simpa [AsMutCurrentCall.cacheCaller,AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout] using size
  · simp [AsMutCurrentCall.cacheCaller,AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout,idEq,offsetEq]
    rfl
  · intro i not15 not16
    simpa [AsMutCurrentCall.cacheCaller,AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout,Ne.symm not15] using saved i not16
  · simpa [AsMutCurrentCall.cacheCaller,AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout,idEq,offsetEq] using stagedArg
  · rw [addr,user]
  · rw [extrasAfter,user]
  · intro key distinct
    exact (helperUnrelated key (by simpa only [idEq] using distinct)).trans (assignedUnrelated key distinct)
  · intro rank currentRoot
    exact cacheAfter (by rw [stillExtra]; exact rank) currentRoot

end DuplicatePrefix.RootAsMutReservation

#print axioms DuplicatePrefix.RootAsMutReservation.completes

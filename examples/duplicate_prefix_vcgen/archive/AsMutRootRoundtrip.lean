import duplicate_prefix.AsMutRootStep
import duplicate_prefix.AsMutRoundtrip

namespace DuplicatePrefix.AsMutRootRoundtrip
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain ActualReferenceMetadata
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
    (older : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length base : UInt64) (parentTag : BorTag)
    (positive : 0 < length) (bounded : length ≤ 9223372036854775807)
    (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (storage : InitializedRegion (Storage.withCurrent older caller machine) length)
    (loan : ExclusiveRegion (Storage.withCurrent older caller machine) length storage parentTag)
    (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (defaultMode : loan.tracker.retagMode = .Default)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id, base⟩)
    (nonnull : base + storage.relativeStart.bytes ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older caller machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older caller machine)).entries.any
      (·.value.ty == 2) = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (source : PreparedContracts.SourceComparator)
    (dispatchBudget : Nat) (dispatchFuel : limits.callDispatch = dispatchBudget + 1)
    (location : caller.location = .mir ⟨6,8⟩)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (instanceId : caller.functionInstance = RootBody.reflected.functionInstance)
    (valid : 16 < caller.locals.size)
    (argument : caller.locals[16].value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))) length reference).imm))
    (argLayout : caller.locals[16].layout = some reference)
    (destLive : (caller.locals[15]'(by omega)).value = .live (.immediate .uninit))
    (destUncached : (caller.locals[15]'(by omega)).layout = none)
    (noClocks : caller.extra.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ older.size) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent older caller machine
    let cached := AsMutCurrentCall.cacheCaller caller (by omega)
    let dest := (LocalPlaces.localRuntimePlace older.size cached 15 CopyCompilerFacts.destPointerLayout).stackView
    let tag := loan.tracker.global.nextPointerTag
    let ptr := Pointer.new (Provenance.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))
    let child := Pointer.new (Provenance.concrete storage.id tag) ptr.offset
    let expected := (RetagReferencePlace.sliceValue cfg.access.runtime.base child length reference).imm

    let pointer := Scalar.fromPointer cfg.access.runtime.base child
    let cachedValid : 15 < cached.locals.size := by
      have atCaller : (15 : Nat) < caller.locals.size := by omega
      simpa [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout] using atCaller
    let returned := {AsMutPtrReturn.writeFrame cached 15 (.scalar pointer) cachedValid with location := FrameLocation.mir ⟨7,0⟩}
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace cfg limits before (Storage.withCurrent older returned finalMachine) ∧
      finalMachine.user.addresses = machine.user.addresses ∧ finalMachine.dataRace = none ∧
      finalMachine.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.payload.payload.user.backend = .none ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      (∃ presentThread, finalMachine.threads.activeThread? = some presentThread) ∧
      (caller.extra.userRelevance = 255 → thread.topUserRelevantFrame = some older.size →
        ∃ reported, finalMachine.threads.activeThread? = some reported ∧ reported.topUserRelevantFrame = some older.size) ∧
      ∃ (next : InitializedRegion (Storage.withCurrent older returned finalMachine) length)
        (right : ExclusiveRegion (Storage.withCurrent older returned finalMachine) length next tag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧ next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } ∧
        next.entry.allocation.extra.roots = #[root] ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        right.tracker.retagMode = .Default := by
  intro cfg before cached dest tag ptr child expected pointer cachedValid returned
  obtain ⟨frame,after,step,loc,bodyEq,identityEq,calleeEq,saved,cont,clocks,size,vaList,ledger,retSlot,
    argSlot,deadSlots,ghostStill,shallowStill,raceStill,addrStill,backendStill,extrasStill,checkedStill,gcStill,fixedStill,⟨activeThread,threadEq,prevCache⟩,
    metadataAfter,alias,next,rights,idEq,offsetEq,modeStill,rootEq,extentEq,⟨node,nodeEq,_,notExposed⟩,materialized,vacant,physicalEntry⟩ :=
    AsMutRootStep.entered options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
      older caller machine length base parentTag positive bounded noRace ghost shallow storage loan root capacity tagRoom
      extent address nonnull metadata noAlias cmp source dispatchBudget dispatchFuel location body identity instanceId valid argument
      argLayout destLive destUncached noClocks backend fixed unchecked noGc thread active relevant
  have localDest : cached.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout]
  have localLive : cached.locals[15].value = .live (.immediate .uninit) := by
    simpa [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout] using destLive
  have returnDest : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace older.size cached 15 CopyCompilerFacts.destPointerLayout := by
    rw [saved]
    rfl
  have childExtent : next.relativeStart.bytes.toNat + length.toNat ≤ next.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [offsetEq,extentEq]
    exact extent
  have cachedBase : after.user.addresses.baseAddr.find? (fun row => row.allocId == next.id) = some ⟨next.id,base⟩ := by
    rw [addrStill,idEq]
    exact address
  have signed : length.toNat < 9223372036854775808 :=
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp bounded) (by decide)
  let relevance := activeThread.topUserRelevantFrame.getD (older.size+1)
  have top : FrameRelevance.top ⟨(older.push cached).push frame⟩ activeThread.topUserRelevantFrame = some relevance := by
    unfold FrameRelevance.top relevance
    cases activeThread.topUserRelevantFrame <;> simp
  have isOne : (({} : FrameState).addProtector storage.id tag).protectedTags = #[(next.id,tag)] := by
    rw [idEq]
    rfl
  have readSlot : frame.locals[1]? = some ⟨.live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete next.id tag) (Size.ofBytes (base+next.relativeStart.bytes))) length reference).imm),some reference⟩ := by
    rw [idEq,offsetEq]
    exact argSlot
  have joined :=
    AsMutRoundtrip.helper options limits remaining span fuel sizeFuel debugOff budget sizeBudget older cached frame after
      length base tag next rights (modeStill.trans defaultMode) bodyEq identityEq calleeEq loc size retSlot positive signed
      cachedBase (by rw [offsetEq]; exact nonnull) deadSlots clocks 15 cachedValid localDest localLive noClocks returnDest
      cont vaList _ ledger isOne root rootEq node nodeEq notExposed materialized vacant childExtent
      activeThread relevance threadEq top ghostStill shallowStill fixedStill checkedStill gcStill cmp metadataAfter alias readSlot
  have sameAddress : Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete next.id tag) (Size.ofBytes (base+next.relativeStart.bytes))) = pointer := by
    rw [idEq,offsetEq]
    rfl
  rw [sameAddress] at joined
  obtain ⟨final,trace,finalAddr,finalRace,finalUser,finalFixed,activeFinal,retainsRoot,result,finalId,finalOffset,physicalReturn,retainedRoots,retainedExtent,resultRights,finalMode⟩ := joined
  have finalChecked : (cfg.terminators.getControl final.user).checkedArithmetic = false := by
    rw [finalUser]
    unfold AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span]
    exact checkedStill
  have finalGc : (cfg.terminators.getControl final.user).gcInterval = 0 := by
    rw [finalUser]
    unfold AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span]
    exact gcStill
  have finalGhost : final.user.payload.ghost = false := by
    rw [finalUser]
    unfold AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ghostStill
  have finalShallow : final.user.payload.validation = .Shallow := by
    rw [finalUser]
    unfold AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact shallowStill
  have finalBackend : final.user.payload.payload.user.backend = .none := by
    rw [finalUser]
    unfold AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backendStill
  have finalExtras : final.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    rw [finalUser]
    unfold AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact extrasStill
  refine ⟨final, SuccessfulTrace.Trace.next step trace, finalAddr.trans addrStill,
    finalRace.trans raceStill, finalFixed.trans fixedStill, finalChecked, finalGc, finalBackend, finalExtras, finalGhost, finalShallow,
    activeFinal, ?_, result,resultRights,finalId.trans idEq,finalOffset.trans offsetEq, ?_,retainedRoots.trans rootEq,retainedExtent.trans extentEq,
    finalMode.trans (modeStill.trans defaultMode)⟩
  · intro rank topRoot
    exact retainsRoot rank (prevCache topRoot)
  · rw [physicalReturn, physicalEntry]
    rfl

end DuplicatePrefix.AsMutRootRoundtrip

#print axioms DuplicatePrefix.AsMutRootRoundtrip.completes

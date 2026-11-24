import duplicate_prefix.AsMutPreparedEntry
import duplicate_prefix.AsMutCurrentCall

namespace DuplicatePrefix.AsMutRootStep
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain ActualReferenceMetadata
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem entered
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
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      ExecutionMachine.step cfg limits () before =
        (Storage.withCurrent (older.push cached) frame after,.ok true) ∧
      frame.location = .mir ⟨0,0⟩ ∧ frame.body = HelperCompilerFacts.asMutPtrBody.body ∧
      frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity ∧ frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee ∧
      frame.returnPlace = dest ∧ frame.returnContinuation = .goto (some 7) .Unreachable ∧
      frame.extra.dataRace = none ∧ frame.locals.size = 5 ∧ frame.vaList = #[] ∧
      frame.extra.borrowTracker = some (({} : FrameState).addProtector storage.id tag) ∧
      frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩ ∧
      frame.locals[1]? = some ⟨.live (.immediate expected), some reference⟩ ∧
      (∀ localId, 2 ≤ localId → localId < 5 → frame.locals[localId]? = some ⟨.dead, none⟩) ∧
      after.user.payload.ghost = false ∧ after.user.payload.validation = .Shallow ∧ after.dataRace = none ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.payload.user.backend = .none ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (cfg.terminators.getControl after.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl after.user).gcInterval = 0 ∧
      after.threads.fixedScheduling = true ∧
      (∃ presentThread, after.threads.activeThread? = some presentThread ∧
        (thread.topUserRelevantFrame = some older.size → presentThread.topUserRelevantFrame = some older.size ∨
          presentThread.topUserRelevantFrame = some (older.push cached).size)) ∧
      (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push cached) frame after)).metadata =
        PreparedReflection.actual.runtime ∧
      (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push cached) frame after)).entries.any
        (·.value.ty == 2) = false ∧
      ∃ (next : InitializedRegion (Storage.withCurrent (older.push cached) frame after) length)
        (right : ExclusiveRegion (Storage.withCurrent (older.push cached) frame after) length next tag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        right.tracker.retagMode = loan.tracker.retagMode ∧
        next.entry.allocation.extra.roots = #[root] ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        (∃ node, next.entry.allocation.extra.nodeAt right.source = some node ∧ node.tag = tag ∧ node.isExposed = false) ∧
        RetagReleaseFootprint.MaterializedWithin next.entry.allocation.extra right.source
          next.relativeStart.bytes (next.relativeStart.bytes + length) ∧
        RetagReleaseFootprint.VacantRows next.entry.allocation.extra ∧
        next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } := by
  intro cfg before cached dest tag ptr child expected
  let charged := AsMutCurrentCall.charged options (remaining+1) span machine
  let cachedState := Storage.withCurrent older cached charged
  have chargedGhost : charged.user.payload.ghost = false := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ghost
  have chargedShallow : charged.user.payload.validation = .Shallow := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact shallow
  have chargedAddress : charged.user.addresses = machine.user.addresses := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have chargedMeta : (EvalProjectionMachine.arrays.get cachedState).metadata = PreparedReflection.actual.runtime := by
    unfold cachedState charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have chargedAlias : (EvalProjectionMachine.arrays.get cachedState).entries.any (·.value.ty == 2) = false := by
    unfold cachedState charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact noAlias
  let initialStorage : InitializedRegion cachedState length := {storage with live := storage.live}
  let initialLoan : ExclusiveRegion cachedState length initialStorage parentTag := {loan with tracked := loan.tracked}
  let pushed := AsMutPush.pushed options.userRelevantCrates cachedState dest
  have pushedSize : pushed.stack.frames.size = older.size + 2 := by
    simp [pushed,AsMutPush.pushed,cachedState,Storage.withCurrent,Array.size_push]
  let index := thread.topUserRelevantFrame.getD (older.size+1)
  have top : FrameRelevance.top pushed.stack thread.topUserRelevantFrame = some index := by
    unfold FrameRelevance.top index
    cases found : thread.topUserRelevantFrame with
    | none =>
      have nonempty : pushed.stack.frames.isEmpty = false := by
        simp [pushed,AsMutPush.pushed,cachedState,Storage.withCurrent]
      simp [nonempty,pushedSize]
    | some i => rfl
  have indexBound : index < pushed.stack.frames.size := by
    rw [pushedSize]
    unfold index
    cases found : thread.topUserRelevantFrame with
    | none => simp
    | some i =>
      have fits := relevant i found
      simp only [Option.getD_some]
      omega
  let atIndex := pushed.stack.frames[index]'indexBound
  have lookup : pushed.stack.frames[index]? = some atIndex := by
    exact Array.getElem?_eq_getElem indexBound
  have cachedValid : 15 < cached.locals.size := by
    have initial : (15 : Nat) < caller.locals.size := by omega
    simpa [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout] using initial
  have cachedDest : cached.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout]
  have cachedLive : cached.locals[15].value = .live (.immediate .uninit) := by
    simpa [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout] using destLive
  obtain ⟨frame,after,installation,rest⟩ := AsMutPreparedEntry.prepared options limits remaining fuel sizeFuel span
    budget sizeBudget debugOff preciseOff implicitOff older cached charged length base parentTag positive bounded noRace
    chargedGhost chargedShallow initialStorage initialLoan root capacity tagRoom extent
    (by rw [chargedAddress]; exact address) nonnull chargedMeta chargedAlias cmp .uninit 15 cachedValid
    cachedDest cachedLive noClocks thread index atIndex active top lookup
  have invoked := AsMutCurrentCall.step options limits (remaining+1) dispatchBudget dispatchFuel span debugOff source cmp
    older caller machine after frame _ body identity instanceId location valid argument argLayout destUncached
    noClocks ghost noRace backend fixed unchecked noGc installation
  obtain ⟨enterLoc, enterBody, enterIdentity, enterCallee, saved, continuation, frameClocks, frameSize,
    varargs, ledger, resultSlot, valueSlot, deadSlots, afterGhost, afterShallow, afterRace, afterAddress,
    afterHost, afterBackend, afterExtras, afterFixed, afterThread, afterMeta, afterAlias, rights⟩ := rest
  have controls : cfg.terminators.getControl after.user = cfg.terminators.getControl charged.user := by
    dsimp only [cfg]
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    change after.user.payload.payload.user.host.control = charged.user.payload.payload.user.host.control
    rw [afterHost]
  have checked : (cfg.terminators.getControl after.user).checkedArithmetic = false := by
    rw [controls]
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span]
    exact unchecked
  have gc : (cfg.terminators.getControl after.user).gcInterval = 0 := by
    rw [controls]
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span]
    exact noGc
  have chargedBackend : charged.user.payload.payload.user.backend = .none := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have chargeExtras : charged.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  refine ⟨frame,after,invoked,enterLoc,enterBody,enterIdentity,enterCallee,saved,continuation,
    frameClocks,frameSize,varargs,ledger,resultSlot,?_,deadSlots,afterGhost,afterShallow,afterRace,
    afterAddress.trans chargedAddress,afterBackend.trans chargedBackend,afterExtras.trans chargeExtras,checked,gc,afterFixed.trans fixed,?_,afterMeta,afterAlias,?_⟩
  · simpa only [expected, child, ptr, Pointer.new, initialStorage, initialLoan] using valueSlot
  · refine ⟨_,afterThread,?_⟩
    intro rootWasTop
    unfold PushThread.after
    split
    · exact Or.inr rfl
    · exact Or.inl rootWasTop
  · simpa only [initialStorage,initialLoan] using rights

end DuplicatePrefix.AsMutRootStep

#print axioms DuplicatePrefix.AsMutRootStep.entered

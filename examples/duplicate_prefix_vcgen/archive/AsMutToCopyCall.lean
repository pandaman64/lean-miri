import duplicate_prefix.AsMutPreparedAddFrame
import duplicate_prefix.RootPositiveAfterAsMut

namespace DuplicatePrefix.AsMutToCopyCall
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open PreparedArguments SourceDomain ActualReferenceMetadata
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

/-- Continue the actual accepted branch from the as_mut_ptr call through the
nested pointer-add guard, pointer return and copy-argument preparation. -/
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
    (relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ older.size)
    (count : UInt64) (countPositive : 0 < count.toNat)
    (copyBounds : count.toNat+count.toNat ≤ length.toNat)
    (frameSize : caller.locals.size = 25)
    (statementFuel : limits.validation = fuel+1)
    (countSlot : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (unused : ∀ i (h : i < caller.locals.size), 17 ≤ i → i ≤ 23 → caller.locals[i]'h = ⟨.dead,none⟩)
    (unused24 : caller.locals[24]? = some ⟨.dead,none⟩)
    (trackedCaller : caller.trackCallerArg = none)
    (direct : CopyHelperCleanup.AllImmediate caller)
    (localRank : caller.extra.userRelevance = 255) (cachedRoot : thread.topUserRelevantFrame = some older.size) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let tag := loan.tracker.global.nextPointerTag
    let pointer := Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes)))
    let advanced := Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes+count)))
    ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent older caller machine)
        (Storage.withCurrent older result finalMachine) ∧
      result.location = .mir ⟨8,4⟩ ∧ result.locals.size = 25 ∧
      result.body = caller.body ∧ result.bodyIdentity = caller.bodyIdentity ∧ result.functionInstance = caller.functionInstance ∧
      result.extra = caller.extra ∧ result.returnPlace = caller.returnPlace ∧ result.returnContinuation = caller.returnContinuation ∧
      result.vaList = caller.vaList ∧ result.localsIdentity = caller.localsIdentity ∧ result.trackCallerArg = caller.trackCallerArg ∧
      result.locals[17]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[18]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]? = some ⟨.live (.immediate (.scalar advanced)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[24]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧ finalMachine.user.addresses = machine.user.addresses ∧
      ∃ (next : InitializedRegion (Storage.withCurrent older result finalMachine) length)
        (right : ExclusiveRegion (Storage.withCurrent older result finalMachine) length next tag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧ right.tracker.retagMode = .Default := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let tag := loan.tracker.global.nextPointerTag
  let pointer : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base
    (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes)))
  let v15 : 15 < caller.locals.size := by omega
  let returned := AsMutPreparedAddFrame.returned caller v15 pointer
  obtain ⟨after,history,addressAfter,raceAfter,fixedAfter,checkedAfter,gcAfter,backendAfter,extrasAfter,ghostAfter,shallowAfter,
      activeAfter,rootCache,next,right,idEq,offsetEq,entryEq,rootsEq,extentEq,modeAfter⟩ :=
    AsMutRootRoundtrip.completes options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
      older caller machine length base parentTag positive bounded noRace ghost shallow storage loan root capacity tagRoom
      defaultMode extent address nonnull metadata noAlias cmp source dispatchBudget dispatchFuel location body identity instanceId
      valid argument argLayout destLive destUncached noClocks backend fixed unchecked noGc thread active relevant
  obtain ⟨current,activeCurrent,cachedCurrent⟩ := rootCache localRank cachedRoot
  have placeSize : returned.locals.size = 25 :=
    (AsMutPreparedAddFrame.locals_size caller v15 pointer).trans frameSize
  have pointerSlot : returned.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete next.id tag) (Size.ofBytes (base+next.relativeStart.bytes)))))),some CopyCompilerFacts.destPointerLayout⟩ := by
    rw [idEq,offsetEq]
    exact AsMutPreparedAddFrame.slot caller v15 pointer
  have copiedCount : returned.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ :=
    (AsMutPreparedAddFrame.unchanged caller v15 pointer 2 (by decide)).trans countSlot
  let temp := (RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))) length reference).imm
  have g16 : returned.locals[16]? = caller.locals[16]? := AsMutPreparedAddFrame.unchanged caller v15 pointer 16 (by decide)
  have present16 : returned.locals[16].value = .live (.immediate temp) := by
    rw [getElem?_pos returned.locals 16 (by omega),getElem?_pos caller.locals 16 valid] at g16
    exact (congrArg LocalState.value (Option.some.inj g16)).trans argument
  have unused' (i : Nat) (bound : i < returned.locals.size) (hi : 17 ≤ i) (hj : i ≤ 23) :
      returned.locals[i] = ⟨.dead,none⟩ := by
    have kept := AsMutPreparedAddFrame.unchanged caller v15 pointer i (by omega)
    have h : i < caller.locals.size := by omega
    rw [getElem?_pos returned.locals i bound,getElem?_pos caller.locals i h] at kept
    exact (Option.some.inj kept).trans (unused i h hi hj)
  have unused24' : returned.locals[24]? = some ⟨.dead,none⟩ :=
    (AsMutPreparedAddFrame.unchanged caller v15 pointer 24 (by decide)).trans unused24
  have cachedAddress : after.user.addresses.baseAddr.find? (fun row => row.allocId == next.id) = some ⟨next.id,base⟩ := by
    rw [addressAfter,idEq]
    exact address
  have signed : count.toNat < 2^63 := by
    have limit := UInt64.le_iff_toNat_le.mp bounded
    change length.toNat ≤ 9223372036854775807 at limit
    omega
  obtain ⟨result,finalMachine,trace,pc,sz,b,i,f,e,r,c,a,localId,callerTracked,s17,s18,s19,s21,s24,
      kept,directFinal,addrFinal,ghostFinal,shallowFinal,owned,exclusive,sameId,sameOffset,sameEntry,sameTracker⟩ :=
    RootPositiveAfterAsMut.through_copy_call options limits remaining span debugOff fuel budget statementFuel
      older returned (Storage.withCurrent older caller machine) after history
      length count base tag next right countPositive signed copyBounds cachedAddress placeSize pointerSlot temp present16
      copiedCount unused' unused24' body identity instanceId rfl noClocks modeAfter ghostAfter shallowAfter
      (AsMutPreparedAddFrame.direct caller v15 pointer direct) raceAfter trackedCaller current activeCurrent cachedCurrent
      (by change caller.extra.userRelevance > 0;rw [localRank]; decide) dispatchBudget dispatchFuel backendAfter
      checkedAfter gcAfter fixedAfter source
  have finalMode : exclusive.tracker.retagMode = .Default := by rw [sameTracker]; exact modeAfter
  rw [idEq,offsetEq] at s19 s21
  exact ⟨result,finalMachine,trace,pc,sz,b,i,f,e,r,c,a,localId,callerTracked,
    s17,s18,s19,s21,s24,directFinal,addrFinal.trans addressAfter,owned,exclusive,sameId.trans idEq,sameOffset.trans offsetEq,finalMode⟩

end DuplicatePrefix.AsMutToCopyCall

#print axioms DuplicatePrefix.AsMutToCopyCall.completes

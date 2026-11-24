import duplicate_prefix.RootAcceptedAfterLen
import duplicate_prefix.RootAsMutReservation

namespace DuplicatePrefix.RootAcceptedAsMut
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
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
    (count : UInt64) (accepted : ¬ count > length / 2)
    (entry : RootZeroShallowReturn.RejectionEntry frame machine length count)
    (none7 : (frame.locals[7]'(by rw [entry.size]; decide)).layout = none)
    (slot15 : frame.locals[15]? = some ⟨.dead,none⟩)
    (slot16 : frame.locals[16]? = some ⟨.dead,none⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (noRace : machine.dataRace = none)
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
    (defaultMode : loan.tracker.retagMode = .Default)
    (backend : machine.user.payload.payload.user.backend = .none)
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
      afterFrame.locals.size = 25 ∧
      afterFrame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base
        (.new (.concrete storage.id (loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag))
          (Size.ofBytes (base+storage.relativeStart.bytes)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      afterFrame.locals[0]? = frame.locals[0]? ∧ afterFrame.locals[2]? = frame.locals[2]? ∧
      (∀ i, 17 ≤ i → afterFrame.locals[i]? = frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate afterFrame ∧
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
        ∃ reported, afterMachine.threads.activeThread? = some reported ∧ reported.topUserRelevantFrame = some older.size)
    := by
  intro cfg oldPointer oldValue newTag newPointer newValue args finalTag tags reservation installed release
  obtain ⟨ready,charged,run,loc,keep0,keep1,keep2,size,placed15,placed16,body,identity,callee,extra,memory,tracker,
    race,threads,addresses,ghost,shallow,arrays,flag,gc,backendEq,extrasEq,savedTail,readyDirect,trackEq,returnEq,contEq,argsEq,localsEq⟩ :=
    RootAcceptedAfterLen.prepared options limits remaining span source debugOff fuel budget older frame machine length count
      accepted entry none7 slot15 slot16 loan.tracker loan.tracked defaultMode unchecked noGc
  have v : 16 < ready.locals.size := by rw [size]; decide
  have atSlot (i : Nat) (below : i < ready.locals.size) {expected : LocalState Provenance LocalLayout}
      (found : ready.locals[i]? = some expected) : ready.locals[i] = expected :=
    Option.some.inj ((Array.getElem?_eq_getElem below).symm.trans found)
  have prior : ready.locals[1]'(by omega) = frame.locals[1]'(by omega) := by
    rw [Array.getElem?_eq_getElem (show 1 < ready.locals.size by omega),
      Array.getElem?_eq_getElem (show 1 < frame.locals.size by omega)] at keep1
    exact Option.some.inj keep1
  let readyState := Storage.withCurrent older ready charged
  let readyStorage : InitializedRegion readyState length :=
    {storage with live := by change charged.memory.live[storage.id]? = _; rw [memory]; exact storage.live}
  let readyBorrow : ExclusiveRegion readyState length readyStorage parentTag :=
    {loan with tracked := by change charged.borrowTracker = _; rw [tracker]; exact loan.tracked}
  have callResult := RootAsMutReservation.completes options limits remaining fuel sizeFuel span budget sizeBudget
    debugOff preciseOff implicitOff older ready charged length base parentTag positive bounded v
    (body.trans entry.body) (identity.trans entry.identity) (callee.trans entry.callee) loc
    (by rw [prior]; exact sourceCached)
    (by rw [atSlot 16 v placed16]) (by rw [atSlot 16 v placed16])
    (by rw [extra]; exact entry.noClocks) (race.trans noRace) ghost shallow readyStorage readyBorrow root capacity
    tagRoom extent (by rw [addresses]; exact address) nonnull
    (by rw [arrays]; exact metadata) (by rw [arrays]; exact noAlias)
    source dispatch dispatchFuel (by rw [atSlot 15 (by omega) placed15]) (by rw [atSlot 15 (by omega) placed15])
    defaultMode (backendEq.trans backend) (by rw [threads]; exact entry.fixed) flag gc
    thread (by rw [threads]; exact active) relevant future cmp (by rw [prior]; exact args)
  obtain ⟨last,lastMachine,stored,right,tail,finish,finalBody,finalIdentity,finalCallee,finalExtra,finalTrack,finalReturn,finalCont,finalArgs,finalLocals,finalId,finalOffset,finalPhysical,finalRoots,finalExtent,finalMode,finalTree,finalTags,
    finalSize,pointerSlot,kept,temp16,finalAddress,finalRace,finalFixed,finalFlag,finalGc,finalBackend,finalExtras,finalUnrelated,finalGhost,finalShallow,finalCache⟩ := callResult
  refine ⟨last,lastMachine,stored,right,SuccessfulTrace.append run tail,finish,
    finalBody.trans body,finalIdentity.trans identity,finalCallee.trans callee,finalExtra.trans extra,
    finalTrack.trans trackEq,finalReturn.trans returnEq,finalCont.trans contEq,finalArgs.trans argsEq,finalLocals.trans localsEq,
    finalId,finalOffset,finalPhysical,finalRoots,finalExtent,finalMode,finalTree,finalTags,finalSize.trans size,pointerSlot,(kept 0 (by decide) (by decide)).trans keep0,(kept 2 (by decide) (by decide)).trans keep2,?_,?_,temp16,
    finalAddress.trans addresses,finalRace,finalFixed,finalFlag,finalGc,finalBackend,finalExtras.trans extrasEq,?_,finalGhost,finalShallow,?_⟩
  · intro i tail
    exact (kept i (by omega) (by omega)).trans (savedTail i tail)
  · intro slot member pointer invalid
    obtain ⟨i, fits, same⟩ := Array.mem_iff_getElem.mp member
    have lookup : last.locals[i]? = some slot := by rw [Array.getElem?_eq_getElem fits,same]
    by_cases ret : i = 15
    · subst i
      rw [lookup] at pointerSlot
      cases pointerSlot
      cases invalid
    · by_cases cast : i = 16
      · subst i
        rw [lookup] at temp16
        cases temp16
        cases invalid
      · have priorSlot : ready.locals[i]? = some slot := (kept i ret cast).symm.trans lookup
        obtain ⟨bound, previous⟩ := Array.getElem?_eq_some_iff.mp priorSlot
        exact readyDirect slot (Array.mem_iff_getElem.mpr ⟨i,bound,previous⟩) pointer invalid
  · intro key distinct
    exact (finalUnrelated key distinct).trans (congrArg (fun rows => rows.live[key]?) memory)
  · intro rank oldCache
    exact finalCache (by rw [extra]; exact rank) oldCache

end DuplicatePrefix.RootAcceptedAsMut

#print axioms DuplicatePrefix.RootAcceptedAsMut.completes

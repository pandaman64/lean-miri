import duplicate_prefix.RuntimeZeroCurrentStep
import duplicate_prefix.RuntimeZeroCurrentInstalled
import duplicate_prefix.LanguageGuardCurrentLeafTrace
import duplicate_prefix.PushThread
import duplicate_prefix.PopActive

namespace DuplicatePrefix.RuntimeZeroCurrentRoundtrip
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open RuntimeZeroCurrentStep RuntimeZeroCurrentUncached LanguageGuardCurrentReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem call_returns_false_with_cache
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (original : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : original.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : original.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : original.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : original.location = .mir ⟨0,3⟩)
    (originalSize : 1 < original.locals.size)
    (originalLive : original.locals[1].value = .live (.immediate .uninit))
    (originalUncached : original.locals[1].layout = none)
    (originalNoClocks : original.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine)) (RuntimeZeroEntry.destination frames original)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine)) (RuntimeZeroEntry.destination frames original)).stack.frames[threadIndex]? = some current)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (shallow : machine.user.payload.validation = .Shallow) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let caller := cachedCaller original originalSize
    let charged := accountedMachine options remaining span machine
    let state := Storage.withCurrent frames caller charged
    let dest := RuntimeZeroEntry.destination frames original
    let leaf := RuntimeZeroCurrentInstalled.frame options state dest
    let pushed := RuntimeZeroEntry.pushedMachine options state dest current
    ∃ finalMachine threadAfter, SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames original machine)
      (Storage.withCurrent frames
        (returnedCallerFrame caller .runtimeGuard
          (by change 1 < caller.locals.size; simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout] using originalSize) 1) finalMachine) ∧
      finalMachine.memory = machine.memory ∧ finalMachine.borrowTracker = machine.borrowTracker ∧
      finalMachine.user.addresses = machine.user.addresses ∧ finalMachine.dataRace = none ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.threads.activeThread? = some threadAfter ∧
      (∀ earlier, thread.topUserRelevantFrame = some earlier → earlier < frames.size →
        RuntimeZeroEntryFacts.rank options.userRelevantCrates < current.extra.userRelevance →
        finalMachine.threads.activeThread? = some thread) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let caller := cachedCaller original originalSize
  let charged := accountedMachine options remaining span machine
  let state := Storage.withCurrent frames caller charged
  let dest := RuntimeZeroEntry.destination frames original
  let leaf := RuntimeZeroCurrentInstalled.frame options state dest
  let pushed := RuntimeZeroEntry.pushedMachine options state dest current
  let fresh := (CallEntryFacts.freshRoot charged).1
  let raw := RuntimeZeroEntry.rawFrame options state dest
  have e1 := RuntimeZeroCurrentStep.step options limits remaining budget dispatchFuel span source debugOff
    frames original machine body identity callee location originalSize originalLive originalUncached
    originalNoClocks noRace backend ghost tracker tracked thread threadIndex current active top present unchecked noGc fixed
  have metadata := RuntimeZeroCurrentInstalled.metadata options state dest
  obtain ⟨hBody,hId,hFn,hPC,hDest,hCont,hVa,hClocks,hTracked⟩ := metadata
  have leafSlots := RuntimeZeroCurrentInstalled.locals options state dest
  have v0 : 0 < leaf.locals.size := by rw [leafSlots]; decide
  have observed : leaf.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    change (RuntimeZeroCurrentInstalled.frame options state dest).locals[0]? = _
    rw [leafSlots]
    rfl
  have leaf0 := (Array.getElem?_eq_some_iff.mp observed).2
  have all : CopyHelperCleanup.AllImmediate leaf := by
    intro slot member memory
    rw [leafSlots] at member
    simp at member
    subst slot
    simp
  have noClocks : leaf.extra.dataRace = none := by rw [hClocks]; exact congrArg (Option.map _) noRace
  have leafTracked : leaf.extra.borrowTracker = some ({} : FrameState) := by
    rw [hTracked]; exact congrArg (Option.map _) tracked
  have callerValid : (1 : MIR.LocalId) < caller.locals.size := by
    simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout] using originalSize
  have callerLive : caller.locals[1].value = .live (.immediate .uninit) := by
    simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout] using originalLive
  have callerCache : caller.locals[1].layout = some RootCompilerFacts.boolLayout := by
    simp [caller,cachedCaller,LocalPlaces.cachePlaceLayout]
  have destination : leaf.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout := by
    change (RuntimeZeroCurrentInstalled.frame options state dest).returnPlace.toRuntimePlace = _
    rw [hDest]
    rfl
  let rose := raw.extra.userRelevance
  let former := current.extra.userRelevance
  let pushedThread := PushThread.after thread (frames.push caller).size rose former
  have nextThread : pushed.threads.activeThread? = some pushedThread :=
    PushThread.active_after fresh thread (frames.push caller).size rose former active
  have pushedUser : pushed.user = fresh.user := by
    change (GenericPushRelevance.afterPush fresh (frames.push caller).size rose former).user = fresh.user
    unfold GenericPushRelevance.afterPush
    split <;> rfl
  have pushedMemory : pushed.memory = machine.memory := by
    change (GenericPushRelevance.afterPush fresh (frames.push caller).size rose former).memory = machine.memory
    unfold GenericPushRelevance.afterPush
    split <;> rfl
  have pushedTracker : pushed.borrowTracker = some tracker := by
    change (GenericPushRelevance.afterPush fresh (frames.push caller).size rose former).borrowTracker = some tracker
    unfold GenericPushRelevance.afterPush
    split <;> exact tracked
  have pushedFixed : pushed.threads.fixedScheduling = true := by
    change (GenericPushRelevance.afterPush fresh (frames.push caller).size rose former).threads.fixedScheduling = true
    unfold GenericPushRelevance.afterPush
    split <;> exact fixed
  have pushedRace : pushed.dataRace = none := by
    change (GenericPushRelevance.afterPush fresh (frames.push caller).size rose former).dataRace = none
    unfold GenericPushRelevance.afterPush
    split <;> exact noRace
  have pushedGhost : pushed.user.payload.ghost = false := by
    rw [pushedUser]
    exact (PointerAddCurrentReturn.accounted_ghost options remaining span machine).trans ghost
  have pushedShallow : pushed.user.payload.validation = .Shallow := by
    rw [pushedUser]
    exact (PointerAddCurrentReturn.accounted_validation options remaining span machine).trans shallow
  have nextControl : cfg.terminators.getControl pushed.user =
      TerminatorClock.advance (cfg.terminators.getControl machine.user) := by
    rw [pushedUser]
    unfold fresh CallEntryFacts.freshRoot charged accountedMachine
      PointerAddCurrentReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have pushUnchecked : (cfg.terminators.getControl pushed.user).checkedArithmetic = false := by
    rw [nextControl]
    exact unchecked
  have pushNoGc : (cfg.terminators.getControl pushed.user).gcInterval = 0 := by
    rw [nextControl]
    exact noGc
  have e2 := LanguageGuardCurrentLeafTrace.returns_false options limits remaining span debugOff fuel validationFuel
    frames caller leaf pushed v0 .uninit (by rw [leaf0]) (by rw [leaf0]) hBody hId hFn hPC noClocks
    callerValid callerLive callerCache originalNoClocks destination 1 .Unreachable hCont all hVa
    tracker pushedTracker {} leafTracked rfl pushedThread nextThread pushedGhost pushedShallow pushUnchecked pushNoGc pushedFixed
  let completed := {ActualLocalCopy.written leaf 0 RootCompilerFacts.boolLayout v0
    (.scalar (.fromBool false)) with location := .mir ⟨0,1⟩}
  let ticked := accountedMachine options remaining span pushed
  let after := poppedMachine frames caller completed ticked (pushedThread.topUserRelevantFrame.getD (frames.push caller).size)
  have afterMemory : after.memory = machine.memory := by
    unfold after poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact pushedMemory
  have afterTracker : after.borrowTracker = machine.borrowTracker := by
    unfold after poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact pushedTracker.trans tracked.symm
  have afterRace : after.dataRace = none := by
    unfold after poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact pushedRace
  have afterFixed : after.threads.fixedScheduling = true := by
    unfold after poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact pushedFixed
  have afterUser : after.user = ticked.user := popped_user frames caller completed ticked _
  have userFields : after.user.addresses = machine.user.addresses ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      after.user.payload.payload.user.types = machine.user.payload.payload.user.types := by
    rw [afterUser]
    unfold ticked accountedMachine PointerAddCurrentReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators,pushedUser]
    unfold fresh CallEntryFacts.freshRoot charged accountedMachine
      PointerAddCurrentReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have afterGhost : after.user.payload.ghost = false := by
    rw [afterUser]
    exact (PointerAddCurrentReturn.accounted_ghost options remaining span pushed).trans pushedGhost
  have afterShallow : after.user.payload.validation = .Shallow := by
    rw [afterUser]
    exact (PointerAddCurrentReturn.accounted_validation options remaining span pushed).trans pushedShallow
  have afterControl : cfg.terminators.getControl after.user = TerminatorClock.advance
      (cfg.terminators.getControl pushed.user) := by
    rw [afterUser]
    exact CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have afterUnchecked : (cfg.terminators.getControl after.user).checkedArithmetic = false := by
    rw [afterControl]
    exact pushUnchecked
  have afterNoGc : (cfg.terminators.getControl after.user).gcInterval = 0 := by
    rw [afterControl]
    exact pushNoGc
  obtain ⟨threadAfter,afterActive⟩ := PopActive.after_relevance_at_active (frames.push caller)
    completed ticked (pushedThread.topUserRelevantFrame.getD (frames.push caller).size) pushedThread nextThread
  have keepThread (earlier : Nat) (cached : thread.topUserRelevantFrame = some earlier)
      (bound : earlier < frames.size) (rankBelow : RuntimeZeroEntryFacts.rank options.userRelevantCrates < current.extra.userRelevance) :
      after.threads.activeThread? = some thread := by
    have rankEq : rose = RuntimeZeroEntryFacts.rank options.userRelevantCrates := rfl
    have noPush : ¬rose ≥ former := by
      rw [rankEq]
      intro opposite
      have h1 := UInt8.lt_iff_toNat_lt.mp rankBelow
      have h2 := UInt8.le_iff_toNat_le.mp opposite
      change current.extra.userRelevance.toNat ≤ _ at h2
      omega
    have sameThread : pushedThread = thread := by simp [pushedThread,PushThread.after,noPush]
    have noPop : pushedThread.topUserRelevantFrame.getD (frames.push caller).size ≠ (frames.push caller).size := by
      rw [sameThread,cached]
      simp
      omega
    unfold after poppedMachine GenericPopFrame.afterRelevanceAt
    rw [if_neg noPop]
    exact nextThread.trans (congrArg some sameThread)
  exact ⟨after,threadAfter,.next e1 e2,afterMemory,afterTracker,userFields.1,afterRace,
    afterGhost,afterShallow,userFields.2.1,userFields.2.2.1,userFields.2.2.2,afterFixed,afterUnchecked,afterNoGc,afterActive,keepThread⟩

end DuplicatePrefix.RuntimeZeroCurrentRoundtrip

#print axioms DuplicatePrefix.RuntimeZeroCurrentRoundtrip.call_returns_false_with_cache

import duplicate_prefix.LanguageGuardCurrentParentPrelude
import duplicate_prefix.RuntimeZeroCurrentRoundtrip
import duplicate_prefix.LanguageGuardCurrentParentExit

namespace DuplicatePrefix.LanguageGuardCurrentRoundtrip
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open LanguageGuardCurrentReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

noncomputable def prepared := LanguageGuardCurrentParentPrelude.result

theorem preparedSize (frame : CompilerFrameContext.ActualFrame)
    (valid1 : 1 < frame.locals.size) (valid2 : 2 < frame.locals.size) :
    (prepared frame valid1 valid2).locals.size = frame.locals.size := by
  simp [prepared,LanguageGuardCurrentParentPrelude.result,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout]

noncomputable def runtimeCaller (frame : CompilerFrameContext.ActualFrame)
    (valid1 : 1 < frame.locals.size) (valid2 : 2 < frame.locals.size) :=
  RuntimeZeroCurrentUncached.cachedCaller (prepared frame valid1 valid2)
    (by rw [preparedSize]; exact valid1)

noncomputable def runtimeRawState
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid1 : 1 < frame.locals.size) (valid2 : 2 < frame.locals.size) :=
  RuntimeZeroEntryFacts.pushed options.userRelevantCrates
    (Storage.withCurrent (frames.push caller) (runtimeCaller frame valid1 valid2)
      (PointerAddCurrentReturn.accountedMachine options remaining span machine))
    (RuntimeZeroEntry.destination (frames.push caller) (prepared frame valid1 valid2))

/-- Execute the compiled language guard, including the nested runtime call
and both physical returns. The caller is either ptr.add or copy_nonoverlapping. -/
theorem returns_false_with_cache
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (callFuel : limits.callDispatch = budget+1)
    (validationFuel : options.limits.validation = fuel+1)
    (statementFuel : limits.validation = fuel+1) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (debug : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.parentBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.parentCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (valid0 : 0 < frame.locals.size) (valid1 : 1 < frame.locals.size) (valid2 : 2 < frame.locals.size)
    (local0 : frame.locals[0] = ⟨.live (.immediate .uninit),none⟩)
    (local1 : frame.locals[1] = ⟨.dead,none⟩) (local2 : frame.locals[2] = ⟨.dead,none⟩)
    (noClocks : frame.extra.dataRace = none) (direct : CopyHelperCleanup.AllImmediate frame)
    (varargs : frame.vaList = #[])
    (borrowFrame : FrameState) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default) (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (other : CompilerFrameContext.ActualFrame) (index : Nat)
    (top : FrameRelevance.top (runtimeRawState options remaining span frames caller frame machine valid1 valid2).stack
      thread.topUserRelevantFrame = some index)
    (found : (runtimeRawState options remaining span frames caller frame machine valid1 valid2).stack.frames[index]? = some other)
    (site : Site) (returnSite : site = .languageGuard ∨ site = .copyLanguageGuard)
    (callerValid : callerSlot site < caller.locals.size)
    (callerLive : caller.locals[callerSlot site].value = .live (.immediate .uninit))
    (callerCache : caller.locals[callerSlot site].layout = some RootCompilerFacts.boolLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller (callerSlot site) RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ after threadAfter, SuccessfulTrace.Trace cfg limits
      (Storage.withCurrent (frames.push caller) frame machine)
      (Storage.withCurrent frames (returnedCallerFrame caller site callerValid target) after) ∧
      after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
      after.user.addresses = machine.user.addresses ∧ after.dataRace = none ∧
      after.user.payload.ghost = false ∧ after.user.payload.validation = .Shallow ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      after.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      after.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl after.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl after.user).gcInterval = 0 ∧
      after.threads.activeThread? = some threadAfter ∧
      (∀ earlier, thread.topUserRelevantFrame = some earlier → earlier < frames.size →
        RuntimeZeroEntryFacts.rank options.userRelevantCrates < other.extra.userRelevance →
        after.threads.activeThread? = some thread) := by
  let pre := prepared frame valid1 valid2
  let cached := runtimeCaller frame valid1 valid2
  have start := LanguageGuardCurrentParentPrelude.to_runtime_call options limits (remaining+1) span
    debug fuel statementFuel (frames.push caller) frame machine body identity callee location valid1 valid2
    (by rw [local1]) (by rw [local2]) (by rw [local2]) noClocks ghost shallow
  have preValid1 : 1 < pre.locals.size := by rw [preparedSize]; exact valid1
  have preLive1 : pre.locals[1].value = .live (.immediate .uninit) := by
    simp [pre,prepared,LanguageGuardCurrentParentPrelude.result,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set]
  have preUncached1 : pre.locals[1].layout = none := by
    simp [pre,prepared,LanguageGuardCurrentParentPrelude.result,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,local1]
  obtain ⟨middle,tMid,runtime,memMid,trackedMid,addressesMid,raceMid,ghostMid,shallowMid,backendMid,extrasMid,typesMid,fixedMid,
      uncheckedMid,noGcMid,activeMid,keepMid⟩ :=
    RuntimeZeroCurrentRoundtrip.call_returns_false_with_cache options limits remaining budget callFuel span source debug
      (frames.push caller) pre machine body identity callee rfl preValid1 preLive1 preUncached1 noClocks
      noRace backend ghost tracker tracked thread index other active top found unchecked noGc fixed fuel validationFuel shallow
  have cv1 : 1 < cached.locals.size := by
    simpa [cached,runtimeCaller,RuntimeZeroCurrentUncached.cachedCaller,LocalPlaces.cachePlaceLayout] using preValid1
  let returned := returnedCallerFrame cached .runtimeGuard cv1 1
  have csize : returned.locals.size = frame.locals.size := by
    simp [returned,returnedCallerFrame,callerSlot,cached,runtimeCaller,RuntimeZeroCurrentUncached.cachedCaller,
      LocalPlaces.cachePlaceLayout,preparedSize]
  have r0 : 0 < returned.locals.size := by rw [csize]; exact valid0
  have r1 : 1 < returned.locals.size := by rw [csize]; exact valid1
  have r2 : 2 < returned.locals.size := by rw [csize]; exact valid2
  have seen0 : returned.locals[0] = ⟨.live (.immediate .uninit),none⟩ := by
    simpa [returned,returnedCallerFrame,callerSlot,cached,runtimeCaller,RuntimeZeroCurrentUncached.cachedCaller,
      LocalPlaces.cachePlaceLayout,pre,prepared,LanguageGuardCurrentParentPrelude.result,
      SourceSteps.liveFrame,Array.getElem_set] using local0
  have seen1 : returned.locals[1] =
      ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ := by
    simp [returned,returnedCallerFrame,callerSlot,cached,runtimeCaller,RuntimeZeroCurrentUncached.cachedCaller,
      LocalPlaces.cachePlaceLayout]
  have seen2 : returned.locals[2].value = .live (.immediate .uninit) := by
    simp [returned,returnedCallerFrame,callerSlot,cached,runtimeCaller,RuntimeZeroCurrentUncached.cachedCaller,
      LocalPlaces.cachePlaceLayout,pre,prepared,LanguageGuardCurrentParentPrelude.result,SourceSteps.liveFrame,
      Array.getElem_set]
  let one := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1
  let bound2 : 2 < one.locals.size := by simpa [one,SourceSteps.liveFrame] using valid2
  let two := SourceSteps.liveFrame one ⟨0,1⟩ 2 bound2
  have b2 : 2 < two.locals.size := by simpa [two,SourceSteps.liveFrame] using bound2
  have preDirect : CopyHelperCleanup.AllImmediate pre :=
    CopyHelperCleanup.all_immediate_cache two 2 CopyHelperUnit.layout b2
      (LocalDirectness.live one ⟨0,1⟩ 2 bound2 (LocalDirectness.live frame ⟨0,0⟩ 1 valid1 direct))
  have cachedDirect : CopyHelperCleanup.AllImmediate cached :=
    CopyHelperCleanup.all_immediate_cache pre 1 RootCompilerFacts.boolLayout preValid1 preDirect
  have returnedDirect : CopyHelperCleanup.AllImmediate returned :=
    CopyHelperCleanup.all_immediate_set cached 1 _ cv1 cachedDirect (by intro ptr; simp)
  obtain ⟨after,tAfter,exit,memAfter,trackedAfter,addressesAfter,raceAfter,ghostAfter,shallowAfter,backendAfter,extrasAfter,typesAfter,fixedAfter,
      uncheckedAfter,noGcAfter,activeAfter,keepAfter⟩ :=
    LanguageGuardCurrentParentExit.returns_false_with_cache options limits remaining span debug fuel validationFuel
      frames caller returned middle body identity callee rfl r0 r1 r2
      (by rw [seen0]) (by rw [seen0]) (by rw [seen1]) (by rw [seen1]) .uninit seen2
      noClocks tracker (trackedMid.trans tracked) mode ghostMid shallowMid uncheckedMid noGcMid fixedMid
      site returnSite callerValid callerLive callerCache callerClocks destination target unwind continuation
      returnedDirect varargs borrowFrame frameTracked empty tMid activeMid
  have setup : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent (frames.push caller) frame machine)
      (Storage.withCurrent (frames.push caller) pre machine) := start
  have keepThread (earlier : Nat) (cachedIndex : thread.topUserRelevantFrame = some earlier)
      (bound : earlier < frames.size)
      (rank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < other.extra.userRelevance) :
      after.threads.activeThread? = some thread := by
    have mid := keepMid earlier cachedIndex (by simp; omega) rank
    have same : tMid = thread := Option.some.inj (activeMid.symm.trans mid)
    exact (keepAfter earlier (same.symm ▸ cachedIndex) bound).trans (congrArg some same)
  exact ⟨after,tAfter,SuccessfulTrace.append setup (SuccessfulTrace.append runtime exit),
    memAfter.trans memMid,trackedAfter.trans trackedMid,addressesAfter.trans addressesMid,
    raceAfter.trans raceMid,ghostAfter,shallowAfter,backendAfter.trans backendMid,extrasAfter.trans extrasMid,typesAfter.trans typesMid,fixedAfter,uncheckedAfter,noGcAfter,activeAfter,keepThread⟩

end DuplicatePrefix.LanguageGuardCurrentRoundtrip

#print axioms DuplicatePrefix.LanguageGuardCurrentRoundtrip.returns_false_with_cache

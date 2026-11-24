import duplicate_prefix.PointerAddLanguageGuardStep
import duplicate_prefix.PointerAddLanguageGuardStorage
import duplicate_prefix.LanguageZeroInstalled
import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.PointerAddGuardEntryCurrent
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

noncomputable def ready (frame : CompilerFrameContext.ActualFrame)
    (v3 : 3 < frame.locals.size) (v4 : 4 < frame.locals.size) :=
  let local3 := SourceSteps.liveFrame frame ⟨0,0⟩ 3 v3
  SourceSteps.liveFrame local3 ⟨0,1⟩ 4 (by simpa [local3,SourceSteps.liveFrame] using v4)

theorem readySize (frame : CompilerFrameContext.ActualFrame)
    (v3 : 3 < frame.locals.size) (v4 : 4 < frame.locals.size) :
    (ready frame v3 v4).locals.size = frame.locals.size := by
  simp [ready,SourceSteps.liveFrame]

noncomputable def cached (frame : CompilerFrameContext.ActualFrame)
    (v3 : 3 < frame.locals.size) (v4 : 4 < frame.locals.size) :=
  PointerAddLanguageGuardUncached.cachedCaller (ready frame v3 v4)
    (by rw [readySize]; exact v4)

noncomputable def guardState (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (root frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (v3 : 3 < frame.locals.size) (v4 : 4 < frame.locals.size) :=
  Storage.withCurrent (older.push root) (cached frame v3 v4)
    (PointerAddCurrentReturn.accountedMachine options remaining span machine)

noncomputable def guardDestination (older : Array CompilerFrameContext.ActualFrame)
    (root frame : CompilerFrameContext.ActualFrame)
    (v3 : 3 < frame.locals.size) (v4 : 4 < frame.locals.size) :=
  LanguageGuardEntryAt.destination (older.push root) (ready frame v3 v4) 4

/-- Execute the current pointer-add prelude and the actual language-guard call. -/
theorem reaches_guard
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (callFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false)
    (older : Array CompilerFrameContext.ActualFrame) (root frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (v3 : 3 < frame.locals.size) (v4 : 4 < frame.locals.size)
    (dead3 : frame.locals[3].value = .dead) (dead4 : frame.locals[4].value = .dead)
    (uncached4 : frame.locals[4].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (noRace : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some older.size)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let state := guardState options remaining span older root frame machine v3 v4
    let dest := guardDestination older root frame v3 v4
    let parent := LanguageZeroInstalled.frame options state dest
    let nextMachine := LanguageZeroEntry.pushedMachine options state dest root
    SuccessfulTrace.Trace cfg limits (Storage.withCurrent (older.push root) frame machine)
      (Storage.withCurrent ((older.push root).push (cached frame v3 v4)) parent nextMachine) := by
  obtain ⟨first,second⟩ := PointerAddLanguageGuardStorage.guardStorageLive options limits
    (remaining+1) span (older.push root) frame machine body location v3 v4 dead3 dead4 noClocks
  let pre := ready frame v3 v4
  have preSize : 4 < pre.locals.size := by rw [readySize]; exact v4
  have preLive : pre.locals[4].value = .live (.immediate .uninit) := by
    simp [pre,ready,SourceSteps.liveFrame]
  have preUncached : pre.locals[4].layout = none := by
    simp [pre,ready,SourceSteps.liveFrame,Array.getElem_set,uncached4]
  let before := LanguageZeroEntryFacts.pushed options.userRelevantCrates
    (guardState options remaining span older root frame machine v3 v4)
    (guardDestination older root frame v3 v4)
  have selected : FrameRelevance.top before.stack thread.topUserRelevantFrame = some older.size :=
    by simp [FrameRelevance.top,top]
  have cachedRoot : before.stack.frames[older.size]? = some root := by
    dsimp only [before,LanguageZeroEntryFacts.pushed,guardState,Storage.withCurrent]
    rw [Array.getElem?_push_lt (by simp only [Array.size_push]; omega)]
    simp [Array.getElem_push]
  have enter := PointerAddLanguageGuardStep.step options limits remaining budget callFuel span source debug
    (older.push root) pre machine body identity callee rfl preSize preLive preUncached noClocks
    noRace backend ghost tracker tracked thread older.size root active selected cachedRoot unchecked noGc fixed
  exact .next first (.next second (.next enter (.refl _)))

end DuplicatePrefix.PointerAddGuardEntryCurrent

#print axioms DuplicatePrefix.PointerAddGuardEntryCurrent.reaches_guard

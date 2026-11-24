import duplicate_prefix.LanguageGuardCurrentRuntime
import duplicate_prefix.LanguageGuardCurrentReturn
import duplicate_prefix.SuccessfulTrace
import duplicate_prefix.LocalDirectness

namespace DuplicatePrefix.LanguageGuardCurrentLeafTrace
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open LanguageGuardCurrentReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem returns_false
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 0 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[0].value = .live (.immediate old))
    (uncached : frame.locals[0].layout = none)
    (body : frame.body = LanguageGuardCurrentFacts.leafBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.leafBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.leafCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (callerValid : 1 < caller.locals.size)
    (callerLive : caller.locals[1].value = .live (.immediate .uninit))
    (callerCache : caller.locals[1].layout = some RootCompilerFacts.boolLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (direct : CopyHelperCleanup.AllImmediate frame) (va : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (borrowFrame : FrameState) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let written := {ActualLocalCopy.written frame 0 RootCompilerFacts.boolLayout valid
      (.scalar (.fromBool false)) with location := .mir ⟨0,1⟩}
    let after := poppedMachine frames caller written
      (SourceControl.accounted config.terminators (Storage.withCurrent (frames.push caller) written machine)).machine
      (thread.topUserRelevantFrame.getD (frames.push caller).size)
    SuccessfulTrace.Trace config limits (Storage.withCurrent (frames.push caller) frame machine)
      (Storage.withCurrent frames (returnedCallerFrame caller .runtimeGuard callerValid target) after) := by
  intro config written after
  have assign := LanguageGuardCurrentRuntime.runtimeGuardAssignment options limits remaining span debug fuel budget
    (frames.push caller) frame machine valid old live uncached body identity callee location noClocks ghost shallow
  have stillValid : 0 < written.locals.size := by
    simpa [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using valid
  have live' : written.locals[0].value = .live (.immediate (.scalar (.fromBool false))) := by
    simp [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have cache' : written.locals[0].layout = some RootCompilerFacts.boolLayout := by
    simp [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have direct' : CopyHelperCleanup.AllImmediate written :=
    LocalDirectness.written_at frame 0 _ _ valid _ direct
  have exit := return_step options limits remaining span debug fuel budget
    frames caller written machine .runtimeGuard body rfl stillValid live' cache' noClocks
    callerValid callerLive callerCache callerClocks destination target unwind continuation
    direct' va tracker borrowFrame tracked frameTracked empty thread active unchecked noGc fixed ghost shallow
  exact .next assign (.next exit (.refl _))

end DuplicatePrefix.LanguageGuardCurrentLeafTrace

#print axioms DuplicatePrefix.LanguageGuardCurrentLeafTrace.returns_false

import duplicate_prefix.LanguageGuardCurrentParentTail
import duplicate_prefix.PopActive

namespace DuplicatePrefix.LanguageGuardCurrentParentExit
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open LanguageGuardCurrentReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem returns_false_with_cache
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.parentBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.parentCall.callee)
    (location : frame.location = .mir ⟨1,0⟩)
    (valid0 : 0 < frame.locals.size) (valid1 : 1 < frame.locals.size) (valid2 : 2 < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit)) (cache0 : frame.locals[0].layout = none)
    (live1 : frame.locals[1].value = .live (.immediate (.scalar (.fromBool false))))
    (cache1 : frame.locals[1].layout = some RootCompilerFacts.boolLayout)
    (unit : Immediate Provenance) (live2 : frame.locals[2].value = .live (.immediate unit))
    (noClocks : frame.extra.dataRace = none) (tracker : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some tracker) (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (site : Site) (returnSite : site = .languageGuard ∨ site = .copyLanguageGuard)
    (callerValid : callerSlot site < caller.locals.size)
    (callerLive : caller.locals[callerSlot site].value = .live (.immediate .uninit))
    (callerCache : caller.locals[callerSlot site].layout = some RootCompilerFacts.boolLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller (callerSlot site) RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (direct : CopyHelperCleanup.AllImmediate frame) (va : frame.vaList = #[])
    (borrowFrame : FrameState) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ after threadAfter, SuccessfulTrace.Trace config limits
      (Storage.withCurrent (frames.push caller) frame machine)
      (Storage.withCurrent frames (returnedCallerFrame caller site callerValid target) after) ∧
      after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
      after.user.addresses = machine.user.addresses ∧ after.dataRace = machine.dataRace ∧
      after.user.payload.ghost = false ∧ after.user.payload.validation = .Shallow ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      after.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      after.threads.fixedScheduling = true ∧
      (config.terminators.getControl after.user).checkedArithmetic = false ∧
      (config.terminators.getControl after.user).gcInterval = 0 ∧
      after.threads.activeThread? = some threadAfter ∧
      (∀ earlier, thread.topUserRelevantFrame = some earlier → earlier < frames.size →
        after.threads.activeThread? = some thread) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let tick := PointerAddCurrentReturn.accountedMachine options remaining span
  let ticked := tick (tick machine)
  obtain ⟨done, history, shape⟩ := LanguageGuardCurrentParentTail.from_runtime_return
    options limits remaining span debug fuel budget (frames.push caller) frame machine body identity callee
    location valid0 valid1 valid2 live0 cache0 live1 cache1 unit live2 noClocks tracker tracked mode ghost shallow unchecked noGc fixed
  have code : done.body = bodyAt site := by
    rcases returnSite with rfl | rfl <;> exact shape.body.trans body
  have pc : done.location = .mir ⟨returnBlock site,1⟩ := by
    rcases returnSite with rfl | rfl <;> exact shape.location
  have at0 := (Array.getElem?_eq_some_iff.mp shape.output).2
  have valid : 0 < done.locals.size := by rw [shape.size]; exact valid0
  have clock (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    cfg.terminators.getControl (tick before).user = TerminatorClock.advance (cfg.terminators.getControl before.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have tickedGhost : ticked.user.payload.ghost = false := by
    simp only [ticked,tick,PointerAddCurrentReturn.accounted_ghost]
    exact ghost
  have tickedShallow : ticked.user.payload.validation = .Shallow := by
    simp only [ticked,tick,PointerAddCurrentReturn.accounted_validation]
    exact shallow
  have tickedUnchecked : (cfg.terminators.getControl ticked.user).checkedArithmetic = false := by
    rw [show ticked = tick (tick machine) from rfl,clock,clock]
    exact unchecked
  have tickedNoGc : (cfg.terminators.getControl ticked.user).gcInterval = 0 := by
    rw [show ticked = tick (tick machine) from rfl,clock,clock]
    exact noGc
  have returned := return_step options limits remaining span debug fuel budget frames caller done ticked site
    code pc valid (by rw [at0]) (by rw [at0]) (by rw [shape.extra];exact noClocks)
    callerValid callerLive callerCache callerClocks (by rw [shape.returnPlace];exact destination)
    target unwind (shape.continuation.trans continuation) (shape.direct direct) (shape.varargs.trans va)
    tracker borrowFrame tracked (by rw [shape.extra];exact frameTracked) empty
    thread active tickedUnchecked tickedNoGc fixed tickedGhost tickedShallow
  let index := thread.topUserRelevantFrame.getD (frames.push caller).size
  let after := poppedMachine frames caller done (tick ticked) index
  have fields : after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
      after.dataRace = machine.dataRace ∧ after.threads.fixedScheduling = true := by
    unfold after poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact ⟨rfl,rfl,rfl,fixed⟩
  have afterUser : after.user = (tick ticked).user := popped_user frames caller done _ _
  have userFields : after.user.addresses = machine.user.addresses ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      after.user.payload.payload.user.types = machine.user.payload.payload.user.types := by
    rw [afterUser]
    unfold ticked tick PointerAddCurrentReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have afterGhost : after.user.payload.ghost = false := by
    rw [afterUser]
    exact (PointerAddCurrentReturn.accounted_ghost options remaining span ticked).trans tickedGhost
  have afterShallow : after.user.payload.validation = .Shallow := by
    rw [afterUser]
    exact (PointerAddCurrentReturn.accounted_validation options remaining span ticked).trans tickedShallow
  have afterUnchecked : (cfg.terminators.getControl after.user).checkedArithmetic = false := by
    rw [afterUser,clock]
    exact tickedUnchecked
  have afterNoGc : (cfg.terminators.getControl after.user).gcInterval = 0 := by
    rw [afterUser,clock]
    exact tickedNoGc
  obtain ⟨threadAfter,afterActive⟩ :=
    PopActive.after_relevance_at_active (frames.push caller) done (tick ticked) index thread active
  have keepThread (earlier : Nat) (cached : thread.topUserRelevantFrame = some earlier)
      (bound : earlier < frames.size) : after.threads.activeThread? = some thread := by
    have noPop : index ≠ (frames.push caller).size := by
      simp [index,cached]
      omega
    unfold after poppedMachine GenericPopFrame.afterRelevanceAt
    rw [if_neg noPop]
    exact active
  exact ⟨after,threadAfter,SuccessfulTrace.append history (.next returned (.refl _)),
    fields.1,fields.2.1,userFields.1,fields.2.2.1,afterGhost,afterShallow,userFields.2.1,userFields.2.2.1,userFields.2.2.2,
    fields.2.2.2,afterUnchecked,afterNoGc,afterActive,keepThread⟩

end DuplicatePrefix.LanguageGuardCurrentParentExit

#print axioms DuplicatePrefix.LanguageGuardCurrentParentExit.returns_false_with_cache

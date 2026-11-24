import duplicate_prefix.RootSuccessToReturn

namespace DuplicatePrefix.RootPositiveReturnContinuation
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Memory Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

abbrev State := MachineHooks.State MiriMemoryKind Machine.RootUser

/-- Compose the eight cleanup statements, the jump to the actual return block
and the caller-specific copy-out step. The last step receives the exact
cleaned frame, including its cached true Boolean and unmodified return place. -/
theorem completes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (size : frame.locals.size = 25) (temp15 temp18 temp19 temp21 temp24 : Immediate Provenance)
    (slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (slot15 : frame.locals[15]? = some ⟨.live (.immediate temp15),some CopyCompilerFacts.destPointerLayout⟩)
    (slot17 : frame.locals[17]? = some ⟨.live (.immediate .uninit),none⟩)
    (slot18 : frame.locals[18]? = some ⟨.live (.immediate temp18),some CopyHelperUnit.layout⟩)
    (slot19 : frame.locals[19]? = some ⟨.live (.immediate temp19),some CopyCompilerFacts.sourcePointerLayout⟩)
    (slot21 : frame.locals[21]? = some ⟨.live (.immediate temp21),some CopyCompilerFacts.destPointerLayout⟩)
    (slot24 : frame.locals[24]? = some ⟨.live (.immediate temp24),some RootCompilerFacts.usizeLayout⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨9,0⟩) (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (initial : State)
    (history : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits initial
      (Storage.withCurrent frames frame machine))
    (post : State → Prop)
    (returnStep : ∀ done : CompilerFrameContext.ActualFrame,
      RootSuccessCleanupFacts.Shape frame done RootCompilerFacts.boolLayout (.scalar (.fromBool true)) →
      let config := PreparedContracts.actualConfig options () (remaining+1) span
      let start := Storage.withCurrent frames {done with location := .mir ⟨10,0⟩}
        (SourceControl.accounted config.terminators (Storage.withCurrent frames done machine)).machine
      ∃ final, ExecutionMachine.step config limits () start = (final,.ok true) ∧ post final) :
    ∃ final, SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits initial final ∧
      post final := by
  have s0 := (Array.getElem?_eq_some_iff.mp slot0).2
  have s15 := (Array.getElem?_eq_some_iff.mp slot15).2
  have s17 := (Array.getElem?_eq_some_iff.mp slot17).2
  have s18 := (Array.getElem?_eq_some_iff.mp slot18).2
  have s19 := (Array.getElem?_eq_some_iff.mp slot19).2
  have s21 := (Array.getElem?_eq_some_iff.mp slot21).2
  have s24 := (Array.getElem?_eq_some_iff.mp slot24).2
  obtain ⟨done,cleanup,shape⟩ := RootSuccessToReturn.reaches_return options limits remaining span source debug fuel validation
    frames frame machine size temp15 temp18 temp19 temp21 temp24
    (by rw [s0]) (by rw [s0]) (by rw [s15]) (by rw [s17]) (by rw [s17]) (by rw [s18])
    (by rw [s19]) (by rw [s21]) (by rw [s24]) body identity callee location noClocks
    tracker tracked mode ghost shallow unchecked noGc fixed
  obtain ⟨final,returned,satisfies⟩ := returnStep done shape
  exact ⟨final, SuccessfulTrace.append history (SuccessfulTrace.append cleanup (.next returned (.refl _))), satisfies⟩

#print axioms completes
end DuplicatePrefix.RootPositiveReturnContinuation

import duplicate_prefix.LanguageGuardCurrentSwitch
import duplicate_prefix.PointerAddCurrentGuardTail
import duplicate_prefix.PointerAddCurrentReturn
import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.PointerAddCurrentGuardSuffix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

/-- Follow the emitted false branch from the guard result to the offset block. -/
theorem from_false
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (located : frame.location = .mir ⟨1,0⟩)
    (valid3 : 3 < frame.locals.size) (valid4 : 4 < frame.locals.size)
    (live3 : frame.locals[3].value = .live (.immediate .uninit))
    (uncached3 : frame.locals[3].layout = none)
    (live4 : frame.locals[4].value = .live (.immediate (.scalar (.fromBool false))))
    (cached4 : frame.locals[4].layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let switched := {frame with location := .mir ⟨5,0⟩}
    let result := {ActualLocalCopy.written switched 3 CopyHelperUnit.layout valid3 .uninit with location := .mir ⟨6,0⟩}
    let afterSwitch := PointerAddCurrentReturn.accountedMachine options remaining span machine
    let afterGoto := PointerAddCurrentReturn.accountedMachine options remaining span afterSwitch
    SuccessfulTrace.Trace config limits (Storage.withCurrent older frame machine)
      (Storage.withCurrent older result afterGoto) ∧
    (∀ i, i ≠ 3 → result.locals[i]? = frame.locals[i]?) := by
  intro config switched result afterSwitch afterGoto
  have e1 := LanguageGuardCurrentSwitch.takeFalse options limits (remaining+1) span debug older frame machine
    .pointerAdd body located valid4 live4 cached4 noClocks ghost fixed unchecked noGc
  have ghost' := (PointerAddCurrentReturn.accounted_ghost options remaining span machine).trans ghost
  have shallow' := (PointerAddCurrentReturn.accounted_validation options remaining span machine).trans shallow
  have e2 := PointerAddCurrentGuardTail.guardTailAssignment options limits remaining span debug fuel budget
    older switched afterSwitch valid3 .uninit live3 uncached3 body identity callee rfl noClocks
    tracker tracked mode ghost' shallow'
  have newControl : config.terminators.getControl afterSwitch.user =
      TerminatorClock.advance (config.terminators.getControl machine.user) := by
    exact CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have unchecked' : (config.terminators.getControl afterSwitch.user).checkedArithmetic = false := by
    rw [newControl]
    exact unchecked
  have noGc' : (config.terminators.getControl afterSwitch.user).gcInterval = 0 := by
    rw [newControl]
    exact noGc
  let assigned := {ActualLocalCopy.written switched 3 CopyHelperUnit.layout valid3 .uninit with location := .mir ⟨5,1⟩}
  let block := PointerAddCurrentFacts.body.body.basicBlocks[5]'(by with_unfolding_all decide +kernel)
  have e3 := SourceControl.goto_step config limits () older assigned afterSwitch ⟨5,1⟩ block 6 rfl
    (by rw [show assigned.body = PointerAddCurrentFacts.body.body from body]; simp [block])
    (by with_unfolding_all rfl) (by exact ⟨#[],by with_unfolding_all rfl⟩)
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span)
    unchecked' noGc' fixed
  refine ⟨.next e1 (.next e2 (.next e3 (.refl _))), ?_⟩
  intro index distinct
  simp [result,switched,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm distinct]

end DuplicatePrefix.PointerAddCurrentGuardSuffix

#print axioms DuplicatePrefix.PointerAddCurrentGuardSuffix.from_false

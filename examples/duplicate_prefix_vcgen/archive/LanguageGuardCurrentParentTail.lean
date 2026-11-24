import duplicate_prefix.LanguageGuardCurrentControl
import duplicate_prefix.LanguageGuardCurrentFalse
import duplicate_prefix.LanguageGuardCurrentSwitch
import duplicate_prefix.LanguageGuardCurrentReturn
import duplicate_prefix.PointerAddCurrentReturn
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.LanguageGuardCurrentParentTail
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open LanguageGuardCurrentControl
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

structure Shape (before after : CompilerFrameContext.ActualFrame) : Prop where
  body : after.body = before.body
  identity : after.bodyIdentity = before.bodyIdentity
  callee : after.functionInstance = before.functionInstance
  extra : after.extra = before.extra
  returnPlace : after.returnPlace = before.returnPlace
  continuation : after.returnContinuation = before.returnContinuation
  varargs : after.vaList = before.vaList
  location : after.location = .mir ⟨4,1⟩
  size : after.locals.size = before.locals.size
  output : after.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  direct : CopyHelperCleanup.AllImmediate before → CopyHelperCleanup.AllImmediate after

/-- Run the actual language guard after its nested runtime guard returned false. -/
theorem from_runtime_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
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
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let firstTick := PointerAddCurrentReturn.accountedMachine options remaining span machine
    let finalMachine := PointerAddCurrentReturn.accountedMachine options remaining span firstTick
    ∃ result, SuccessfulTrace.Trace config limits (Storage.withCurrent older frame machine)
      (Storage.withCurrent older result finalMachine) ∧ Shape frame result := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let dead := SourceSteps.deadFrame frame ⟨1,0⟩ 2 valid2
  have e1 := retire options limits (remaining+1) span older frame machine body
    .unitTemporary location valid2 unit live2
  have valid1' : 1 < dead.locals.size := by simpa [dead,SourceSteps.deadFrame] using valid1
  have e2 := LanguageGuardCurrentSwitch.takeFalse options limits (remaining+1) span debug
    older dead machine .languageGuard body rfl valid1'
    (by simpa [dead,SourceSteps.deadFrame,Array.getElem_set,LanguageGuardCurrentSwitch.booleanSlot] using live1)
    (by simpa [dead,SourceSteps.deadFrame,Array.getElem_set,LanguageGuardCurrentSwitch.booleanSlot] using cache1)
    noClocks ghost fixed unchecked noGc
  let firstTick := PointerAddCurrentReturn.accountedMachine options remaining span machine
  let switched := {dead with location := .mir ⟨3,0⟩}
  have valid0' : 0 < switched.locals.size := by simpa [switched,dead,SourceSteps.deadFrame] using valid0
  have ghost' := (PointerAddCurrentReturn.accounted_ghost options remaining span machine).trans ghost
  have shallow' := (PointerAddCurrentReturn.accounted_validation options remaining span machine).trans shallow
  have e3 := LanguageGuardCurrentFalse.guardFalseAssignment options limits remaining span debug fuel budget
    older switched firstTick valid0' .uninit
    (by simpa [switched,dead,SourceSteps.deadFrame,Array.getElem_set] using live0)
    (by simpa [switched,dead,SourceSteps.deadFrame,Array.getElem_set] using cache0)
    body identity callee rfl noClocks tracker tracked mode ghost' shallow'
  let assigned := {ActualLocalCopy.written switched 0 RootCompilerFacts.boolLayout valid0'
    (.scalar (.fromBool false)) with location := .mir ⟨3,1⟩}
  have clock : cfg.terminators.getControl firstTick.user =
      TerminatorClock.advance (cfg.terminators.getControl machine.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have unchecked' : (cfg.terminators.getControl firstTick.user).checkedArithmetic = false := by
    rw [clock]
    exact unchecked
  have noGc' : (cfg.terminators.getControl firstTick.user).gcInterval = 0 := by
    rw [clock]
    exact noGc
  have e4 := gotoRetirement options limits (remaining+1) span older assigned firstTick body
    rfl fixed unchecked' noGc'
  let finalMachine := PointerAddCurrentReturn.accountedMachine options remaining span firstTick
  let beforeRetirement := {assigned with location := .mir ⟨4,0⟩}
  have validFinal1 : 1 < beforeRetirement.locals.size := by
    simpa [beforeRetirement,assigned,switched,dead,SourceSteps.deadFrame,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout] using valid1
  have liveFinal1 : beforeRetirement.locals[1].value = .live (.immediate (.scalar (.fromBool false))) := by
    simpa [beforeRetirement,assigned,switched,dead,SourceSteps.deadFrame,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout,Array.getElem_set] using live1
  let result := SourceSteps.deadFrame beforeRetirement ⟨4,0⟩ 1 validFinal1
  have e5 := retire options limits (remaining+1) span older beforeRetirement finalMachine body
    .guardValue rfl validFinal1 (.scalar (.fromBool false)) liveFinal1
  refine ⟨result,.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.refl _))))),?_⟩
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · simp [result,beforeRetirement,assigned,switched,dead,SourceSteps.deadFrame,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout]
  · simp [result,beforeRetirement,assigned,switched,dead,SourceSteps.deadFrame,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout]
  · intro all
    have deadDirect : CopyHelperCleanup.AllImmediate switched :=
      LocalDirectness.dead frame ⟨1,0⟩ 2 valid2 all
    have assignedDirect : CopyHelperCleanup.AllImmediate beforeRetirement :=
      LocalDirectness.written_at switched 0 RootCompilerFacts.boolLayout
        (.scalar (.fromBool false)) valid0' ⟨4,0⟩ deadDirect
    exact LocalDirectness.dead beforeRetirement ⟨4,0⟩ 1 validFinal1 assignedDirect

end DuplicatePrefix.LanguageGuardCurrentParentTail

#print axioms DuplicatePrefix.LanguageGuardCurrentParentTail.from_runtime_return

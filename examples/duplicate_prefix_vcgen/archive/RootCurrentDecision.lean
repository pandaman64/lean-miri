import duplicate_prefix.LocalDirectness
import duplicate_prefix.RootGuardStatements
import duplicate_prefix.RootGuardSwitch
import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.RootCurrentDecision
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open SuccessfulTrace
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def usizeValue (value : UInt64) : LocalValue Provenance :=
  .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 value))))

private def dividedFrame (frame : CompilerFrameContext.ActualFrame) (len : UInt64)
    (capacity : 11 < frame.locals.size) : CompilerFrameContext.ActualFrame := by
  have valid : 10 < frame.locals.size := by omega
  exact {(ActualLocalCopy.written frame 10 RootCompilerFacts.usizeLayout valid
    (.scalar (.fromScalarInt (.ofUInt64 (len/2))))) with location := .mir ⟨4,1⟩}

private def retiredFrame (frame : CompilerFrameContext.ActualFrame) (len : UInt64)
    (capacity : 11 < frame.locals.size) : CompilerFrameContext.ActualFrame :=
  SourceSteps.deadFrame (dividedFrame frame len capacity) ⟨4,1⟩ 11
    (by simpa [dividedFrame, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using capacity)

private def comparedFrame (frame : CompilerFrameContext.ActualFrame) (len count : UInt64)
    (capacity : 11 < frame.locals.size) : CompilerFrameContext.ActualFrame := by
  have valid : 8 < frame.locals.size := by omega
  have retiredValid : 8 < (retiredFrame frame len capacity).locals.size := by
    simpa [retiredFrame, dividedFrame, SourceSteps.deadFrame, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout] using valid
  exact {(ActualLocalCopy.written (retiredFrame frame len capacity) 8 RootCompilerFacts.boolLayout
    retiredValid (.scalar (.fromBool (count > len / 2)))) with location := .mir ⟨4,3⟩}

def decisionFrame (frame : CompilerFrameContext.ActualFrame) (len count : UInt64)
    (capacity : 11 < frame.locals.size) : CompilerFrameContext.ActualFrame :=
  {comparedFrame frame len count capacity with location := .mir ⟨if count > len / 2 then 5 else 6,0⟩}

def decisionMachine (config : CanonicalConfigFacts.RootConfig)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (capacity : 11 < frame.locals.size) :=
  (SourceControl.accounted config.terminators (Storage.withCurrent older
    (comparedFrame frame len count capacity) machine)).machine

theorem decisionFrameShape (frame : CompilerFrameContext.ActualFrame) (len count : UInt64)
    (capacity : 11 < frame.locals.size) :
    let decided := decisionFrame frame len count capacity
    decided.locals.size = frame.locals.size ∧ decided.body = frame.body ∧
    decided.bodyIdentity = frame.bodyIdentity ∧ decided.functionInstance = frame.functionInstance ∧
    decided.extra = frame.extra ∧ (∀ id, id ≠ 8 → id ≠ 10 → id ≠ 11 →
      decided.locals[id]? = frame.locals[id]?) ∧
    decided.locals[8]? = some ⟨.live (.immediate (.scalar (.fromBool (count > len / 2)))),
      some RootCompilerFacts.boolLayout⟩ ∧
    decided.locals[10]? = some ⟨usizeValue (len/2),some RootCompilerFacts.usizeLayout⟩ := by
  intro decided
  have bound8 : 8 < frame.locals.size := by omega
  have bound10 : 10 < frame.locals.size := by omega
  simp [decided,decisionFrame,comparedFrame,retiredFrame,dividedFrame,ActualLocalCopy.written,
    SourceSteps.deadFrame,LocalPlaces.cachePlaceLayout,Array.getElem?_set,bound8,bound10,
    usizeValue]
  intro id a b c
  simp [Ne.symm a,Ne.symm b,Ne.symm c]

theorem decisionImmediate (frame : CompilerFrameContext.ActualFrame) (len count : UInt64)
    (capacity : 11 < frame.locals.size) (direct : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate (decisionFrame frame len count capacity) := by
  have divided : CopyHelperCleanup.AllImmediate (dividedFrame frame len capacity) := by
    unfold dividedFrame
    exact LocalDirectness.written_at frame 10 _ _ _ _ direct
  have retired : CopyHelperCleanup.AllImmediate (retiredFrame frame len capacity) :=
    LocalDirectness.dead (dividedFrame frame len capacity) ⟨4,1⟩ 11 _ divided
  unfold decisionFrame comparedFrame
  exact LocalDirectness.written_at (retiredFrame frame len capacity) 8 _ _ _ _ retired

theorem decisionStatic (frame : CompilerFrameContext.ActualFrame) (len count : UInt64)
    (capacity : 11 < frame.locals.size) :
    let output := decisionFrame frame len count capacity
    output.trackCallerArg = frame.trackCallerArg ∧
    output.returnPlace = frame.returnPlace ∧ output.returnContinuation = frame.returnContinuation ∧
    output.vaList = frame.vaList ∧ output.localsIdentity = frame.localsIdentity := by
  simp [decisionFrame,comparedFrame,retiredFrame,dividedFrame,SourceSteps.deadFrame,
    ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]

theorem decisionMachineShape (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (capacity : 11 < frame.locals.size) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let decided := decisionMachine cfg older frame machine len count capacity
    decided.memory = machine.memory ∧ decided.borrowTracker = machine.borrowTracker ∧
      decided.dataRace = machine.dataRace ∧ decided.threads = machine.threads ∧
      decided.user.addresses = machine.user.addresses ∧
      decided.user.payload.ghost = machine.user.payload.ghost ∧
      decided.user.payload.validation = machine.user.payload.validation := by
  intro cfg decided
  unfold decided decisionMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem decisionPolicy (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame next : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (capacity : 11 < frame.locals.size) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let charged := decisionMachine cfg older frame machine len count capacity
    (EvalProjectionMachine.arrays.get (Storage.withCurrent older next charged)) =
      (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)) ∧
    (cfg.terminators.getControl charged.user).checkedArithmetic =
      (cfg.terminators.getControl machine.user).checkedArithmetic ∧
    (cfg.terminators.getControl charged.user).gcInterval =
      (cfg.terminators.getControl machine.user).gcInterval ∧
    charged.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
    charged.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  intro cfg charged
  unfold charged decisionMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem evaluateCurrentBounds
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (capacity : 11 < frame.locals.size)
    (hasLength : frame.locals[11].value = usizeValue len)
    (hasCount : (frame.locals[9]'(by omega)).value = usizeValue count)
    (lengthCached : frame.locals[11].layout = some RootCompilerFacts.usizeLayout)
    (countCached : (frame.locals[9]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (halfLive : (frame.locals[10]'(by omega)).value = .live (.immediate .uninit))
    (halfUncached : (frame.locals[10]'(by omega)).layout = none)
    (boundLive : (frame.locals[8]'(by omega)).value = .live (.immediate .uninit))
    (boundUncached : (frame.locals[8]'(by omega)).layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨4,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    Trace config limits (Storage.withCurrent older frame machine)
      (Storage.withCurrent older (decisionFrame frame len count capacity)
        (decisionMachine config older frame machine len count capacity)) := by
  intro config
  have valid10 : 10 < frame.locals.size := by omega
  let divided := {(ActualLocalCopy.written frame 10 RootCompilerFacts.usizeLayout valid10
    (.scalar (.fromScalarInt (.ofUInt64 (len/2))))) with location := FrameLocation.mir ⟨4,1⟩}
  have stepDiv := RootGuardStatements.division options limits remaining span source debug fuel budget
    older frame machine len capacity valid10 hasLength lengthCached halfLive halfUncached
    body identity callee located noClocks ghost shallow
  have valid11 : 11 < divided.locals.size := by
    simpa [divided, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using capacity
  have sameLength : divided.locals[11].value = usizeValue len := by
    simp [divided, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout, Array.getElem_set, hasLength]
  have blockBound : 4 < RootBody.reflected.body.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := RootBody.reflected.body.body.basicBlocks[4]'blockBound
  have stmtBound : 1 < block.statements.size := by with_unfolding_all change 1 < 3; decide
  let stmt := block.statements[1]'stmtBound
  have blockAt : divided.body.basicBlocks[4]? = some block := by
    simpa [divided, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using
      (show frame.body.basicBlocks[4]? = some block by simp [body, block, blockBound])
  let retired := SourceSteps.deadFrame divided ⟨4,1⟩ 11 valid11
  have stepDead := SourceSteps.storage_dead_exact config limits () older divided machine ⟨4,1⟩ block stmt
    11 (.scalar (.fromScalarInt (.ofUInt64 len))) rfl blockAt (by simp [stmt])
    (by with_unfolding_all rfl) valid11 (by decide) sameLength
  have retiredSize : retired.locals.size = frame.locals.size := by
    simp [retired, SourceSteps.deadFrame, divided, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout]
  have v8 : 8 < retired.locals.size := by rw [retiredSize]; omega
  have v9 : 9 < retired.locals.size := by rw [retiredSize]; omega
  have v10 : 10 < retired.locals.size := by rw [retiredSize]; omega
  have countStill : retired.locals[9].value = usizeValue count := by
    simp [retired, SourceSteps.deadFrame, divided, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout, Array.getElem_set, hasCount]
  have halfStored : retired.locals[10].value = usizeValue (len/2) := by
    simp [retired, SourceSteps.deadFrame, divided, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout, Array.getElem_set, usizeValue]
  have countStillCached : retired.locals[9].layout = some RootCompilerFacts.usizeLayout := by
    simp [retired, SourceSteps.deadFrame, divided, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout, Array.getElem_set, countCached]
  have halfCached : retired.locals[10].layout = some RootCompilerFacts.usizeLayout := by
    simp [retired, SourceSteps.deadFrame, divided, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout, Array.getElem_set]
  have checkLive : retired.locals[8].value = .live (.immediate .uninit) := by
    simp [retired, SourceSteps.deadFrame, divided, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout, Array.getElem_set, boundLive]
  have checkUncached : retired.locals[8].layout = none := by
    simp [retired, SourceSteps.deadFrame, divided, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout, Array.getElem_set, boundUncached]
  have stepCompare := RootGuardStatements.greater_than options limits remaining span debug fuel budget
    older retired machine count (len/2) v9 v10 v8 countStill halfStored countStillCached halfCached
    checkLive checkUncached body identity callee noClocks ghost shallow rfl
  let compared := {(ActualLocalCopy.written retired 8 RootCompilerFacts.boolLayout v8
    (.scalar (.fromBool (count > len / 2)))) with location := FrameLocation.mir ⟨4,3⟩}
  have boolValid : 8 < compared.locals.size := by
    simpa [compared, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using v8
  have boolStored : compared.locals[8].value = .live (.immediate (.scalar (.fromBool (count > len / 2)))) := by
    simp [compared, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout]
  have boolCached : compared.locals[8].layout = some RootCompilerFacts.boolLayout := by
    simp [compared, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout]
  have stepSwitch := RootGuardSwitch.stepWithBound options limits remaining span debug older compared machine
    (count > len / 2) body identity callee rfl boolValid boolStored boolCached
    noClocks ghost unchecked noGc fixed
  refine .next stepDiv (.next stepDead (.next stepCompare (.next ?_ (.refl _))))
  simpa [decisionFrame, decisionMachine, comparedFrame, retiredFrame, dividedFrame,
    compared, retired, divided, decide_eq_true_eq] using stepSwitch

end DuplicatePrefix.RootCurrentDecision

#print axioms DuplicatePrefix.RootCurrentDecision.evaluateCurrentBounds

#print axioms DuplicatePrefix.RootCurrentDecision.decisionImmediate
#print axioms DuplicatePrefix.RootCurrentDecision.decisionStatic
#print axioms DuplicatePrefix.RootCurrentDecision.decisionFrameShape
#print axioms DuplicatePrefix.RootCurrentDecision.decisionMachineShape

#print axioms DuplicatePrefix.RootCurrentDecision.decisionPolicy

import duplicate_prefix.RootZeroCompleteState
import duplicate_prefix.RootBlock0
import duplicate_prefix.SuccessfulTrace
import duplicate_prefix.RootLenPrefix

namespace DuplicatePrefix.RootNonzeroEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private def guardFrame (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 25) (n : UInt64) :=
  let storage := RootPrefix.afterStorageFrame frame size
  let count := RootCopyCount.postFrame storage (by simp [storage,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,size]) n
  RootEqStepSuccess.postFrame count (by simp [count,storage,RootCopyCount.postFrame,RootCopyCount.writeFrame,
    LocalPlaces.cachePlaceLayout,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,size]) n

/-- Execute the emitted initial guard for any nonzero count and preserve the
other locals and borrowed state for the retained slice-length path. -/
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64) (positive : n ≠ 0)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (uncached3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : ZeroImmediateFacts.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent older frame machine)
        (Storage.withCurrent older result (tick options remaining span machine)) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.trackCallerArg = frame.trackCallerArg ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨2,0⟩ ∧
      result.locals[3]?.map (·.value) = some (.live (.immediate .uninit)) ∧
      result.locals[3]?.map (·.layout) = some none ∧
      result.locals[4]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[5]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ index, index < 3 ∨ 5 < index → result.locals[index]? = frame.locals[index]?) ∧
      ZeroImmediateFacts.AllImmediate result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let guard := guardFrame frame size n
  obtain ⟨s1,s2,s3,s4,s5,h1,h2,h3,h4,h5,_,lastEq,_⟩ := RootBlock0.actual_first_block_statements
    options limits remaining span source debugOff older frame machine n body identity location callee size dead3 dead4 dead5
    uncached4 uncached5 (by rw [size];decide) live2 cached2 noClocks tracker tracked defaultMode ghost shallow fuel fuelEq
  have last : s5 = Storage.withCurrent older guard machine := by simpa only [guard,guardFrame] using lastEq
  rw [last] at h5
  have storageSize : guard.locals.size = 25 := by
    simp [guard,guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
      RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size]
  have valid4 : (4 : MIR.LocalId) < guard.locals.size := by rw [storageSize]; decide
  have eqFalse : (n == 0) = false := by simpa using positive
  have live4 : guard.locals[4].value = .live (.immediate (.scalar (.fromBool (n == 0)))) := by
    simp [guard,guardFrame,RootEqStepSuccess.postFrame]
  have cache4 : guard.locals[4].layout = some RootCompilerFacts.boolLayout := by
    simp [guard,guardFrame,RootEqStepSuccess.postFrame]
  have guardShape : guard.body = frame.body ∧ guard.bodyIdentity = frame.bodyIdentity ∧
      guard.functionInstance = frame.functionInstance ∧ guard.location = .mir ⟨0,5⟩ ∧
      guard.extra.dataRace = frame.extra.dataRace ∧ guard.returnPlace = frame.returnPlace ∧
      guard.returnContinuation = frame.returnContinuation ∧ guard.vaList = frame.vaList ∧
      guard.localsIdentity = frame.localsIdentity ∧ guard.trackCallerArg = frame.trackCallerArg := by
    simp [guard, guardFrame, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, RootCopyCount.postFrame,
      RootCopyCount.writeFrame, RootEqStepSuccess.postFrame, LocalPlaces.cachePlaceLayout]
  obtain ⟨guardBody, guardIdentity, guardCallee, guardLocation, guardClocks, guardPlace,
    guardContinuation, guardVa, guardLocalsId, guardTrack⟩ := guardShape
  have jump := RootZeroCompleteSwitch.switch_exact options limits remaining span debugOff older guard machine n
    (guardBody.trans body) (guardIdentity.trans identity) (guardCallee.trans callee) guardLocation
    storageSize valid4 live4 cache4 (guardClocks.trans noClocks) ghost unchecked noGc fixed
  let result := {guard with location := FrameLocation.mir ⟨2,0⟩}
  let next := tick options remaining span machine
  have jump' : ExecutionMachine.step config limits () (Storage.withCurrent older guard machine) =
      (Storage.withCurrent older result next,.ok true) := by
    simpa only [result,next,tick,config,SourceControl.accounted,Storage.withCurrent,eqFalse,Bool.false_eq_true,↓reduceIte] using jump
  refine ⟨result, .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.next jump' (.refl _)))))),
    guardBody,guardIdentity,guardCallee,?_,guardPlace,guardContinuation,guardVa,guardLocalsId,guardTrack,storageSize,rfl,?_,?_,?_,?_,?_,?_⟩
  · simp [result, guard, guardFrame, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, RootCopyCount.postFrame,
      RootCopyCount.writeFrame, RootEqStepSuccess.postFrame, LocalPlaces.cachePlaceLayout]
  · simp [result,guard,guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
      RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size]
  · simp [result,guard,guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
      RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size,uncached3]
  · simp [result,guard,guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
      RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size,eqFalse]
  · simp [result,guard,guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
      RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size]
  · intro index outside
    have three : index ≠ 3 := by omega
    have four : index ≠ 4 := by omega
    have five : index ≠ 5 := by omega
    simp [result,guard,guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
      RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size,eqFalse,
      Ne.symm three, Ne.symm four, Ne.symm five]
  · change ZeroImmediateFacts.AllImmediate guard
    unfold guard guardFrame
    exact all_guard _ _ _ (all_count _ _ _ (all_live _ _ _ _ (all_live _ _ _ _ (all_live _ _ _ _ all))))

/-- Reach the actual shared-reference assignment following the nonzero guard. -/
theorem reachesSharedReference
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64) (positive : n ≠ 0)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (uncached3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : ZeroImmediateFacts.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let nextMachine := tick options remaining span machine
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent older frame machine)
        (Storage.withCurrent older result nextMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.trackCallerArg = frame.trackCallerArg ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨2,11⟩ ∧
      result.locals[0]? = frame.locals[0]? ∧ result.locals[1]? = frame.locals[1]? ∧
      result.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[13]? = frame.locals[13]? ∧
      ZeroImmediateFacts.AllImmediate result := by
  let nextMachine := tick options remaining span machine
  obtain ⟨middle, first, bodyM, identityM, calleeM, extraM, placeM, continuationM, vaM, localsIdM,
    trackM, sizeM, locationM, slot3, cache3, slot4, slot5, other, allM⟩ :=
    executes options limits remaining span source debugOff fuel fuelEq older frame machine body identity callee location
      size n positive dead3 uncached3 dead4 dead5 uncached4 uncached5 live2 cached2 noClocks all tracker tracked
      defaultMode ghost shallow unchecked noGc fixed
  have getSlot (index : Nat) (inside : index < middle.locals.size) (initial : index < frame.locals.size)
      (outside : index < 3 ∨ 5 < index) : middle.locals[index] = frame.locals[index] :=
    Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans ((other index outside).trans (Array.getElem?_eq_getElem initial)))
  have v3 : 3 < middle.locals.size := by rw [sizeM]; decide
  have v4 : 4 < middle.locals.size := by rw [sizeM]; decide
  have v5 : 5 < middle.locals.size := by rw [sizeM]; decide
  rw [Array.getElem?_eq_getElem v3] at slot3 cache3
  have slot4' := Option.some.inj ((Array.getElem?_eq_getElem v4).symm.trans slot4)
  have slot5' := Option.some.inj ((Array.getElem?_eq_getElem v5).symm.trans slot5)
  have slot2' := getSlot 2 (by rw [sizeM]; decide) (by rw [size]; decide) (by decide)
  have unusedM : ∀ id (valid : id < middle.locals.size), 7 ≤ id → id ≤ 12 → middle.locals[id] = ⟨.dead,none⟩ := by
    intro id valid low high
    have validInitial : id < frame.locals.size := by omega
    exact (getSlot id valid validInitial (Or.inr (by omega))).trans (unused id validInitial low high)
  obtain ⟨result, ⟨second, bodyR, identityR, calleeR, extraR, placeR, continuationR, sizeR, locationR, slot0,
    slot1, _, slot7, slot8, slot9, slot10, slot11, slot12, slot13, vaR, localsIdR, allR⟩, trackR⟩ :=
    RootLenPrefix.executes_tracked options limits remaining span source debugOff fuel fuelEq older middle nextMachine n
      (.scalar (.fromBool false)) (.scalar (.fromScalarInt (.ofUInt64 n))) sizeM
      ((congrArg (·.value) slot2').trans live2) ((congrArg (·.layout) slot2').trans cached2)
      (Option.some.inj slot3) (Option.some.inj cache3) (congrArg (·.value) slot4') (congrArg (·.value) slot5')
      unusedM (bodyM.trans body) (identityM.trans identity) (calleeM.trans callee) locationM
      ((congrArg (·.dataRace) extraM).trans noClocks) tracker tracked defaultMode
      ((tick_ghost options remaining span machine).trans ghost) ((tick_shallow options remaining span machine).trans shallow) allM
  exact ⟨result, SuccessfulTrace.append first second, bodyR.trans bodyM, identityR.trans identityM, calleeR.trans calleeM,
    extraR.trans extraM, placeR.trans placeM, continuationR.trans continuationM, vaR.trans vaM, localsIdR.trans localsIdM, trackR.trans trackM,
    sizeR, locationR, slot0.trans (other 0 (by decide)), slot1.trans (other 1 (by decide)), slot7, slot8, slot9, slot10,
    slot11, slot12, slot13.trans (other 13 (by decide)), allR⟩

#print axioms executes
#print axioms reachesSharedReference
end DuplicatePrefix.RootNonzeroEntry

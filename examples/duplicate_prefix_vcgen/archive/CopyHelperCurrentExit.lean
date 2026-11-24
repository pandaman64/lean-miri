import duplicate_prefix.CopyHelperResult
import duplicate_prefix.CopyHelperCleanup
import duplicate_prefix.CopyHelperReturnDriver
import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.CopyHelperCurrentExit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- The current helper stores its unit result before retiring the copy operands
and returning to the caller. -/
theorem trace_exact
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨7,9⟩)
    (size : frame.locals.size = 17)
    (source dest : Scalar Provenance) (n : UInt64)
    (live14 : (frame.locals[14]'(by omega)).value = .live (.immediate (.scalar source)))
    (live15 : (frame.locals[15]'(by omega)).value = .live (.immediate (.scalar dest)))
    (live16 : (frame.locals[16]'(by omega)).value =
      .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerOld : Immediate Provenance)
    (callerLive : caller.locals[callerId].value = .live (.immediate callerOld))
    (callerCached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals,
      ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (defaultMode : tracker.retagMode = .Default)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ done returnedMachine,
      returnedMachine = GenericPopFrame.afterRelevanceAt (frames.push caller) done
        (ActualPopPlan.released (PointerAddCurrentReturn.accountedMachine options remaining span machine)
          finalMemory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD (frames.push caller).size) ∧
      returnedMachine.memory = finalMemory ∧
      SuccessfulTrace.Trace config limits
        (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {PointerAddCurrentReturn.writeFrame caller callerId .uninit callerValid with
            location := .mir ⟨target,0⟩} returnedMachine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let returnedLocal := CopyHelperSteps.advance
    (ActualLocalCopy.written frame 0 CopyHelperUnit.layout valid0 .uninit) ⟨7,9⟩
  have assigned := CopyHelperResult.step options limits remaining span debugOff fuel validationFuel
    (frames.push caller) frame machine .uninit valid0 live0 uncached0 sourceBody identity location
    callee noClocks tracker tracked defaultMode ghost shallow
  have resultSize : returnedLocal.locals.size = 17 := by
    simp [returnedLocal,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size]
  have resultSlot : returnedLocal.locals[0]? =
      some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ := by
    simp [returnedLocal,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have resultDirect : CopyHelperCleanup.AllImmediate returnedLocal :=
    CopyHelperCleanup.all_immediate_written frame 0 CopyHelperUnit.layout .uninit valid0 immediateLocals
  obtain ⟨next, next', done, s1, s2, s3, doneBody, doneId, doneCall, doneExtra, donePlace, doneCont,
      doneVars, _, doneSize, doneLoc, done0, doneDirect⟩ :=
    CopyHelperCleanup.actual_three_dead options limits (remaining+1) span (frames.push caller)
      returnedLocal machine source dest n resultSize sourceBody rfl
      (by simpa [returnedLocal,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live14)
      (by simpa [returnedLocal,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live15)
      (by simpa [returnedLocal,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live16)
      resultDirect
  have doneValue := (Array.getElem?_eq_some_iff.mp (done0.trans resultSlot)).2
  have validDone : (0 : MIR.LocalId) < done.locals.size := by rw [doneSize]; decide
  have ret := CopyHelperReturnDriver.return_step options limits remaining span debugOff fuel validationFuel
    frames caller done machine (doneBody.trans sourceBody) (doneId.trans identity) (doneCall.trans callee)
    doneLoc validDone (by rw [doneValue]) (by rw [doneValue]) (by rw [doneExtra]; exact noClocks)
    callerId callerValid callerOld callerLive callerCached callerClocks (by rw [donePlace]; exact destination)
    target unwindAction (by rw [doneCont]; exact continuation) doneDirect (by rw [doneVars]; exact varargs)
    tracker borrowFrame tracked (by rw [doneExtra]; exact frameTracked) finalMemory plan thread active
    unchecked noGc fixed ghost shallow
  let final := GenericPopFrame.afterRelevanceAt (frames.push caller) done
    (ActualPopPlan.released (PointerAddCurrentReturn.accountedMachine options remaining span machine)
      finalMemory tracker borrowFrame)
    (thread.topUserRelevantFrame.getD (frames.push caller).size)
  have finalMemoryEq : final.memory = finalMemory := by
    unfold final GenericPopFrame.afterRelevanceAt
    split <;> rfl
  exact ⟨done,final,rfl,finalMemoryEq,.next assigned (.next s1 (.next s2 (.next s3 (.next ret (.refl _)))))⟩

theorem trace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨7,9⟩)
    (size : frame.locals.size = 17)
    (source dest : Scalar Provenance) (n : UInt64)
    (live14 : (frame.locals[14]'(by omega)).value = .live (.immediate (.scalar source)))
    (live15 : (frame.locals[15]'(by omega)).value = .live (.immediate (.scalar dest)))
    (live16 : (frame.locals[16]'(by omega)).value =
      .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerOld : Immediate Provenance)
    (callerLive : caller.locals[callerId].value = .live (.immediate callerOld))
    (callerCached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals,
      ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (defaultMode : tracker.retagMode = .Default)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ returnedMachine, returnedMachine.memory = finalMemory ∧
      SuccessfulTrace.Trace config limits
        (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {PointerAddCurrentReturn.writeFrame caller callerId .uninit callerValid with
            location := .mir ⟨target,0⟩} returnedMachine) := by
  obtain ⟨_, returnedMachine, _, memoryEq, actualTrace⟩ :=
    trace_exact options limits remaining span debugOff fuel validationFuel frames caller frame machine
      sourceBody identity callee location size source dest n live14 live15 live16 valid0 live0 uncached0 noClocks
      callerId callerValid callerOld callerLive callerCached callerClocks destination target unwindAction
      continuation immediateLocals varargs tracker borrowFrame tracked frameTracked finalMemory plan defaultMode
      thread active unchecked noGc fixed ghost shallow
  exact ⟨returnedMachine,memoryEq,actualTrace⟩

#print axioms trace_exact
#print axioms trace
end DuplicatePrefix.CopyHelperCurrentExit

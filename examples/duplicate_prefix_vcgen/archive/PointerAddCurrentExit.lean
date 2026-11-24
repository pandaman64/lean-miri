import duplicate_prefix.PointerAddCurrentOffset
import duplicate_prefix.PointerAddCurrentStorage
import duplicate_prefix.RootOffsetQueries
import duplicate_prefix.SuccessfulTrace
import duplicate_prefix.PointerAddCurrentReturn

namespace DuplicatePrefix.PointerAddCurrentExit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- From the production Offset instruction through the normal pointer-add return. -/
theorem trace_exact
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (size : frame.locals.size = 12)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (pointer : (frame.locals[10]'(by omega)).value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (pointerLayout : (frame.locals[10]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (countValue : (frame.locals[11]'(by omega)).value =
      .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (countLayout : (frame.locals[11]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : frame.location = .mir ⟨6,6⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (callerId : Miri.MIR.LocalId)
    (callerValid0 : callerId < caller.locals.size)
    (callerLive0 : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerCached0 : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (borrowFrame : Miri.TreeBorrows.FrameState)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let value := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count)))
    ∃ done returnedMachine, returnedMachine = PointerAddCurrentReturn.poppedMachine frames caller done
        (PointerAddCurrentReturn.accountedMachine options remaining span machine)
        (thread.topUserRelevantFrame.getD (frames.push caller).size) ∧
      returnedMachine.memory = machine.memory ∧
      returnedMachine.borrowTracker = machine.borrowTracker ∧
      returnedMachine.user.addresses = machine.user.addresses ∧
      SuccessfulTrace.Trace config limits
      (Storage.withCurrent (frames.push caller) frame machine)
      (Storage.withCurrent frames
        {PointerAddCurrentReturn.writeFrame caller callerId (.scalar value) callerValid0 with
          location := .mir ⟨target,0⟩} returnedMachine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let result := Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count)))
  let raw := Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
  have v0 : (0 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have v10 : (10 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have v11 : (11 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  let written := {ActualLocalCopy.written frame 0 CopyCompilerFacts.destPointerLayout v0 (.scalar result) with
    location := .mir ⟨6,7⟩}
  have s1 := PointerAddCurrentOffset.offset options limits remaining span RootOffsetQueries.overflowLayout
    (RootOffsetQueries.overflow_query options (remaining+1) span) debugOff fuel validationFuel
    (frames.push caller) frame machine v10 v11 v0 id tag base offset count entry
    pointer pointerLayout countValue countLayout live0 uncached0 sourceBody identity callee location
    noClocks ghostFalse shallow cached present positive fits bounds
  have v11' : (11 : Miri.MIR.LocalId) < written.locals.size := by
    simpa [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using v11
  let deadCount := SourceSteps.deadFrame written ⟨6,7⟩ 11 v11'
  have wc : written.locals[11].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))) := by
    simpa [written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using countValue
  have s2 := PointerAddCurrentStorage.dead_count options limits remaining span (frames.push caller) written machine
    (show written.body = PointerAddCurrentFacts.body.body from sourceBody) rfl v11' _ wc
  have v10' : (10 : Miri.MIR.LocalId) < deadCount.locals.size := by
    simpa [deadCount,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,SourceSteps.deadFrame] using v10
  let done := SourceSteps.deadFrame deadCount ⟨6,8⟩ 10 v10'
  have dp : deadCount.locals[10].value = .live (.immediate (.scalar raw)) := by
    simpa [deadCount,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,SourceSteps.deadFrame,Array.getElem_set,raw]
      using pointer
  have s3 := PointerAddCurrentStorage.dead_pointer options limits remaining span (frames.push caller) deadCount machine
    (show deadCount.body = PointerAddCurrentFacts.body.body from sourceBody) rfl v10' _ dp
  have resultValid : (0 : Miri.MIR.LocalId) < done.locals.size := by
    simpa [done,deadCount,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,SourceSteps.deadFrame] using v0
  have resultSlot : done.locals[0]'resultValid =
      ⟨.live (.immediate (.scalar result)), some CopyCompilerFacts.destPointerLayout⟩ := by
    simp [done,deadCount,written,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set]
  have doneDirect : ∀ slot ∈ done.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    intro slot member memory
    obtain ⟨i,inBounds,localAt⟩ := Array.mem_iff_getElem.mp member
    subst slot
    by_cases a : i = 0
    · subst i
      rw [resultSlot]
      simp
    by_cases b : i = 10
    · subst i
      simp [done,SourceSteps.deadFrame]
    by_cases c : i = 11
    · subst i
      simp [done,deadCount,SourceSteps.deadFrame,Array.getElem_set]
    have priorBound : i < frame.locals.size := by
      simpa [done,deadCount,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,SourceSteps.deadFrame]
        using inBounds
    have untouched : done.locals[i] = frame.locals[i] := by
      simp [done,deadCount,written,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,SourceSteps.deadFrame,
        Array.getElem_set, Ne.symm a,Ne.symm b,Ne.symm c]
    rw [untouched]
    exact immediateLocals _ (Array.mem_iff_getElem.mpr ⟨i,priorBound,rfl⟩) memory
  have ret := PointerAddCurrentReturn.return_step options limits remaining span debugOff fuel validationFuel
    frames caller done machine result callerId sourceBody rfl resultValid
    (by rw [resultSlot]) (by rw [resultSlot]) noClocks
    callerValid0 callerLive0 callerCached0 callerClocks destination
    target unwindAction continuation doneDirect
    varargs tracker borrowFrame tracked
    frameTracked empty thread active unchecked noGc fixed ghostFalse shallow
  let final := PointerAddCurrentReturn.poppedMachine frames caller done
    (PointerAddCurrentReturn.accountedMachine options remaining span machine)
    (thread.topUserRelevantFrame.getD (frames.push caller).size)
  have memoryEq : final.memory = machine.memory := by
    unfold final PointerAddCurrentReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have trackerEq : final.borrowTracker = machine.borrowTracker := by
    unfold final PointerAddCurrentReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have addressesEq : final.user.addresses = machine.user.addresses := by
    dsimp only [final]
    rw [PointerAddCurrentReturn.popped_user]
    unfold PointerAddCurrentReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  exact ⟨done,final,rfl,memoryEq,trackerEq,addressesEq, .next s1 (.next s2 (.next s3 (.next ret (.refl _))))⟩

theorem trace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (size : frame.locals.size = 12)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (pointer : (frame.locals[10]'(by omega)).value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (pointerLayout : (frame.locals[10]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (countValue : (frame.locals[11]'(by omega)).value =
      .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (countLayout : (frame.locals[11]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : frame.location = .mir ⟨6,6⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (callerId : Miri.MIR.LocalId)
    (callerValid0 : callerId < caller.locals.size)
    (callerLive0 : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerCached0 : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (borrowFrame : Miri.TreeBorrows.FrameState)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let value := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count)))
    ∃ returnedMachine, returnedMachine.memory = machine.memory ∧
      returnedMachine.borrowTracker = machine.borrowTracker ∧
      returnedMachine.user.addresses = machine.user.addresses ∧
      SuccessfulTrace.Trace config limits
      (Storage.withCurrent (frames.push caller) frame machine)
      (Storage.withCurrent frames
        {PointerAddCurrentReturn.writeFrame caller callerId (.scalar value) callerValid0 with
          location := .mir ⟨target,0⟩} returnedMachine) := by
  obtain ⟨_, returnedMachine, _, memoryEq, trackerEq, addressEq, actualTrace⟩ :=
    trace_exact options limits remaining span debugOff fuel validationFuel frames caller frame machine
      id tag base offset count entry size live0 uncached0 pointer pointerLayout countValue countLayout
      sourceBody identity callee location noClocks tracker tracked ghostFalse shallow cached present
      positive fits bounds callerId callerValid0 callerLive0 callerCached0 callerClocks destination target
      unwindAction continuation immediateLocals varargs borrowFrame frameTracked empty thread active unchecked noGc fixed
  exact ⟨returnedMachine,memoryEq,trackerEq,addressEq,actualTrace⟩

#print axioms trace_exact
#print axioms trace
end DuplicatePrefix.PointerAddCurrentExit

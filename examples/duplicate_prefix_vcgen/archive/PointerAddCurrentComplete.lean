import duplicate_prefix.PointerAddCurrentSetup
import duplicate_prefix.PointerAddCurrentExit
import duplicate_prefix.PointerAddCurrentCleanup
import duplicate_prefix.PointerAddCurrentReturn

namespace DuplicatePrefix.PointerAddCurrentComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- From the selected language guard continuation through the normal pointer-add return. -/
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
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (cached1 : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (dead10 : (frame.locals[10]'(by omega)).value = .dead)
    (uncached10 : (frame.locals[10]'(by omega)).layout = none)
    (dead11 : (frame.locals[11]'(by omega)).value = .dead)
    (uncached11 : (frame.locals[11]'(by omega)).layout = none)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : frame.location = .mir ⟨6,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (temp3 temp4 : Immediate Provenance)
    (guardUnit : (frame.locals[3]'(by omega)).value = .live (.immediate temp3))
    (guardBool : (frame.locals[4]'(by omega)).value = .live (.immediate temp4))
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
  have valid3 : (3 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have valid4 : (4 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  let one := SourceSteps.deadFrame frame ⟨6,0⟩ 4 valid4
  let two := SourceSteps.deadFrame one ⟨6,1⟩ 3 (by simpa [one,SourceSteps.deadFrame] using valid3)
  have cleanup : SuccessfulTrace.Trace config limits
      (Storage.withCurrent (frames.push caller) frame machine) (Storage.withCurrent (frames.push caller) two machine) :=
    PointerAddCurrentCleanup.cleanup options limits remaining span (frames.push caller) frame machine
      sourceBody location valid3 valid4 temp3 temp4 guardUnit guardBool
  have sizeTwo : two.locals.size = 12 := by simp [two,one,SourceSteps.deadFrame,size]
  have intermediateDirect : ∀ slot ∈ two.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    intro slot member memory
    obtain ⟨i,inBounds,localAt⟩ := Array.mem_iff_getElem.mp member
    subst slot
    have oldBounds : i < frame.locals.size := by simpa [two,one,SourceSteps.deadFrame] using inBounds
    by_cases a : i = 3
    · simp [a,two,one,SourceSteps.deadFrame,Array.getElem_set]
    by_cases b : i = 4
    · simp [b,two,one,SourceSteps.deadFrame,Array.getElem_set]
    have localEq : two.locals[i] = frame.locals[i] := by
      simp [two,one,SourceSteps.deadFrame,Array.getElem_set,a,b,Ne.symm a,Ne.symm b]
    rw [localEq]
    exact immediateLocals _ (Array.mem_iff_getElem.mpr ⟨i,oldBounds,rfl⟩) memory
  obtain ⟨ready, setup, readyBody, readyIdentity, readyCallee, readyExtra, readyDest, readyCont, readyVa,
      readySize, readyLocation, ready0, ready10, ready11, readyDirect⟩ :=
    PointerAddCurrentSetup.setup options limits remaining span debugOff fuel
      validationFuel (frames.push caller) two machine id tag base offset count sizeTwo
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using live1)
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using cached1)
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using live2)
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using cached2)
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using dead10)
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using uncached10)
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using dead11)
      (by simpa [two,one,SourceSteps.deadFrame,Array.getElem_set] using uncached11)
      sourceBody identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow intermediateDirect
  have initial0 : frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩ := by
    have bounded : 0 < frame.locals.size := by omega
    apply Array.getElem?_eq_some_iff.mpr
    refine ⟨bounded, ?_⟩
    have v := live0
    have l := uncached0
    cases slotEq : frame.locals[0] with
    | mk value layout =>
      have valueEq : value = .live (.immediate .uninit) := by simpa only [slotEq] using v
      have layoutEq : layout = none := by simpa only [slotEq] using l
      simp only [valueEq,layoutEq]
  have slot0 : ready.locals[0]? = some ⟨.live (.immediate .uninit), none⟩ := by
    rw [ready0]
    simpa [two,one,SourceSteps.deadFrame,Array.getElem?_set] using initial0
  have state0 := (Array.getElem?_eq_some_iff.mp slot0).2
  have state10 := (Array.getElem?_eq_some_iff.mp ready10).2
  have state11 := (Array.getElem?_eq_some_iff.mp ready11).2
  obtain ⟨done, returned, machineEq, memEq, trackerEq, addressEq, tail⟩ :=
    PointerAddCurrentExit.trace_exact options limits remaining span debugOff fuel validationFuel
      frames caller ready machine id tag base offset count entry readySize
      (by rw [state0]) (by rw [state0]) (by rw [state10]) (by rw [state10])
      (by rw [state11]) (by rw [state11])
      (readyBody.trans sourceBody) (readyIdentity.trans identity) (readyCallee.trans callee)
      readyLocation (by rw [readyExtra]; exact noClocks) tracker tracked ghostFalse shallow cached present
      positive fits bounds callerId callerValid0 callerLive0 callerCached0 callerClocks
      (by rw [readyDest]; exact destination) target unwindAction (by rw [readyCont]; exact continuation)
      readyDirect (by rw [readyVa]; exact varargs) borrowFrame (by rw [readyExtra]; exact frameTracked)
      empty thread active unchecked noGc fixed
  exact ⟨done,returned,machineEq,memEq,trackerEq,addressEq, SuccessfulTrace.append cleanup (SuccessfulTrace.append setup tail)⟩

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
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (cached1 : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (dead10 : (frame.locals[10]'(by omega)).value = .dead)
    (uncached10 : (frame.locals[10]'(by omega)).layout = none)
    (dead11 : (frame.locals[11]'(by omega)).value = .dead)
    (uncached11 : (frame.locals[11]'(by omega)).layout = none)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : frame.location = .mir ⟨6,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (temp3 temp4 : Immediate Provenance)
    (guardUnit : (frame.locals[3]'(by omega)).value = .live (.immediate temp3))
    (guardBool : (frame.locals[4]'(by omega)).value = .live (.immediate temp4))
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
      id tag base offset count entry size live0 uncached0 live1 cached1 live2 cached2 dead10 uncached10 dead11 uncached11
      sourceBody identity callee location noClocks tracker tracked defaultMode ghostFalse shallow cached present
      positive fits bounds temp3 temp4 guardUnit guardBool callerId callerValid0 callerLive0 callerCached0
      callerClocks destination target unwindAction continuation immediateLocals varargs borrowFrame frameTracked
      empty thread active unchecked noGc fixed
  exact ⟨returnedMachine,memoryEq,trackerEq,addressEq,actualTrace⟩

#print axioms trace_exact
#print axioms trace
end DuplicatePrefix.PointerAddCurrentComplete

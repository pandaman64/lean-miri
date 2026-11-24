import duplicate_prefix.PointerAddCurrentStatements
import duplicate_prefix.SuccessfulTrace
import duplicate_prefix.PointerAddCurrentStorage
namespace DuplicatePrefix.PointerAddCurrentSetup
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency true
set_option backward.dsimp.instances false

private theorem written_locals (frame : CompilerFrameContext.ActualFrame)
    (slot : MIR.LocalId) (layout : LocalLayout) (valid : slot < frame.locals.size)
    (value : Immediate Provenance) :
    (ActualLocalCopy.written frame slot layout valid value).locals =
      frame.locals.set slot ⟨.live (.immediate value),some layout⟩ valid := by
  simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.set_set]

private def frameCore (frame : CompilerFrameContext.ActualFrame) : CompilerFrameContext.ActualFrame :=
  {frame with locals := #[], location := .mir ⟨0,0⟩}

private theorem coreLive (frame : CompilerFrameContext.ActualFrame) (pc : Location)
    (id : MIR.LocalId) (valid : id < frame.locals.size) :
    frameCore (SourceSteps.liveFrame frame pc id valid) = frameCore frame := rfl

private theorem coreWrite (frame : CompilerFrameContext.ActualFrame) (pc : Location)
    (id : MIR.LocalId) (layout : LocalLayout) (valid : id < frame.locals.size)
    (value : Immediate Provenance) :
    frameCore {ActualLocalCopy.written frame id layout valid value with location := .mir pc} =
      frameCore frame := rfl

private theorem assemble (before after : CompilerFrameContext.ActualFrame)
    (core : frameCore before = frameCore after)
    (locals : before.locals = after.locals)
    (whereAt : before.location = after.location) : before = after := by
  have h := congrArg (fun frame : CompilerFrameContext.ActualFrame =>
    {frame with locals := before.locals, location := before.location}) core
  rw [show {frameCore before with locals := before.locals, location := before.location} = before by cases before; rfl] at h
  rw [locals,whereAt] at h
  exact h

private def afterCopy (frame : CompilerFrameContext.ActualFrame) (raw : Scalar Provenance)
    (count : UInt64) (size : frame.locals.size = 12) : CompilerFrameContext.ActualFrame :=
  let locals := frame.locals.set 10
    ⟨.live (.immediate (.scalar raw)),some CopyCompilerFacts.destPointerLayout⟩ (by rw [size]; decide)
  let updated := locals.set 11
    ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ (by simp [locals,size])
  {frame with locals := updated, location := .mir ⟨6,6⟩}

private theorem transitions
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (size : frame.locals.size = 12)
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
    (location : frame.location = .mir ⟨6,2⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let raw := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
    let out := afterCopy frame raw count size
    ∃ f1 f2 f3 : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
        (Storage.withCurrent framesBefore f1 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f1 machine) =
        (Storage.withCurrent framesBefore f2 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f2 machine) =
        (Storage.withCurrent framesBefore f3 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f3 machine) =
        (Storage.withCurrent framesBefore out machine,.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let raw : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
  have valid3 : (10 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have valid4 : (11 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  let f1 := SourceSteps.liveFrame frame ⟨6,2⟩ 10 valid3
  have step1 := PointerAddCurrentStorage.live_pointer options limits remaining span framesBefore frame
    machine sourceBody location valid3 dead10 noClocks
  have size1 : f1.locals.size = 12 := by simp [f1,SourceSteps.liveFrame,size]
  have v11 : (1 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1]; decide
  have v13 : (10 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1]; decide
  let f2 := {(ActualLocalCopy.written f1 10 CopyCompilerFacts.destPointerLayout v13 (.scalar raw)) with location := .mir ⟨6,4⟩}
  have step2 := PointerAddCurrentStatements.copy_pointer options limits remaining span debugOff fuel validationFuel
    framesBefore f1 machine raw v11 v13
    (by simpa [f1,SourceSteps.liveFrame,Array.getElem_set,raw] using live1)
    (by simpa [f1,SourceSteps.liveFrame,Array.getElem_set] using cached1)
    (by simp [f1,SourceSteps.liveFrame])
    (by simpa [f1,SourceSteps.liveFrame] using uncached10)
    sourceBody identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow
  have size2 : f2.locals.size = 12 := by simp [f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size1]
  have v24 : (11 : Miri.MIR.LocalId) < f2.locals.size := by rw [size2]; decide
  let f3 := SourceSteps.liveFrame f2 ⟨6,4⟩ 11 v24
  have step3 := PointerAddCurrentStorage.live_count options limits remaining span framesBefore f2 machine
    sourceBody rfl v24
    (by simpa [f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,SourceSteps.liveFrame,Array.getElem_set] using dead11)
    noClocks
  have size3 : f3.locals.size = 12 := by simp [f3,SourceSteps.liveFrame,size2]
  have v32 : (2 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3]; decide
  have v34 : (11 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3]; decide
  let f4 := {(ActualLocalCopy.written f3 11 RootCompilerFacts.usizeLayout v34 (.scalar (.fromScalarInt (.ofUInt64 count)))) with location := .mir ⟨6,6⟩}
  have step4 := PointerAddCurrentStatements.copy_count options limits remaining span debugOff fuel validationFuel
    framesBefore f3 machine count v32 v34
    (by simpa [f3,SourceSteps.liveFrame,f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,Array.getElem_set] using live2)
    (by simpa [f3,SourceSteps.liveFrame,f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,Array.getElem_set] using cached2)
    (by simp [f3,SourceSteps.liveFrame])
    (by simpa [f3,SourceSteps.liveFrame,f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,Array.getElem_set] using uncached11)
    sourceBody identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow
  let pointerLocal : LocalState Provenance LocalLayout :=
    ⟨.live (.immediate (.scalar raw)),some CopyCompilerFacts.destPointerLayout⟩
  let countLocal : LocalState Provenance LocalLayout :=
    ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  have locals2 : f2.locals = frame.locals.set 10 pointerLocal valid3 := by
    change (ActualLocalCopy.written f1 10 CopyCompilerFacts.destPointerLayout v13 (.scalar raw)).locals = _
    rw [written_locals]
    exact Array.set_set _ valid3
  have locals4 : f4.locals = f2.locals.set 11 countLocal v24 := by
    change (ActualLocalCopy.written f3 11 RootCompilerFacts.usizeLayout v34 (.scalar (.fromScalarInt (.ofUInt64 count)))).locals = _
    rw [written_locals]
    exact Array.set_set _ v24
  have countValid : 11 < (frame.locals.set 10 pointerLocal valid3).size := by simp [size]
  have countUpdate := congrArg
    (fun locals : Array (LocalState Provenance LocalLayout) => locals.setIfInBounds 11 countLocal)
    locals2
  simp only [Array.setIfInBounds_def, dite_eq_left v24, dite_eq_left countValid] at countUpdate
  have core1 : frameCore f1 = frameCore frame := coreLive frame ⟨6,2⟩ 10 valid3
  have core2 : frameCore f2 = frameCore f1 :=
    coreWrite f1 ⟨6,4⟩ 10 CopyCompilerFacts.destPointerLayout v13 (.scalar raw)
  have core3 : frameCore f3 = frameCore f2 := coreLive f2 ⟨6,4⟩ 11 v24
  have core4 : frameCore f4 = frameCore f3 :=
    coreWrite f3 ⟨6,6⟩ 11 RootCompilerFacts.usizeLayout v34 (.scalar (.fromScalarInt (.ofUInt64 count)))
  have coreAfter : frameCore (afterCopy frame raw count size) = frameCore frame := rfl
  have sameCore := core4.trans (core3.trans (core2.trans (core1.trans coreAfter.symm)))
  have sameLocals : f4.locals = (afterCopy frame raw count size).locals := locals4.trans countUpdate
  have sameFrame : f4 = afterCopy frame raw count size :=
    assemble f4 (afterCopy frame raw count size) sameCore sameLocals rfl
  have sameState := congrArg
    (fun out : CompilerFrameContext.ActualFrame =>
      (Storage.withCurrent framesBefore out machine, (.ok true : Except StepError Bool)))
    sameFrame
  exact ⟨f1,f2,f3,step1,step2,step3,step4.trans sameState⟩

theorem setup
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (size : frame.locals.size = 12)
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
    (location : frame.location = .mir ⟨6,2⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (direct : ∀ slot ∈ frame.locals, ∀ opaqueMemory, slot.value ≠ .live (.indirect opaqueMemory)) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ out : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore out machine) ∧
      out.body = frame.body ∧ out.bodyIdentity = frame.bodyIdentity ∧
      out.functionInstance = frame.functionInstance ∧ out.extra = frame.extra ∧
      out.returnPlace = frame.returnPlace ∧ out.returnContinuation = frame.returnContinuation ∧
      out.vaList = frame.vaList ∧
      out.locals.size = 12 ∧ out.location = .mir ⟨6,6⟩ ∧
      out.locals[0]? = frame.locals[0]? ∧
      out.locals[10]? = some ⟨.live (.immediate (.scalar
        (Scalar.fromPointer config.access.runtime.base
         (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      out.locals[11]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
        some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ slot ∈ out.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let raw := Scalar.fromPointer cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
  let p : LocalState Provenance LocalLayout :=
    ⟨.live (.immediate (.scalar raw)),some CopyCompilerFacts.destPointerLayout⟩
  let c : LocalState Provenance LocalLayout :=
    ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  have valid10 : (10 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  let once := frame.locals.set 10 p valid10
  have valid11 : (11 : MIR.LocalId) < once.size := by simp [once,size]
  let out := afterCopy frame raw count size
  have outLocals : out.locals = once.set 11 c valid11 := rfl
  obtain ⟨f1,f2,f3,s1,s2,s3,s4⟩ :=
    transitions options limits remaining span debugOff fuel validationFuel framesBefore frame machine
      id tag base offset count size live1 cached1 live2 cached2 dead10 uncached10 dead11 uncached11
      sourceBody identity callee location noClocks tracker tracked defaultMode ghostFalse shallow
  let st (f : CompilerFrameContext.ActualFrame) := Storage.withCurrent framesBefore f machine
  have tr : SuccessfulTrace.Trace cfg limits (st frame) (st out) :=
    .next (after := st f1) s1 (.next (after := st f2) s2
      (.next (after := st f3) s3 (.next (after := st out) s4 (.refl _))))
  have untouched0 : out.locals[0]? = frame.locals[0]? := by
    rw [outLocals,Array.getElem?_set_ne valid11 (by decide : 11 ≠ 0)]
    exact Array.getElem?_set_ne valid10 (by decide : 10 ≠ 0)
  have pointerSlot : out.locals[10]? = some p := by
    rw [outLocals,Array.getElem?_set_ne valid11 (by decide : 11 ≠ 10)]
    exact Array.getElem?_set_self valid10
  have countSlot : out.locals[11]? = some c := by
    rw [outLocals]
    exact Array.getElem?_set_self valid11
  have outDirect : ∀ slot ∈ out.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    intro slot member memory
    rw [outLocals] at member
    rcases Array.mem_or_eq_of_mem_set (w := valid11) member with prior | equal
    · rcases Array.mem_or_eq_of_mem_set (w := valid10) prior with original | equal
      · exact direct slot original memory
      · rw [equal]
        simp [p]
    · rw [equal]
      simp [c]
  refine ⟨out,tr,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,untouched0,pointerSlot,countSlot,outDirect⟩
  rw [outLocals]
  simp [once,size]

#print axioms setup
end DuplicatePrefix.PointerAddCurrentSetup

import duplicate_prefix.SliceLenBody
import duplicate_prefix.LenReturn

namespace DuplicatePrefix.SliceLenExtended
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Concurrency
open PtrMetadataExecution PtrMetadataHelper PtrMetadataComplete MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Execute the retained length helper through its validated Return and the
release selected by a checked per-allocation plan. -/
theorem returnsLength
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) (carrierValid : SliceCarrier.Valid machine carrier len)
    (size : frame.locals.size = 3)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some SharedReferenceMetadata.sharedLayout)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead) (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (body : frame.body = SliceLenFacts.body.body) (identity : frame.bodyIdentity = SliceLenFacts.body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) (located : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker) (defaultMode : tracker.retagMode = .Default)
    (noRace : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) frame machine)).entries.any (·.value.ty == 2) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < (older.push caller).size+1)
    (borrowFrame : FrameState) (ownedFrame : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (release : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (index : Miri.MIR.LocalId) (callerValid : index < caller.locals.size)
    (callerLive : caller.locals[index].value = .live (.immediate .uninit))
    (callerCached : caller.locals[index].layout = some RootCompilerFacts.usizeLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace older.size caller index RootCompilerFacts.usizeLayout)
    (target : MIR.BasicBlockId) (action : MIR.UnwindAction)
    (resume : frame.returnContinuation = .goto (some target) action)
    (varargs : frame.vaList = #[]) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace config limits (Storage.withCurrent (older.push caller) frame machine)
        (Storage.withCurrent older
          {writeFrame caller index (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid with
            location := .mir ⟨target, 0⟩} finalMachine) ∧
      finalMachine.memory = finalMemory ∧
      finalMachine.borrowTracker = some { tracker with global := tracker.global.endCall borrowFrame } ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.threads.fixedScheduling = true ∧
      (config.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (config.terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.dataRace = machine.dataRace ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ currentThread, finalMachine.threads.activeThread? = some currentThread) := by
  let frames := older.push caller
  obtain ⟨second, current, done, returned, valid, trace, sameBody, sameIdentity, sameFn, extra, place,
    cont, args, localsId, localsSize, pc, resultSlot, sameArg, deadTemp⟩ :=
    SliceLenBody.before_return options limits remaining budget dispatchFuel span debug fuel validationFuel
      frames frame machine carrier len carrierValid size live0 uncached0 live1 cached1 dead2 uncached2
      body identity callee located noClocks tracker tracked defaultMode noRace backend ghost shallow dynamicFuel
      dynamicEq source cmp metadata notConstructed unchecked noGc fixed thread active cacheBound
  let restored := MetadataCallSummary.outputMachine options remaining span frames second machine valid current done thread
  have retained := MetadataOutputFacts.memory_eq options remaining span frames second machine valid current done thread
  have finalRelease : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList restored.memory finalMemory := by
    change StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList
      (MetadataCallSummary.outputMachine options remaining span frames second machine valid current done thread).memory finalMemory
    rw [retained]
    exact release
  have returned0 : 0 < returned.locals.size := by rw [localsSize]; decide
  have returned1 : 1 < returned.locals.size := by rw [localsSize]; decide
  have returned2 : 2 < returned.locals.size := by rw [localsSize]; decide
  have finalSlot : returned.locals[0] =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))), some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem returned0).symm.trans resultSlot)
  have input1 : 1 < frame.locals.size := by rw [size]; decide
  have argSlot : returned.locals[1] = frame.locals[1] :=
    Option.some.inj ((Array.getElem?_eq_getElem returned1).symm.trans (sameArg.trans (Array.getElem?_eq_getElem input1)))
  have tempDead : returned.locals[2].value = .dead := by
    rw [Array.getElem?_eq_getElem returned2] at deadTemp
    exact Option.some.inj deadTemp
  have immediate : ∀ slot ∈ returned.locals, ∀ ptr, slot.value ≠ .live (.indirect ptr) := by
    intro slot member ptr
    obtain ⟨i, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    have small : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases small with rfl | rfl | rfl
    · simp [finalSlot]
    · simp [argSlot, live1]
    · simp [tempDead]
  obtain ⟨activeThread, finalActive⟩ := MetadataOutputFacts.active_exists options remaining span frames second machine
    valid current done thread active
  have finalTracked := MetadataOutputFacts.tracked options remaining span frames second machine valid current done thread tracker tracked
  have finalGhost := (MetadataOutputFacts.ghost_eq options remaining span frames second machine valid current done thread).trans ghost
  have finalShallow := (MetadataOutputFacts.validation_eq options remaining span frames second machine valid current done thread).trans shallow
  have finalUnchecked := MetadataOutputFacts.unchecked options remaining span frames second machine valid current done thread unchecked
  have finalNoGc := MetadataOutputFacts.no_gc options remaining span frames second machine valid current done thread noGc
  have finalFixed := (MetadataOutputFacts.fixed_eq options remaining span frames second machine valid current done thread).trans fixed
  have returnStep := LenReturn.step_with_plan options limits remaining span debug fuel validationFuel older caller returned
    restored len (sameBody.trans body) pc returned0 (congrArg (·.value) finalSlot) (congrArg (·.layout) finalSlot)
    ((congrArg (·.dataRace) extra).trans noClocks) index callerValid callerLive callerCached callerClocks
    (by rw [place]; exact destination) target action (cont.trans resume) immediate (args.trans varargs)
    tracker borrowFrame finalTracked (by rw [extra]; exact ownedFrame) finalMemory finalRelease activeThread
    finalActive finalUnchecked finalNoGc finalFixed finalGhost finalShallow
  let ticked := PtrMetadataReturn.accountedMachine options remaining span restored
  let releasedMachine := ActualPopPlan.released ticked finalMemory tracker borrowFrame
  let activeIndex := activeThread.topUserRelevantFrame.getD frames.size
  let finalMachine := PtrMetadataReturn.poppedMachine older caller returned releasedMachine activeIndex
  have finalUser : finalMachine.user = ticked.user :=
    PtrMetadataReturn.popped_user older caller returned releasedMachine activeIndex
  have flags :
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl ticked.user).checkedArithmetic =
        ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl restored.user).checkedArithmetic ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl ticked.user).gcInterval =
        ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl restored.user).gcInterval := by
    unfold ticked PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl, rfl⟩
  have activeRelease : releasedMachine.threads.activeThread? = some activeThread := finalActive
  refine ⟨finalMachine, SuccessfulTrace.append trace (.next returnStep (.refl _)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold finalMachine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  · unfold finalMachine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  · rw [finalUser]
    exact (PtrMetadataReturn.accounted_ghost options remaining span restored).trans finalGhost
  · rw [finalUser]
    exact (PtrMetadataReturn.accounted_validation options remaining span restored).trans finalShallow
  · unfold finalMachine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact finalFixed
  · rw [finalUser]
    exact flags.1.trans finalUnchecked
  · rw [finalUser]
    exact flags.2.trans finalNoGc
  · have restoredRace : restored.dataRace = machine.dataRace := by
      simp only [restored, MetadataCallSummary.outputMachine, PtrMetadataReturn.poppedMachine,
        GenericPopFrame.afterRelevanceAt]
      split
      all_goals simp only [MetadataPushFacts.posted, MetadataPush.completed, MetadataPushFacts.initial,
        Storage.withCurrent, GenericPushRelevance.afterPush]
      all_goals split <;> rfl
    unfold finalMachine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact restoredRace
  · rw [finalUser]
    have preserved : ticked.user.addresses = restored.user.addresses := by
      unfold ticked PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    exact preserved.trans (MetadataOutputFacts.addresses_eq options remaining span frames second machine valid current done thread)
  · rw [finalUser]
    have preserved : ticked.user.payload.payload.user.types = restored.user.payload.payload.user.types := by
      unfold ticked PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    exact preserved.trans (MetadataOutputFacts.types_eq options remaining span frames second machine valid current done thread)
  · rw [finalUser]
    have preserved : ticked.user.payload.payload.user.backend = restored.user.payload.payload.user.backend := by
      unfold ticked PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    exact preserved.trans (MetadataOutputFacts.backend_eq options remaining span frames second machine valid current done thread)
  · rw [finalUser]
    have preserved : ticked.user.payload.payload.user.runtime.extras = restored.user.payload.payload.user.runtime.extras := by
      unfold ticked PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    exact preserved.trans (MetadataOutputFacts.extras_eq options remaining span frames second machine valid current done thread)
  · unfold finalMachine PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    split
    · exact ⟨_, MetadataOutputFacts.relevance_active frames returned releasedMachine activeThread activeRelease⟩
    · exact ⟨activeThread, activeRelease⟩

#print axioms returnsLength
end
end DuplicatePrefix.SliceLenExtended

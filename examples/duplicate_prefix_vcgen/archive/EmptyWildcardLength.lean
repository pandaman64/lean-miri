import duplicate_prefix.EmptyWildcardReference
import duplicate_prefix.EmptyWildcardRootLenCall

namespace DuplicatePrefix.EmptyWildcardLength
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.Concurrency
open CanonicalConfigFacts EmptyReferenceAllocation
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

abbrev Frame := CompilerFrameContext.ActualFrame
abbrev MachineState := MachineHooks.MachineState MiriMemoryKind Machine.RootUser

def sharedFrame (frame : Frame) (valid : 12 < frame.locals.size) (address : UInt64) :=
  CopyHelperSteps.advance
    (ActualLocalCopy.written frame 12 SharedReferenceMetadata.sharedLayout valid
      (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm) ⟨2,11⟩

/-- Execute the shared-reference assignment and retained Len call for a non-null
unresolved wildcard-provenance empty slice. Neither zero-byte retag adds a protector row. -/
theorem returns_length
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (source : PreparedContracts.SourceComparator)
    (dynamicFuel fuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = fuel+1)
    (older : Array Frame) (frame : Frame) (machine : MachineState)
    (address : UInt64) (nonNull : address ≠ 0)
    (unresolved : EmptyWildcardLocalValidator.Unresolved machine.user.addresses machine.memory address)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨2,11⟩)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (freshAgain : (allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (valid1 : 1 < frame.locals.size) (valid11 : 11 < frame.locals.size) (valid12 : 12 < frame.locals.size)
    (arg : frame.locals[1] = ⟨.live (.immediate
      (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base (Pointer.new .wildcard (Size.ofBytes address)) 0 EmptyReferenceMetadata.reference).imm), some EmptyReferenceMetadata.reference⟩)
    (dest11 : frame.locals[11] = ⟨.live (.immediate .uninit),none⟩)
    (dest12 : frame.locals[12] = ⟨.live (.immediate .uninit),none⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < older.size + 1)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 2) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let afterReference := sharedFrame frame valid12 address
    let afterLength := LenCallResultFrame.resultFrame afterReference
      (by simpa [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using valid11) 0
    ∃ after,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent older frame machine) (Storage.withCurrent older afterLength after) ∧
      after.memory = machine.memory ∧ after.borrowTracker = some (allocatedTracker (allocatedTracker tracker fresh) freshAgain) ∧
      after.user.payload.ghost = false ∧ after.user.payload.validation = .Shallow ∧
      after.dataRace = none ∧ after.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).gcInterval = 0 ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      ∃ threadAfter, after.threads.activeThread? = some threadAfter := by
  let afterReference := sharedFrame frame valid12 address
  let retagged := allocatedMachine machine tracker fresh
  have preserved11 : 11 < afterReference.locals.size := by
    simpa [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using valid11
  have retained12 : 12 < afterReference.locals.size := by
    simpa [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using valid12
  have referenceStep :
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent older frame machine) = (Storage.withCurrent older afterReference retagged,.ok true) := by
    have step := EmptyWildcardReference.zero_statement options limits remaining span preciseOff implicitOff debug
      cmp dynamicFuel fuel dynamicEq validationFuel address nonNull older frame machine unresolved body identity callee located
      tracker tracked mode fresh valid1 valid12 (by
        rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span]
        exact congrArg LocalState.value arg) (congrArg LocalState.layout arg)
      (congrArg LocalState.value dest12) (congrArg LocalState.layout dest12) noClocks ghost shallow metadata notConstructed
    simpa [afterReference, sharedFrame, CanonicalConfigFacts.actual_access_runtime, PtrMetadataComplete.rawImmediate,
      RetagReferencePlace.sliceValue, EmptyReferenceFacts.destination, EmptyReferenceFacts.location, EmptyReferenceInfo.layout, retagged] using step
  have slot11 : afterReference.locals[11] = frame.locals[11] := by
    simp [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout,
      Array.getElem_set]
  obtain ⟨ctx⟩ := EmptyReferenceContext.exists_context options remaining span preciseOff implicitOff
  obtain ⟨after, trace, memory, ledger, gh, sh, raceOff, fix, un, gc, addr, ty, be, ex, thread⟩ :=
    EmptyWildcardRootLenCall.returns_zero options limits remaining budget dispatchFuel span ctx debug cmp dynamicFuel fuel
      dynamicEq validationFuel address nonNull older afterReference retagged unresolved (allocatedTracker tracker fresh)
      rfl mode freshAgain preserved11 ((congrArg LocalState.value slot11).trans (congrArg LocalState.value dest11))
      ((congrArg LocalState.layout slot11).trans (congrArg LocalState.layout dest11)) noClocks ghost shallow race
      thread active cacheBound metadata notConstructed body identity callee rfl source retained12
      (by simp [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout])
      (by simp [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout])
      backend unchecked noGc fixed
  exact ⟨after, .next referenceStep trace, memory, ledger, gh, sh, raceOff, fix, un, gc, addr, ty, be, ex, thread⟩

#print axioms returns_length
end
end DuplicatePrefix.EmptyWildcardLength

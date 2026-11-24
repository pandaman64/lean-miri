import duplicate_prefix.RootSharedRef
import duplicate_prefix.HelperAbiLayouts
import duplicate_prefix.CurrentReferenceLocalWrite
import duplicate_prefix.CurrentSlicePlace
import duplicate_prefix.CompilerFrameLayout
import duplicate_prefix.ActualLocalPlace
import duplicate_prefix.SourceSteps

namespace DuplicatePrefix.RootSharedStep
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

abbrev sharedLayout : LocalLayout := HelperAbiLayouts.sharedSliceLayout

theorem sharedLookup : PreparedReflection.actual.runtime.lookup 7 = .ok sharedLayout :=
  HelperAbiLayouts.shared_slice_layout_eq

private theorem destinationType (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 12 = .ok 7 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

noncomputable def cacheDestination (frame : CompilerFrameContext.ActualFrame) (valid : 12 < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 12 sharedLayout valid

/-- Compose the typed local/dereference steps and physical write of the
emitted shared expression. Validation's result is the single remaining
effect premise, so a caller can supply its independently proved reborrow. -/
theorem stepOfValidation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (debug : options.place.debugAssertions = false)
    (older : Array CompilerFrameContext.ActualFrame) (frame afterFrame : CompilerFrameContext.ActualFrame)
    (machine after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (length : UInt64) (capacity : 12 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨2,11⟩)
    (locatedAfter : afterFrame.location = .mir ⟨2,11⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (destLive : frame.locals[12].value = .live (.immediate .uninit))
    (destUncached : frame.locals[12].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (old new : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some old)
    (trackedAfter : after.borrowTracker = some new)
    (mode : old.retagMode = .Default) (modeAfter : new.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let metadata : Miri.Memory.Scalar Provenance := .fromScalarInt (.ofUInt64 length)
    let input : Immediate Provenance := .scalarPair (.fromPointer config.access.runtime.base pointer) metadata
    let cached := cacheDestination frame capacity
    let stored := CurrentReferenceLocalWrite.written cached 12 input
      (by simpa [cached, cacheDestination, LocalPlaces.cachePlaceLayout] using capacity)
    (frame.locals[1]'(by omega)).value = .live (.immediate input) →
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity () (fuel+1)
      (LocalPlaces.localRuntimePlace older.size stored 12 sharedLayout) true
      (Storage.withCurrent older stored machine) = .ok () (Storage.withCurrent older afterFrame after) →
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {afterFrame with location := .mir ⟨2,12⟩}
        after, .ok true) := by
  intro config metadata input cached stored sourceLive validated
  let hooks := ExecutionMachine.rvalueHooks config limits
  let source : MPlaceTy Provenance :=
    ⟨⟨pointer.withOptionalProvenance, .metadata metadata, none⟩, CurrentSlicePlace.actualSliceLayout⟩
  let destination := LocalPlaces.localRuntimePlace older.size cached 12 sharedLayout
  let before := Storage.withCurrent older frame machine
  let prepared := Storage.withCurrent older cached machine
  let entered := Storage.withCurrent older cached machine
  have sized : sharedLayout.layout.isSized = true := by decide +kernel
  have destinationLayout := PointerAddFacts.compute_local older frame machine 12 7 sharedLayout
    (destinationType frame body identity callee) sharedLookup
  have cachedPlace := ActualLocalPlace.uncached options limits (remaining+1) span debug
    older frame machine 12 sharedLayout capacity destUncached sized destinationLayout
  have validSource : 1 < cached.locals.size := by
    simp [cached,cacheDestination,LocalPlaces.cachePlaceLayout]
    omega
  have sourceStill : cached.locals[1].layout = some RootCompilerFacts.sliceLayout := by
    simpa [cached,cacheDestination,LocalPlaces.cachePlaceLayout,Array.getElem_set] using sourceCached
  have sourceValue : cached.locals[1].value = .live (.immediate input) := by
    simpa [cached,cacheDestination,LocalPlaces.cachePlaceLayout,Array.getElem_set] using sourceLive
  have sourcePlace := CurrentSlicePlace.rootSlicePlace options limits (remaining+1) span debug
    older cached machine pointer length validSource sourceStill noClocks ghost sourceValue
  have typedReference : source.mplace.toRef config.access.runtime.base = .ok input := by
    cases pointer
    rfl
  have enabling : hooks.enforceValidity () destination.layout entered = .ok true entered := by
    change config.compiler.enforceValidity () destination.layout entered = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).compilerEnforce]
    simp [ValidityMachine.enforceValidity, entered, Storage.withCurrent, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have destValid : 12 < cached.locals.size := by
    simpa [cached,cacheDestination,LocalPlaces.cachePlaceLayout] using capacity
  have destStillLive : cached.locals[12].value = .live (.immediate .uninit) := by
    simpa [cached,cacheDestination,LocalPlaces.cachePlaceLayout,Array.getElem_set] using destLive
  have destStillCached : cached.locals[12].layout = some sharedLayout := by
    simp [cached,cacheDestination,LocalPlaces.cachePlaceLayout]
  have wrote := CurrentReferenceLocalWrite.of_validation options limits remaining span debug fuel budget
    older cached machine 12 .uninit input sharedLayout
    destValid destStillLive destStillCached sized noClocks ghost shallow
    (Storage.withCurrent older afterFrame after) validated
  exact RootSharedRef.statement config limits () older frame afterFrame machine after
    prepared prepared destination source input body located locatedAfter cachedPlace sourcePlace
    typedReference old new tracked mode trackedAfter modeAfter enabling wrote

#print axioms stepOfValidation
end DuplicatePrefix.RootSharedStep

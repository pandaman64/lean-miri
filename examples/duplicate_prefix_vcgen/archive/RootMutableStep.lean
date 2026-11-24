import RootMutableReborrow
import duplicate_prefix.CurrentReferenceLocalWrite
import duplicate_prefix.CurrentSlicePlace
import duplicate_prefix.CompilerFrameLayout
import duplicate_prefix.ActualLocalPlace
import duplicate_prefix.SourceSteps

namespace DuplicatePrefix.RootMutableStep
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private theorem destinationType (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 16 = .ok 1 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

def cacheDestination (frame : CompilerFrameContext.ActualFrame) (valid : 16 < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 16 RootCompilerFacts.sliceLayout valid

def scopeMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (borrow : MachineHooks.BorrowState) :=
  {machine with borrowTracker := some {borrow with retagMode := .TwoPhase}}

def restoreMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (before after : MachineHooks.BorrowState) :=
  {machine with borrowTracker := some {after with retagMode := before.retagMode}}

/-- Compose the typed local/dereference steps and physical write of the
emitted mutable expression. Validation's result is the single remaining
effect premise, so a caller can supply its independently proved reborrow. -/
theorem stepOfValidation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (debug : options.place.debugAssertions = false)
    (older : Array CompilerFrameContext.ActualFrame) (frame afterFrame : CompilerFrameContext.ActualFrame)
    (machine after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (length : UInt64) (capacity : 16 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨6,7⟩)
    (locatedAfter : afterFrame.location = .mir ⟨6,7⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (destLive : frame.locals[16].value = .live (.immediate .uninit))
    (destUncached : frame.locals[16].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (old new : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some old)
    (trackedAfter : after.borrowTracker = some new)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let metadata : Miri.Memory.Scalar Provenance := .fromScalarInt (.ofUInt64 length)
    let input : Immediate Provenance := .scalarPair (.fromPointer config.access.runtime.base pointer) metadata
    let cached := cacheDestination frame capacity
    let stored := CurrentReferenceLocalWrite.written cached 16 input
      (by simpa [cached, cacheDestination, LocalPlaces.cachePlaceLayout] using capacity)
    (frame.locals[1]'(by omega)).value = .live (.immediate input) →
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity () (fuel+1)
      (LocalPlaces.localRuntimePlace older.size stored 16 RootCompilerFacts.sliceLayout) true
      (Storage.withCurrent older stored (scopeMachine machine old)) = .ok () (Storage.withCurrent older afterFrame after) →
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {afterFrame with location := .mir ⟨6,8⟩}
        (restoreMachine after old new), .ok true) := by
  intro config metadata input cached stored sourceLive validated
  let hooks := ExecutionMachine.rvalueHooks config limits
  let source : MPlaceTy Provenance :=
    ⟨⟨pointer.withOptionalProvenance, .metadata metadata, none⟩, CurrentSlicePlace.actualSliceLayout⟩
  let destination := LocalPlaces.localRuntimePlace older.size cached 16 RootCompilerFacts.sliceLayout
  let before := Storage.withCurrent older frame machine
  let prepared := Storage.withCurrent older cached machine
  let entered := Storage.withCurrent older cached (scopeMachine machine old)
  have sized : RootCompilerFacts.sliceLayout.layout.isSized = true := by decide +kernel
  have destinationLayout := PointerAddFacts.compute_local older frame machine 16 1 RootCompilerFacts.sliceLayout
    (destinationType frame body identity callee) (by with_unfolding_all exact RootCompilerFacts.slice_layout_eq)
  have cachedPlace := ActualLocalPlace.uncached options limits (remaining+1) span debug
    older frame machine 16 RootCompilerFacts.sliceLayout capacity destUncached sized destinationLayout
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
    simp [ValidityMachine.enforceValidity, entered, Storage.withCurrent, scopeMachine, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have reduced := RootMutableReborrow.writeReference config limits () before prepared prepared destination source
    input cachedPlace sourcePlace typedReference old tracked enabling
  have destValid : 16 < cached.locals.size := by
    simpa [cached,cacheDestination,LocalPlaces.cachePlaceLayout] using capacity
  have destStillLive : cached.locals[16].value = .live (.immediate .uninit) := by
    simpa [cached,cacheDestination,LocalPlaces.cachePlaceLayout,Array.getElem_set] using destLive
  have destStillCached : cached.locals[16].layout = some RootCompilerFacts.sliceLayout := by
    simp [cached,cacheDestination,LocalPlaces.cachePlaceLayout]
  have wrote := CurrentReferenceLocalWrite.of_validation options limits remaining span debug fuel budget
    older cached (scopeMachine machine old) 16 .uninit input RootCompilerFacts.sliceLayout
    destValid destStillLive destStillCached sized noClocks ghost shallow
    (Storage.withCurrent older afterFrame after) validated
  let rvalue : Rvalue := .Ref .Erased (.Mut .TwoPhaseBorrow) ⟨1,#[.Deref]⟩
  have effect : evalRvalueIntoPlace hooks () rvalue ⟨16,#[]⟩ before =
      .ok () (Storage.withCurrent older afterFrame (restoreMachine after old new)) := by
    change evalRvalueIntoPlace hooks () rvalue ⟨16,#[]⟩ before = _ at reduced
    rw [reduced]
    unfold MachineHooks.withRetagMode
    simp only [prepared, Storage.withCurrent, tracked]
    change hooks.writeImmediate () input destination entered = _ at wrote
    simp only [entered, Storage.withCurrent,scopeMachine] at wrote
    rw [wrote]
    simp [trackedAfter, restoreMachine]
  have blockBound : 6 < RootBody.reflected.body.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := RootBody.reflected.body.body.basicBlocks[6]'blockBound
  have assignBound : 7 < block.statements.size := by
    with_unfolding_all change 7 < 8
    decide
  let stmt := block.statements[7]'assignBound
  apply SourceSteps.assign_exact config limits () older frame afterFrame machine (restoreMachine after old new)
    ⟨6,7⟩ block stmt ⟨16,#[]⟩ rvalue located
  · simp [body, block, blockBound]
  · simp [stmt, assignBound]
  · with_unfolding_all rfl
  · exact effect
  · exact locatedAfter

end DuplicatePrefix.RootMutableStep

#print axioms DuplicatePrefix.RootMutableStep.stepOfValidation

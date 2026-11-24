import RootMutableReborrow
import duplicate_prefix.ActualCurrentSlice
import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.RootMetadataQueries
import duplicate_prefix.LocalPlaces
import duplicate_prefix.RootLocalStages
import duplicate_prefix.Storage

namespace DuplicatePrefix.CurrentSlicePlace
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem sourceLocalCached
    (compiler : CompilerProviders.Prepared)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    PlaceMachine.localToOpCore (EvalPlaceConstruction.localLayout compiler) ValidityMachine.validationInProgress localId
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate value,layout⟩ (Storage.withCurrent frames frame machine) := by
  simp [PlaceMachine.localToOpCore,EvalPlaceConstruction.localLayout,MachineHooks.currentFrame,
    MachineHooks.afterLocalRead,ValidityMachine.validationInProgress,Storage.withCurrent,Stack.currentFrame?,
    Frame.getLocal,Frame.getLocalOperand,LocalState.access,valid,live,cached,sized,noClocks,ghost,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    Except.mapError,Except.bind,Except.pure]

theorem constructor_skip_cached_local
    (compiler : CompilerProviders.Prepared) (po : EvalPlaceConstruction.Options)
    (access : ValidityMachine.Access MiriMemoryKind RootStored) (pointers : RootPointers) (table : RootRawVTable)
    (check : Unit → MIR.Place → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
    (validate : Unit → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
    (debugOff : po.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    (EvalPlaceConstruction.compiler compiler po access pointers table check validate).deref ()
      (LocalPlaces.localRuntimePlace frames.size frame localId layout) true
      (Storage.withCurrent frames frame machine) =
      (do
        let immediate ← ValidityMachine.readImmediate access ⟨.immediate value,layout⟩
        let memory ← PointerPlaceMachine.fromImmediate access
          (CompilerExecutionProviders.pointerCompiler compiler.lifecycle.calls.symbols.facts) () immediate
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  have read := sourceLocalCached compiler frames frame machine localId value layout valid live cached sized noClocks ghost
  dsimp only [Storage.withCurrent] at read
  unfold EvalPlaceConstruction.compiler
  dsimp only
  unfold placeToOpCore
  simp [LocalPlaces.localRuntimePlace,debugOff,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,read,
    Except.mapError,Except.bind,Except.pure]
  try (rw [read];rfl)

theorem actual_skip_cached_local
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    config.projection.place.deref () (LocalPlaces.localRuntimePlace frames.size frame localId layout) true
      (Storage.withCurrent frames frame machine) =
      (do
        let immediate ← ValidityMachine.readImmediate config.access ⟨.immediate value,layout⟩
        let memory ← PointerPlaceMachine.fromImmediate config.access
          (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts) () immediate
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨po,pointers,table,compilerEq,projectionEq,operandEq⟩ := fields.placeConstruction
  have poDebug : po.debugAssertions = false := by
    have debug := fields.debug.trans debugOff
    rw [compilerEq] at debug
    exact debug
  have staged := constructor_skip_cached_local PreparedReflection.actual.compiler po config.access pointers table
    config.compiler.checkPlaceType config.compiler.validate poDebug frames frame machine localId value layout
    valid live cached sized noClocks ghost
  change config.projection.place.deref () _ true _ = _
  rw [projectionEq]
  change config.compiler.deref () _ true _ = _
  rw [compilerEq]
  exact staged

theorem eval_one_deref
    (projection : PlaceProjectionHooks Provenance RootState Unit MachineHooks.FrameExtra)
    (localId : Miri.MIR.LocalId) (localPlace : RuntimePlace Provenance) (state : RootState)
    (read : localToPlace projection.place () localId state = .ok localPlace state) :
    PlaceDynamic.evalPlace projection () ⟨localId,#[.Deref]⟩ true state =
      projection.place.deref () localPlace true state := by
  simp [PlaceDynamic.evalPlace,read,bind,EStateM.bind]

theorem actual_eval_skip_cached_local
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    (ExecutionMachine.rvalueHooks config limits).evalPlace () ⟨localId,#[.Deref]⟩ true
      (Storage.withCurrent frames frame machine) =
      (do
        let immediate ← ValidityMachine.readImmediate config.access ⟨.immediate value,layout⟩
        let memory ← PointerPlaceMachine.fromImmediate config.access
          (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts) () immediate
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : projection.place.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = _
    rw [fields.projectionGetFrame]
    exact Storage.current_frame frames frame machine
  have index : projection.place.frameIndex state = .ok frames.size state := by
    change config.projection.place.frameIndex state = _
    rw [fields.projectionFrameIndex]
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind]
  have localRead := LocalPlaces.localToPlace_cached projection.place () frame localId frames.size layout state
    valid getFrame index cached sized
  have evaluated := eval_one_deref projection localId (LocalPlaces.localRuntimePlace frames.size frame localId layout) state localRead
  change PlaceDynamic.evalPlace projection () ⟨localId,#[.Deref]⟩ true state = _
  rw [evaluated]
  exact actual_skip_cached_local options remaining span debugOff frames frame machine localId value layout valid live cached sized noClocks ghost


abbrev actualSliceLayout : LocalLayout := ActualCurrentSlice.layout

theorem actualSlicePointee (before : RootState) :
    (CompilerExecutionProviders.pointerCompiler
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts).builtinDeref
      () RootCompilerFacts.sliceLayout.ty before = .ok (some actualSliceLayout.ty) before := by
  with_unfolding_all rfl

theorem actualSlicePlaceLayout (before : RootState) :
    (CompilerExecutionProviders.pointerCompiler
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts).layoutOf
      () actualSliceLayout.ty before = .ok actualSliceLayout before := by
  rw [ActualCurrentSlice.ty]
  unfold CompilerExecutionProviders.pointerCompiler
  dsimp only
  rw [ActualCurrentSlice.compilerLayout]
  rfl

theorem scopedReadPair
    (access : ValidityMachine.Access MiriMemoryKind RootStored)
    (before : RootState) (layout : LocalLayout) (a b : Miri.Memory.Scalar Provenance)
    (readable : isPrimitiveReadable layout.layout.backendRepr = true)
    (retain : access.retainTouched before.machine none = before.machine) :
    ValidityMachine.readImmediate access ⟨.immediate (.scalarPair a b),layout⟩ before =
      .ok ⟨.scalarPair a b,layout⟩ before := by
  simp only [ValidityMachine.readImmediate, ValidityMachine.scopedAccess,
    ValidityMachine.validationInProgress, PlaceMachine.readImmediate, Miri.Interpreter.readImmediate,
    localMemoryLayout, readable, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  conv => lhs; cbv
  cbv at retain
  rw [retain]

/-- The source object for the root's reborrow is the live fat-pointer local.
This stage computes the actual projected slice place without changing the
allocator, tags, pointer address, or machine state. -/
theorem rootSlicePlace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (length : UInt64) (valid : 1 < frame.locals.size)
    (cached : frame.locals[1].layout = some RootCompilerFacts.sliceLayout)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let metadata : Miri.Memory.Scalar Provenance := .fromScalarInt (.ofUInt64 length)
    let value : Immediate Provenance := .scalarPair (.fromPointer cfg.access.runtime.base pointer) metadata
    let state := Storage.withCurrent older frame machine
    frame.locals[1].value = .live (.immediate value) →
    (ExecutionMachine.rvalueHooks cfg limits).evalPlace () ⟨1,#[.Deref]⟩ true state =
      .ok ⟨.memory ⟨pointer.withOptionalProvenance,.metadata metadata,none⟩, actualSliceLayout⟩ state := by
  intro cfg metadata value state live
  have sized : RootCompilerFacts.sliceLayout.layout.isSized = true := by decide +kernel
  have readable : isPrimitiveReadable RootCompilerFacts.sliceLayout.layout.backendRepr = true := by decide +kernel
  have retain : cfg.access.retainTouched machine none = machine := by
    rw [CanonicalConfigFacts.actual_retain_touched options () remaining span]
  have localRead := actual_eval_skip_cached_local options limits remaining span debug older frame machine
    1 value RootCompilerFacts.sliceLayout valid live cached sized noClocks ghost
  rw [localRead]
  have read := scopedReadPair cfg.access state RootCompilerFacts.sliceLayout
    (.fromPointer cfg.access.runtime.base pointer) metadata readable retain
  have placed := RootMutableReborrow.fromFatReference cfg.access
    (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts)
    () RootCompilerFacts.sliceLayout actualSliceLayout pointer length state
    (actualSlicePointee state) (actualSlicePlaceLayout state) ActualCurrentSlice.align
  simp only [bind, Bind.bind, EStateM.bind, value]
  erw [read]
  simp only [pure, Pure.pure, EStateM.pure]
  change PointerPlaceMachine.fromImmediate (PreparedContracts.actualConfig options () remaining span).access
    (CompilerExecutionProviders.pointerCompiler PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts)
    () ⟨.scalarPair (.fromPointer cfg.access.runtime.base pointer) metadata,RootCompilerFacts.sliceLayout⟩
    state = _ at placed
  erw [placed]

end
end DuplicatePrefix.CurrentSlicePlace

#print axioms DuplicatePrefix.CurrentSlicePlace.actual_eval_skip_cached_local

#print axioms DuplicatePrefix.CurrentSlicePlace.rootSlicePlace

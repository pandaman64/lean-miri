import Miri.Interpreter.ConstantMachine
import Miri.Interpreter.ExecutionMachine
open Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter

namespace DuplicatePrefix.ZeroBoolean
variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

def setTrue (frame : Frame) (bound : 0 < frame.locals.size) : Frame :=
  let slot : LocalState Provenance LocalLayout :=
    { value := .live (.immediate (.scalar (.fromBool true))), layout := frame.locals[0].layout }
  { frame with locals := frame.locals.set 0 slot bound }

theorem writeTrueLocal (compiler : PlaceMachine.CompilerHooks K U C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (sized : layout.layout.isSized = true)
    (bound : 0 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[0].value = .live (.immediate old))
    (noClocks : frame.extra.dataRace = none) (checking : Bool)
    (mode : ∀ stack, compiler.validationInProgress ⟨stack, machine⟩ = .ok checking ⟨stack, machine⟩)
    (debug : compiler.debugAbiCheck (.scalar (.fromBool true)) layout = pure ()) :
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      compiler.validationInProgress MachineHooks.afterLocalWrite compiler.debugAbiCheck
      0 layout (.scalar (.fromBool true)) (⟨⟨older.push frame⟩, machine⟩ : State) =
      .ok () ⟨⟨older.push (setTrue frame bound)⟩, machine⟩ := by
  have operand : frame.getLocalOperand 0 = .ok (.immediate old) := by
    simp [Frame.getLocalOperand, Frame.getLocal, bound, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, LocalState.access, live, Except.mapError]
  have updated : frame.setLocalOperand 0 (.immediate (.scalar (.fromBool true))) =
      .ok (setTrue frame bound) := by
    simp [Frame.setLocalOperand, operand, Frame.replaceLocalValue, bound,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, setTrue]
  cases checking <;>
    simp [placeWriteLocalImmediate, MachineHooks.currentFrame, Stack.currentFrame?,
      MachineHooks.setCurrentFrame, MachineHooks.afterLocalWrite, setTrue, sized, operand, updated,
      mode, debug, noClocks, bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      set, MonadStateOf.set, EStateM.set, Pure.pure, EStateM.pure, pure] <;> rfl

/-- The MIR boolean literal reduces to the canonical initialized scalar
when the compiler has provided its target local layout. -/
theorem evalTrue (runtime : RuntimeMetadata)
    (functions : FunctionPointers.Hooks K U O) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError) (span : SpanRef) (layout : LocalLayout)
    (before : State) :
    ConstantMachine.evalOperandWithLayout runtime functions arithmetic externStatic classify
      ⟨span, none, .Val (.Scalar (.Int 1 1)) 0⟩ (some layout) none before =
      .ok ⟨.immediate (.scalar (.fromBool true)), layout⟩ before := by
  cases before with
  | mk stack machine => with_unfolding_all rfl

def atFrame (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U) : State :=
  ⟨⟨older.push frame⟩, machine⟩

private def frameIndex : MachineHooks.M K U Nat := do
  match (← get).stack.frameIndex with
  | .ok index => pure index
  | .error error => throw (.stack error)

theorem readTrueRaw (access : PlaceMachine.AccessConfig K U)
    (stable : ∀ machine, access.retainTouched machine none = machine)
    (layout : LocalLayout) (before : State) :
    PlaceMachine.readRaw access ⟨.immediate (.scalar (.fromBool true)), layout⟩ before =
      .ok (.immediate ⟨.scalar (.fromBool true), localMemoryLayout layout⟩) before := by
  cases before
  simp [PlaceMachine.readRaw, readImmediateRaw, PlaceMachine.commit, PlaceMachine.finish,
    stable, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Id.run, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] <;> rfl

theorem copyTrueLocal (access : PlaceMachine.AccessConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C)
    (place : PlaceHooks Provenance State C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance State C) (choice : C) (transmute : Bool)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (sized : layout.layout.isSized = true)
    (bound : 0 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[0].value = .live (.immediate old))
    (noClocks : frame.extra.dataRace = none) (checking : Bool)
    (mode : ∀ stack, compiler.validationInProgress ⟨stack, machine⟩ = .ok checking ⟨stack, machine⟩)
    (debug : compiler.debugAbiCheck (.scalar (.fromBool true)) layout = pure ())
    (getFrame : place.getFrame = MachineHooks.currentFrame)
    (currentIndex : place.frameIndex = frameIndex)
    (debugOff : place.debugAssertions = false)
    (writer : place.writeLocalImmediate choice =
      placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
        compiler.validationInProgress MachineHooks.afterLocalWrite compiler.debugAbiCheck)
    (stable : ∀ machine, access.retainTouched machine none = machine)
    (compatible : copy.compatible layout layout = .ok true)
    (padding : copy.hasPadding layout = .ok false)
    (reader : copy.readRaw choice = PlaceMachine.readRaw access)
    (validationOff : ∀ stack, place.enforceValidity choice layout ⟨stack, machine⟩ = .ok false ⟨stack, machine⟩) :
    copyRuntimePlace place copy choice ⟨.immediate (.scalar (.fromBool true)), layout⟩
      ⟨.local older.size 0 none frame.localsIdentity, layout⟩ transmute (atFrame older frame machine) =
      .ok () (atFrame older (setTrue frame bound) machine) := by
  have operand : frame.getLocalOperand 0 = .ok (.immediate old) := by
    simp [Frame.getLocalOperand, Frame.getLocal, bound, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure, LocalState.access, live, Except.mapError]
  have wrote := writeTrueLocal compiler older frame machine layout sized bound old live noClocks checking mode debug
  have read := readTrueRaw access stable layout (atFrame older frame machine)
  simp [copyRuntimePlace, copyRuntimePlaceNoValidate, writePlaceImmediateNoValidate,
    asMplaceOrMutableLocal, requireCurrent_eq, checkLocalIdentity_debugOff place _ debugOff,
    getFrame, currentIndex, debugOff, writer, compatible, padding, reader, validationOff, sized,
    frameIndex, atFrame, Stack.frameIndex, Stack.currentFrame?, MachineHooks.currentFrame,
    operand, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get] at read ⊢
  rw [read]
  simp [EStateM.bind, EStateM.get, EStateM.pure, Stack.currentFrame?, operand, bind, Bind.bind, Except.pure, Except.bind]
  simp only [Pure.pure, EStateM.pure]
  simp only [MachineHooks.currentFrame, get, getThe, MonadStateOf.get, bind, Bind.bind, pure, Pure.pure,
    atFrame, Stack.currentFrame?] at wrote
  rw [wrote]
  simp [validationOff, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

def cacheBool (frame : Frame) (layout : LocalLayout) (bound : 0 < frame.locals.size) : Frame :=
  let slot := { frame.locals[0] with layout := some layout }
  { frame with locals := frame.locals.set 0 slot bound }

theorem evalUncachedDest (projection : PlaceProjectionHooks Provenance State C MachineHooks.FrameExtra)
    (choice : C) (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (sized : layout.layout.isSized = true)
    (bound : 0 < frame.locals.size) (uncached : frame.locals[0].layout = none)
    (getFrame : projection.place.getFrame = MachineHooks.currentFrame)
    (setFrame : projection.place.setFrame = MachineHooks.setCurrentFrame)
    (currentIndex : projection.place.frameIndex = frameIndex)
    (resolve : projection.place.resolveLayout choice 0 (atFrame older frame machine) =
      .ok layout (atFrame older frame machine))
    (check : ∀ destination, projection.place.checkPlaceType choice ⟨0, #[]⟩ destination = pure ()) :
    PlaceDynamic.evalPlace projection choice ⟨0, #[]⟩ true (atFrame older frame machine) =
      .ok ⟨.local older.size 0 none frame.localsIdentity, layout⟩
        (atFrame older (cacheBool frame layout bound) machine) := by
  have slot : frame.getLocal 0 = .ok frame.locals[0] := by
    simp [Frame.getLocal, bound] <;> rfl
  have cached : frame.getOrCacheLocalLayout 0 layout = .ok (cacheBool frame layout bound, layout) := by
    simp [Frame.getOrCacheLocalLayout, slot, uncached, cacheBool, Frame.getLocal, bound,
      bind, Bind.bind, Except.bind, Except.pure, pure, Pure.pure] <;> rfl
  simp only [atFrame] at resolve
  simp [PlaceDynamic.evalPlace, localToPlace, placeLayoutOfLocal, sized, getFrame, setFrame,
    currentIndex, resolve, check, frameIndex, atFrame, Stack.currentFrame?, Stack.frameIndex,
    MachineHooks.currentFrame, MachineHooks.setCurrentFrame, slot, uncached, cached, cacheBool,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure, set, MonadStateOf.set, EStateM.set, Except.pure, Except.bind] <;> rfl

abbrev profilePlace (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) :=
  (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place

/-- Source dictionary equations for the Boolean local under the validation-off
profile. The metadata queries resolve the declared Boolean type and layout. -/
structure BooleanLocalProfile (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (choice : C) (layout : LocalLayout)
    (machine : MachineHooks.MachineState K U) where
  sized : layout.layout.isSized = true
  getFrame : (profilePlace config limits).getFrame = MachineHooks.currentFrame
  setFrame : (profilePlace config limits).setFrame = MachineHooks.setCurrentFrame
  currentIndex : (profilePlace config limits).frameIndex = frameIndex
  debugOff : (profilePlace config limits).debugAssertions = false
  check : ∀ destination, (profilePlace config limits).checkPlaceType choice ⟨0, #[]⟩ destination = pure ()
  checking : Bool
  mode : ∀ stack, (ExecutionMachine.withValidation config limits).compiler.validationInProgress ⟨stack, machine⟩ =
    .ok checking ⟨stack, machine⟩
  debug : (ExecutionMachine.withValidation config limits).compiler.debugAbiCheck (.scalar (.fromBool true)) layout = pure ()
  writer : (profilePlace config limits).writeLocalImmediate choice =
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      (ExecutionMachine.withValidation config limits).compiler.validationInProgress MachineHooks.afterLocalWrite
      (ExecutionMachine.withValidation config limits).compiler.debugAbiCheck
  stable : ∀ machine, config.access.retainTouched machine none = machine
  compatible : (ExecutionMachine.withValidation config limits).copy.compatible layout layout = .ok true
  padding : (ExecutionMachine.withValidation config limits).copy.hasPadding layout = .ok false
  validationOff : ∀ stack, (profilePlace config limits).enforceValidity choice layout ⟨stack, machine⟩ =
    .ok false ⟨stack, machine⟩

/-- Execute the canonical zero-branch rvalue assignment through layout caching,
literal evaluation, immediate copy, and the Default Tree Borrows mode scope. -/
theorem evalAssignTrue (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (choice : C) (span : SpanRef) (layout : LocalLayout)
    (runtime : RuntimeMetadata)
    (externStatic : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError)
    (constant : config.operands.constant choice ⟨span, none, .Val (.Scalar (.Int 1 1)) 0⟩ (some layout) =
      ConstantMachine.evalOperandWithLayout runtime config.functions config.arithmetic externStatic classify
        ⟨span, none, .Val (.Scalar (.Int 1 1)) 0⟩ (some layout) none)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (profile : BooleanLocalProfile config limits choice layout machine)
    (resolve : (profilePlace config limits).resolveLayout choice 0 (atFrame older frame machine) =
      .ok layout (atFrame older frame machine))
    (bound : 0 < frame.locals.size) (uncached : frame.locals[0].layout = none)
    (old : Immediate Provenance) (live : frame.locals[0].value = .live (.immediate old))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default) :
    let cached := cacheBool frame layout bound
    let sizedCache : 0 < cached.locals.size := by simpa [cached, cacheBool] using bound
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) choice
      (.Use (.Constant ⟨span, none, .Val (.Scalar (.Int 1 1)) 0⟩) .Yes)
      ⟨0, #[]⟩ (atFrame older frame machine) =
      .ok () (atFrame older (setTrue cached sizedCache) machine) := by
  let cached := cacheBool frame layout bound
  have sizedCache : 0 < cached.locals.size := by simpa [cached, cacheBool] using bound
  let dest : RuntimePlace Provenance := ⟨.local older.size 0 none frame.localsIdentity, layout⟩
  let copiedValue : OpTy Provenance := ⟨.immediate (.scalar (.fromBool true)), layout⟩
  let hooks := ExecutionMachine.rvalueHooks config limits
  let input := atFrame older frame machine
  let ready := atFrame older cached machine
  let final := atFrame older (setTrue cached sizedCache) machine
  have evaluate : hooks.evalPlace choice ⟨0, #[]⟩ true input = .ok dest ready :=
    evalUncachedDest _ _ _ _ _ _ profile.sized bound uncached profile.getFrame profile.setFrame
      profile.currentIndex resolve profile.check
  have literal : hooks.evalOperand choice (.Constant ⟨span, none, .Val (.Scalar (.Int 1 1)) 0⟩)
      (some layout) ready = .ok copiedValue ready := by
    change config.operands.constant choice ⟨span, none, .Val (.Scalar (.Int 1 1)) 0⟩ (some layout) ready = _
    rw [constant]
    exact evalTrue runtime config.functions config.arithmetic externStatic classify span layout ready
  have liveCached : cached.locals[0].value = .live (.immediate old) := by
    simpa [cached, cacheBool] using live
  have copied : hooks.copyOp choice copiedValue dest ready = .ok () final :=
    copyTrueLocal config.access (ExecutionMachine.withValidation config limits).compiler
      (profilePlace config limits) (ExecutionMachine.withValidation config limits).copy choice false older cached machine
      layout profile.sized sizedCache old liveCached noClocks profile.checking profile.mode profile.debug
      profile.getFrame profile.currentIndex profile.debugOff profile.writer profile.stable
      profile.compatible profile.padding rfl profile.validationOff
  have scopedCopy : hooks.withRetagMode choice .Default (hooks.copyOp choice copiedValue dest) ready =
      .ok () final := by
    change MachineHooks.withRetagMode .Default (hooks.copyOp choice copiedValue dest) ready = _
    have startTrack : ready.machine.borrowTracker = some tracker := tracked
    have endTrack : final.machine.borrowTracker = some tracker := tracked
    have stableTracker (state : State) (h : state.machine.borrowTracker = some tracker) :
        {state with machine := {state.machine with borrowTracker := some tracker}} = state := by
      cases state with
      | mk stack machine =>
        cases machine
        simp_all
    have entered : {ready with machine := {ready.machine with
      borrowTracker := some {tracker with retagMode := .Default}}} = ready := by
      rw [← defaultMode]
      exact stableTracker ready startTrack
    have endSame : {final with machine := {final.machine with
      borrowTracker := some {tracker with retagMode := tracker.retagMode}}} = final :=
      stableTracker final endTrack
    simp [MachineHooks.withRetagMode, startTrack, entered, copied, endTrack, endSame]
  change evalRvalueIntoPlace hooks choice _ _ input = .ok () final
  have layoutEq : hooks.placeLayout dest = layout := rfl
  simp only [evalRvalueIntoPlace, bind, Bind.bind, EStateM.bind, evaluate, layoutEq, beq_self_eq_true, ↓reduceIte]
  rw [literal]
  exact scopedCopy

/-- The canonical Return copy can use the same immediate Boolean path when
the caller supplies its own whole local zero as the return destination. -/
theorem copyReturnTrue (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (choice : C) (layout : LocalLayout)
    (older : Array Frame) (caller : Frame) (machine : MachineHooks.MachineState K U)
    (profile : BooleanLocalProfile config limits choice layout machine)
    (bound : 0 < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[0].value = .live (.immediate old))
    (noClocks : caller.extra.dataRace = none) :
    (ExecutionMachine.terminatorHooks config limits).copyReturn choice
      ⟨.immediate (.scalar (.fromBool true)), layout⟩
      (.frameLocal older.size 0 none layout caller.localsIdentity) (atFrame older caller machine) =
      (atFrame older (setTrue caller bound) machine, .ok ()) := by
  have copied := copyTrueLocal config.access (ExecutionMachine.withValidation config limits).compiler
      (profilePlace config limits) (ExecutionMachine.withValidation config limits).copy choice true older caller machine
      layout profile.sized bound old live noClocks profile.checking profile.mode profile.debug
      profile.getFrame profile.currentIndex profile.debugOff profile.writer profile.stable
      profile.compatible profile.padding rfl profile.validationOff
  change MachineHooks.run
    (copyRuntimePlace (profilePlace config limits) (ExecutionMachine.withValidation config limits).copy
      choice ⟨.immediate (.scalar (.fromBool true)), layout⟩
      ⟨.local older.size 0 none caller.localsIdentity, layout⟩ true) (atFrame older caller machine) = _
  unfold MachineHooks.run Call.run
  rw [copied]

/-- Read the actual return operand from a cached, sized Boolean local in a
profile without frame-local race clocks. -/
theorem readReturnTrue (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (choice : C) (layout : LocalLayout)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (profile : BooleanLocalProfile config limits choice layout machine)
    (bound : 0 < frame.locals.size)
    (live : frame.locals[0].value = .live (.immediate (.scalar (.fromBool true))))
    (cached : frame.locals[0].layout = some layout) (noClocks : frame.extra.dataRace = none)
    (reader : (profilePlace config limits).localToOp choice 0 =
      PlaceMachine.localToOp (ExecutionMachine.withValidation config limits).compiler choice 0) :
    (ExecutionMachine.terminatorHooks config limits).returnOperand choice (atFrame older frame machine) =
      (atFrame older frame machine, .ok ⟨.immediate (.scalar (.fromBool true)), layout⟩) := by
  have slot : frame.getLocal 0 = .ok frame.locals[0] := by simp [Frame.getLocal, bound] <;> rfl
  have operand : frame.getLocalOperand 0 = .ok (.immediate (.scalar (.fromBool true))) := by
    simp [Frame.getLocalOperand, slot, live, bind, Bind.bind, Except.bind, pure, Pure.pure,
      Except.pure, LocalState.access, Except.mapError]
  change MachineHooks.run ((profilePlace config limits).localToOp choice 0) (atFrame older frame machine) = _
  rw [reader]
  let compiler := (ExecutionMachine.withValidation config limits).compiler
  have mode := profile.mode
  cases checkingEq : profile.checking <;>
    simp [MachineHooks.run, Call.run, PlaceMachine.localToOp, PlaceMachine.localToOpCore,
      PlaceMachine.layoutLocal, MachineHooks.currentFrame, Stack.currentFrame?, slot, operand,
      MachineHooks.afterLocalRead, noClocks, cached, mode, checkingEq, profile.sized, atFrame, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get] <;> rfl

#print axioms copyReturnTrue
#print axioms readReturnTrue
#print axioms evalAssignTrue
#print axioms evalUncachedDest
#print axioms copyTrueLocal
#print axioms evalTrue
#print axioms writeTrueLocal
end DuplicatePrefix.ZeroBoolean

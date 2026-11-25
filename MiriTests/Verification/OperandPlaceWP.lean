import Miri.Verification.OperandPlaceWP

namespace MiriTests.Verification.OperandPlaceWP

open Miri.ABI Miri.Interpreter Miri.MIR Miri.Memory Miri.Verification RvalueWP OperandPlaceWP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Op" => OpTy Provenance

/-- The assignment source uses the cached layout and leaves the source slot
live for either Copy or Move. -/
example (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (id : LocalId) (hint cached : LocalLayout) (before : State)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra) (slot : LocalState Provenance LocalLayout)
    (operand : MemPlace Provenance) (post : Op → State → Prop) (onError : StepError → State → Prop)
    (frame : before.stack.currentFrame? = some current)
    (localFound : current.getLocal id = .ok slot)
    (layoutFound : slot.layout = some cached)
    (valueFound : current.getLocalOperand id = .ok (.indirect operand))
    (debug : config.compiler.debugAssertions = false) :
    let hooks := ExecutionMachine.rvalueHooks config limits
    let place : Place := ⟨id, #[]⟩
    actionPre (hooks.evalOperand choice (.Copy place) (some hint)) post onError before =
      post ⟨.indirect operand, cached⟩ before ∧
    actionPre (hooks.evalOperand choice (.Move place) (some hint)) post onError before =
      post ⟨.indirect operand, cached⟩ before := by
  simp only [miri_initial_wp]
  simp only [StorageLiveWP.currentFramePre, frame, localFound, layoutFound, valueFound, debug,
    Except.mapError, scalarCheckPre, Bool.false_eq_true, ↓reduceIte, and_self]

/-- A failed check against the known layout uses the state after the
compiler's layout effect and never publishes the layout. -/
example (hooks : OperandMachine.Hooks K U C) (choice : C)
    (id : LocalId) (hint computed : LocalLayout) (before queried : State)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra) (slot : LocalState Provenance LocalLayout)
    (post : Op → State → Prop) (onError : StepError → State → Prop)
    (frame : before.stack.currentFrame? = some current)
    (localFound : current.getLocal id = .ok slot) (uncached : slot.layout = none)
    (debug : hooks.compiler.debugAssertions = true)
    (layout : hooks.compiler.layout choice id before = .ok computed queried)
    (incompatible : hooks.layoutCompatible computed hint = .ok false) :
    actionPre (OperandMachine.localToOp hooks choice id (some hint)) post onError before =
      onError (.invalidProgram "known local layout differs from compiler layout") queried := by
  simp only [miri_initial_wp]
  simp only [frame, localFound, uncached, debug, layout, incompatible,
    Except.mapError, scalarCheckPre, actionPre, Bool.false_eq_true, ↓reduceIte]

/-- Indexing an indirect operand uses the state left by the index read for
the typed bounds error. -/
example (hooks : OperandMachine.Hooks K U C) (choice : C) (id : LocalId)
    (memory : MemPlace Provenance) (layout : LocalLayout) (before indexed : State)
    (post : Op → State → Prop) (onError : StepError → State → Prop)
    (indexRead : hooks.projection.localIndex choice id before = .ok 4 indexed)
    (array : layout.layout.fields = .Array Size.ZERO 3)
    (sized : layout.layout.isSized = true) :
    actionPre (OperandMachine.project hooks choice ⟨.indirect memory, layout⟩ (.Index id))
      post onError before = onError (.undefinedBehavior "place index 4 out of bounds for 3") indexed := by
  simp only [miri_initial_wp]
  simp only [array, sized, Bool.not_true, Bool.false_eq_true, ↓reduceIte, actionPre, indexRead]
  rfl

/-- Simple destination dereference forwards the caller's bypass flag and
uses the dereference failure state. -/
example (hooks : PlaceProjectionHooks Provenance State C MachineHooks.FrameExtra) (choice : C)
    (id : LocalId) (base : RuntimePlace Provenance) (before ready failed : State) (error : StepError)
    (post : RuntimePlace Provenance → State → Prop) (onError : StepError → State → Prop)
    (localReady : ∀ (next : RuntimePlace Provenance → State → Prop),
      PlaceMentionWP.localPre hooks.place choice id next onError before = next base ready)
    (deref : hooks.place.deref choice base true ready = .error error failed) :
    actionPre (PlaceDynamic.evalPlace hooks choice ⟨id, #[.Deref]⟩ true) post onError before =
      onError error failed := by
  rw [actionPre_evalPlaceSimpleDeref]
  rw [localReady]
  simp only [actionPre, deref]

/-- The bare destination reaches its type check even when evaluation requests
the simple-dereference validity bypass. -/
example (hooks : PlaceProjectionHooks Provenance State C MachineHooks.FrameExtra) (choice : C)
    (id : LocalId) (base : RuntimePlace Provenance) (before ready failed : State) (error : StepError)
    (post : RuntimePlace Provenance → State → Prop) (onError : StepError → State → Prop)
    (localReady : ∀ (next : RuntimePlace Provenance → State → Prop),
      PlaceMentionWP.localPre hooks.place choice id next onError before = next base ready)
    (typeFailed : hooks.place.checkPlaceType choice ⟨id, #[]⟩ base ready = .error error failed) :
    actionPre (PlaceDynamic.evalPlace hooks choice ⟨id, #[]⟩ true) post onError before =
      onError error failed := by
  rw [actionPre_evalPlaceLocal, localReady]
  simp only [actionPre, typeFailed]

/-- Runtime-check operands use the compiler's flag before querying the
Boolean layout. A failed layout query retains the state it leaves. -/
example (hooks : OperandMachine.Hooks K U C) (choice : C)
    (before selected failed : State) (error : StepError)
    (post : Op → State → Prop) (onError : StepError → State → Prop)
    (flag : hooks.runtimeChecks choice .OverflowChecks before = .ok false selected)
    (layout : hooks.boolLayout choice selected = .error error failed) :
    actionPre (OperandMachine.evalOperand hooks choice (.RuntimeChecks .OverflowChecks) none)
      post onError before = onError error failed := by
  rw [actionPre_evalOperand]
  simp only [actionPre, flag, layout]

/-- The immediate-local path checks the machine clock after the validation
probe. A missing global clock reports the state left by that probe. -/
example (hooks : OperandMachine.Hooks K U C) (choice : C) (id : LocalId)
    (layout : LocalLayout) (before checked : State)
    (current checkedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (slot : LocalState Provenance LocalLayout) (value : Immediate Provenance)
    (clocks : Miri.Concurrency.LocalRace.FrameState) (post : Op → State → Prop)
    (onError : StepError → State → Prop)
    (frame : before.stack.currentFrame? = some current)
    (localFound : current.getLocal id = .ok slot) (cached : slot.layout = some layout)
    (operand : current.getLocalOperand id = .ok (.immediate value))
    (sized : layout.layout.backendRepr.isUnsized = false)
    (validation : hooks.compiler.validationInProgress before = .ok false checked)
    (checkedFrameFound : checked.stack.currentFrame? = some checkedFrame)
    (frameClocks : checkedFrame.extra.dataRace = some clocks)
    (globalClock : checked.machine.dataRace = none) :
    actionPre (OperandMachine.localToOp hooks choice id none) post onError before =
      onError (.invalidProgram "frame has vector clocks but machine does not") checked := by
  simp only [miri_initial_wp]
  simp only [StorageLiveWP.currentFramePre, frame, localFound, cached, operand, sized, validation,
    Except.mapError, scalarCheckPre, actionPre, Bool.false_eq_true, ↓reduceIte, localReadClockPre,
    checkedFrameFound, frameClocks, globalClock]

section Production

variable {Os R HostP H D Aff B F T : Type}
local notation "Stored" => Miri.Input.EvalCoreMachine.Stored Os R HostP H D O Aff B Host
local notation "IndexState" => Miri.Input.EvalCoreMachine.State Os R HostP H D O Aff B Host
local notation "MemoryKind" => MiriMemoryKind

/-- The actual production index projection decodes a cached immediate local
using the target pointer width. No local-index hook result is assumed. -/
example (prepared : Miri.Input.CompilerProviders.Prepared)
    (options : Miri.Input.EvalPlaceConstruction.Options)
    (access : ValidityMachine.Access MemoryKind Stored)
    (allocation : PlaceMachine.AllocationConfig MemoryKind
      (Miri.Input.EvalCoreMachine.User Os R HostP H D O Aff B Host))
    (compiler : ValidityMachine.Compiler MemoryKind Stored C)
    (vtable : VTableHooks Provenance IndexState C F T) (choice : C) (id : LocalId)
    (before : IndexState) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (post : UInt64 → IndexState → Prop) (onError : StepError → IndexState → Prop)
    (active : before.stack.currentFrame? = some frame)
    (slotFound : frame.getLocal id = .ok slot) (cached : slot.layout = some layout)
    (operand : frame.getLocalOperand id = .ok (.immediate (.scalar (.fromScalarInt (.ofUInt64 4)))))
    (sized : layout.layout.isSized = true) (ghost : before.machine.user.payload.ghost = true)
    (word : access.runtime.pointerSize = Size.ofBytes 8)
    (readable : isPrimitiveReadable (localMemoryLayout layout).backendRepr = true)
    (untouched : access.retainTouched before.machine none = before.machine) :
    actionPre ((Miri.Input.EvalPlaceConstruction.projection prepared options access allocation compiler
      vtable).localIndex choice id) post onError before = post 4 before := by
  rw [actionPre_productionLocalIndex]
  rw [PlaceReadWriteWP.actionPre_localToOpCore]
  simp only [PlaceReadWriteWP.localToOpPre, actionPre_productionLocalLayout,
    StorageLiveWP.actionPre_currentFrame, StorageLiveWP.currentFramePre, active, slotFound,
    Except.mapError, scalarCheckPre, cached, operand, sized, ↓reduceIte,
    actionPre_validationInProgress, ghost, actionPre_scopedRead, PlaceReadWriteWP.actionPre_readImmediate,
    PlaceReadWriteWP.immediateReadPre_immediate, word, readable, untouched]
  rfl

/-- Derive null-reference UB through the typed dereference used by the source
compiler binding. The hypotheses supply compiler queries and the machine's
alignment policy, with no premise on pointer construction or dereference. -/
example [DecidableEq K] (access : ValidityMachine.Access K U)
    (facts : Miri.Input.CompilerFactAdapters.Prepared) (choice : C)
    (dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State K U) C)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F T) (fuel : Nat)
    (sourceLayout layout : LocalLayout) (pointee : TyId)
    (before : ValidityMachine.State K U)
    (post : MPlaceTy Provenance → ValidityMachine.State K U → Prop)
    (onError : StepError → ValidityMachine.State K U → Prop)
    (kind : (CompilerExecutionProviders.pointerCompiler facts).kind choice sourceLayout.ty before =
      .ok .reference before)
    (deref : (CompilerExecutionProviders.pointerCompiler facts).builtinDeref choice sourceLayout.ty before =
      .ok (some pointee) before)
    (target : (CompilerExecutionProviders.pointerCompiler facts).layoutOf choice pointee before =
      .ok layout before)
    (width : access.runtime.base = ⟨.little, .w64⟩)
    (readable : isPrimitiveReadable (localMemoryLayout sourceLayout).backendRepr = true)
    (untouched : access.retainTouched before.machine none = before.machine)
    (alignment : before.machine.user.payload.alignment = .None)
    (validation : before.machine.user.payload.validation = .Shallow) :
    let source : Op := ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 0))), sourceLayout⟩
    actionPre (PointerPlaceMachine.dereference access (CompilerExecutionProviders.pointerCompiler facts)
      dynamic vtable fuel choice source) post onError before =
      onError (.undefinedBehavior "dereferencing a null reference") before := by
  dsimp only
  rw [actionPre_typedDereference, actionPre_ok kind]
  change actionPre (PlaceMachine.readImmediate access _) _ _ before = _
  simp only [PlaceReadWriteWP.actionPre_readImmediate, PlaceReadWriteWP.immediateReadPre_immediate,
    readable, ↓reduceIte, untouched, actionPre_pointerFromImmediate]
  rw [actionPre_ok deref]
  change actionPre ((CompilerExecutionProviders.pointerCompiler facts).layoutOf choice pointee) _ _ before = _
  rw [actionPre_ok target]
  simp only [Immediate.toScalarAndMeta, Except.mapError, scalarCheckPre, width]
  change actionPre (PointerPlaceMachine.withMetadata access _ _ layout false) _ _ before = _
  simp only [actionPre_pointerWithMetadata, Bool.false_eq_true, ↓reduceIte]
  rw [actionPre_misalignmentSkip]
  · simp only [actionPre_enforceValidity, validation]
    rfl
  · simp only [alignment]
    rfl

end Production

end MiriTests.Verification.OperandPlaceWP

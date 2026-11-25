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
    (debug : (ExecutionMachine.withValidation config limits).compiler.debugAssertions = false) :
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
  rw [actionPre_evalPlace]
  have bypass : (true && (#[.Deref] : Array ProjectionElem) == #[.Deref]) = true := by decide
  simp only [bypass, ↓reduceIte]
  rw [localReady]
  simp only [actionPre, deref]

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

end MiriTests.Verification.OperandPlaceWP

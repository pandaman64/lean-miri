import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.ConstantMachine

namespace DuplicatePrefix.LanguageGuardAssignment
open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR

variable {K U C : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Frame Provenance LocalLayout MachineHooks.FrameExtra

omit [DecidableEq K] in
/-- An exported integer scalar constant with a known Boolean layout uses the
real constant evaluator and leaves the machine unchanged. -/
theorem guardTrueConstant (runtime : Miri.Input.RuntimeMetadata)
    (functions : FunctionPointers.Hooks K U O) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K U (Pointer Provenance))
    (error : ConstantError → StepError) (layout : LocalLayout) (state : State) :
    ConstantMachine.evalOperandWithLayout runtime functions arithmetic externStatic error
      ⟨⟨350⟩, none, .Val (.Scalar (.Int 1 1)) 0⟩ (some layout) none state =
      .ok ⟨.immediate (.scalar (Scalar.fromBool true)), layout⟩ state := by
  cases state
  rfl

/-- Direct place evaluation uses the actual local lookup and installs its
compiler layout in the frame when the local is first observed. -/
theorem uncachedLocalPlace
    (access : PlaceMachine.AccessConfig K U) (alloc : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (localId : LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (slotAt : frame.locals[localId]? = some slot)
    (uncached : slot.layout = none)
    (sized : layout.layout.isSized = true)
    (layoutQuery : compiler.layout choice localId ⟨⟨older.push frame⟩, machine⟩ =
      .ok layout ⟨⟨older.push frame⟩, machine⟩) :
    let cachedSlot : LocalState Provenance LocalLayout := {slot with layout := some layout}
    let cached := {frame with locals := frame.locals.setIfInBounds localId cachedSlot}
    localToPlace (PlaceMachine.placeHooks access alloc compiler) choice localId
      (⟨⟨older.push frame⟩, machine⟩ : State) =
      .ok ⟨.local older.size localId none frame.localsIdentity, layout⟩
        ⟨⟨older.push cached⟩, machine⟩ := by
  have found := (Array.getElem?_eq_some_iff.mp slotAt).2
  have bound := (Array.getElem?_eq_some_iff.mp slotAt).1
  have slotEq : frame.getLocal localId = .ok slot := by
    simp [Frame.getLocal, bound, found, pure, Pure.pure, Except.pure]
  simp [localToPlace, placeLayoutOfLocal, PlaceMachine.placeHooks,
    MachineHooks.currentFrame, MachineHooks.setCurrentFrame, Stack.currentFrame?, Stack.frameIndex,
    slotEq, Frame.getOrCacheLocalLayout, uncached, sized, layoutQuery, bound, Array.setIfInBounds,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
    Except.pure, Except.bind]

/-- Running the actual direct MIR place evaluator installs the compiler's
Boolean layout and checks the place type in that updated frame. -/
theorem evalUncachedLocalPlace
    (projection : PlaceProjectionHooks Provenance State C MachineHooks.FrameExtra)
    (access : PlaceMachine.AccessConfig K U) (alloc : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (placeHooks : projection.place = PlaceMachine.placeHooks access alloc compiler)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (localId : LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (slotAt : frame.locals[localId]? = some slot)
    (uncached : slot.layout = none)
    (sized : layout.layout.isSized = true)
    (layoutQuery : compiler.layout choice localId ⟨⟨older.push frame⟩, machine⟩ =
      .ok layout ⟨⟨older.push frame⟩, machine⟩)
    (check : compiler.checkPlaceType choice ⟨localId, #[]⟩ = fun _ => pure ()) :
    let cachedSlot : LocalState Provenance LocalLayout := {slot with layout := some layout}
    let cached := {frame with locals := frame.locals.setIfInBounds localId cachedSlot}
    PlaceDynamic.evalPlace projection choice ⟨localId, #[]⟩ true
      (⟨⟨older.push frame⟩, machine⟩ : State) =
      .ok ⟨.local older.size localId none frame.localsIdentity, layout⟩
        ⟨⟨older.push cached⟩, machine⟩ := by
  have localPlace := uncachedLocalPlace access alloc compiler choice older frame machine
    localId slot layout slotAt uncached sized layoutQuery
  simp only [PlaceDynamic.evalPlace, placeHooks, bind, Bind.bind, EStateM.bind]
  rw [localPlace]
  simp [PlaceMachine.placeHooks, check, ← Array.forIn_toList, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]

end DuplicatePrefix.LanguageGuardAssignment

#print axioms DuplicatePrefix.LanguageGuardAssignment.guardTrueConstant
#print axioms DuplicatePrefix.LanguageGuardAssignment.evalUncachedLocalPlace

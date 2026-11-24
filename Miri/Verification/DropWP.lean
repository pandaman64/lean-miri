import Miri.Verification.CanonicalStepWP
import Miri.Verification.CallDispatchWP

/-! Exact pullbacks for synchronous MIR drops and their typed call setup. -/


namespace Miri.Verification.DropWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Std.WP
open RvalueWP (actionPre actionPre_bind_fun actionPre_eq_wp)

variable {P S C E Other Extern FnABI ArgABI K U O X Host : Type}
local notation "Hooks" => CallHooks P S C E Other Extern FnABI ArgABI
local notation "Errors" => StepError → S → Prop
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Limits" => ExecutionMachine.Limits
local notation "State" => MachineHooks.State K U
local notation "MachineErrors" => StepError → State → Prop

/-- The debug consistency query runs only for a non-dynamic receiver and may
itself fail. The final glue lookup runs for either receiver kind. -/
def receiverPre (hooks : Hooks) (choice : C) (original : CallInstance) (place : MPlaceTy P)
    (post : MPlaceTy P → S → Prop) (onError : Errors) : S → Prop :=
  actionPre (hooks.isDynamic place.layout.ty) (fun dynamic =>
    if dynamic then actionPre (hooks.unpackDynForDrop choice place) post onError
    else if hooks.debugAssertions then
      actionPre (hooks.resolveDropGlue choice place.layout.ty) (fun resolved ready =>
        if original == resolved then post place ready
        else onError (.invalidProgram "drop glue instance mismatch") ready) onError
    else post place) onError

/-- Allocate the receiver, perform dynamic unpacking or the debug check, then
build the ordinary Rust-ABI call request with the original target and unwind. -/
def initDropPre (hooks : Hooks) (choice : C) (budget : Nat) (place : RuntimeStackPlace P)
    (original : CallInstance) (target : BasicBlockId) (unwind : UnwindAction)
    (post : S → Prop) (onError : Errors) : S → Prop :=
  actionPre (hooks.forceAllocation choice place) (fun allocated =>
    receiverPre hooks choice original allocated (fun receiver =>
      actionPre (hooks.resolveDropGlue choice receiver.layout.ty) (fun instanceId =>
        actionPre (hooks.fnAbiOfInstance choice instanceId #[]) (fun abi =>
          actionPre (hooks.mplaceToMutRef choice receiver) (fun arg =>
            actionPre (hooks.fakeUnitReturn choice) (fun ret =>
              CallWP.dispatchPre hooks choice post onError budget
                ⟨.Instance instanceId, hooks.rustAbi, some abi, #[.Copy arg], false,
                  ret, some target, unwind⟩) onError) onError) onError) onError) onError) onError

theorem actionPre_initDrop (hooks : Hooks) (choice : C) (budget : Nat)
    (place : RuntimeStackPlace P) (original : CallInstance) (target : BasicBlockId)
    (unwind : UnwindAction) (post : S → Prop) (onError : Errors) :
    actionPre (Call.initDropInPlaceCall hooks choice budget place original target unwind)
      (fun _ => post) onError = initDropPre hooks choice budget place original target unwind post onError := by
  simp only [Call.initDropInPlaceCall, initDropPre, receiverPre, actionPre_bind_fun]
  congr 1
  funext allocated
  congr 1
  funext dynamic
  cases dynamic
  · by_cases debug : hooks.debugAssertions = true
    · simp only [debug, Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun]
      congr 1
      funext resolved ready
      by_cases same : (original == resolved) = true
      · simp only [Call.require_eq, same, ↓reduceIte, CallWP.dispatchPre_eq_wp, ← actionPre_eq_wp]
        rfl
      · simp only [Call.require_eq, same]
        rfl
    · simp only [debug, Bool.false_eq_true, ↓reduceIte, pure_bind, actionPre_bind_fun,
        CallWP.dispatchPre_eq_wp, ← actionPre_eq_wp]
  · simp only [↓reduceIte, actionPre_bind_fun, CallWP.dispatchPre_eq_wp, ← actionPre_eq_wp]

variable [DecidableEq K]

/-- The empty glue branch changes the active frame location. The other
instance kinds go through the full typed drop initialization. -/
def gluePre (hooks : ExecutionMachine.Calls K U C O X) (choice : C) (budget : Nat)
    (place : RuntimePlace Provenance) (callee : CallInstance) (target : BasicBlockId)
    (unwind : UnwindAction) (post : State → Prop) (onError : MachineErrors) : State → Prop :=
  actionPre (hooks.instanceKind callee) (fun
    | .Shim (.DropGlue _ none) => InstructionWP.jumpPre target post onError
    | _ => initDropPre hooks choice budget place.stackView callee target unwind post onError) onError

/-- Resolve glue from the evaluated place's layout, with ordinary validity
checks enabled for the evaluation. -/
def dropPre (config : Config) (limits : Limits) (choice : C) (place : Place)
    (target : BasicBlockId) (unwind : UnwindAction) (post : State → Prop)
    (onError : MachineErrors) : State → Prop :=
  let checked := ExecutionMachine.withValidation config limits
  let hooks := ExecutionMachine.callHooks checked limits
  actionPre (PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks checked) choice place false)
    (fun dest => actionPre (hooks.resolveDropGlue choice dest.layout.ty)
      (fun callee => gluePre hooks choice limits.callDispatch dest callee target unwind post onError)
      onError) onError

theorem dropEffect_eq (config : Config) (limits : Limits) (choice : C) (place : Place)
    (target : BasicBlockId) (unwind : UnwindAction) (post : State → Prop)
    (onError : MachineErrors) :
    wp (CanonicalStepWP.dropEffect config limits choice place target unwind)
      (fun _ => post) onError = dropPre config limits choice place target unwind post onError := by
  simp only [← actionPre_eq_wp, CanonicalStepWP.dropEffect, dropPre, gluePre, actionPre_bind_fun]
  congr 1
  funext place
  congr 1
  funext callee
  congr 1
  funext kind
  cases kind <;> try exact actionPre_initDrop _ _ _ _ _ _ _ _ _
  case Shim shim =>
    cases shim <;> try exact actionPre_initDrop _ _ _ _ _ _ _ _ _
    case DropGlue definition ty =>
      cases ty
      · funext state
        change actionPre (do
          let previous ← get
          let (after, outcome) := ControlFlow.goToBlock target previous
          set after
          match outcome with
          | .ok value => pure value
          | .error error => throw error) (fun _ => post) onError state =
            InstructionWP.jumpPre target post onError state
        change _ = InstructionWP.locationPre (.mir ⟨target, 0⟩) post onError state
        unfold InstructionWP.locationPre ControlFlow.goToBlock ControlFlow.setLocation
        unfold actionPre
        simp only [bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
        cases state.stack.currentFrame? <;> rfl
      · exact actionPre_initDrop _ _ _ _ _ _ _ _ _

/-- Runtime MIR rejects an unexpanded async drop before evaluating the place. -/
theorem selectedDrop_eq (config : Config) (limits : Limits) (choice : C)
    (info : SourceInfo) (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
    (replace : Bool) (asyncDrop : Option BasicBlockId) (post : State → Prop)
    (onError : MachineErrors) (before : State) :
    CanonicalStepWP.selectedTerminatorPre config limits choice
      ⟨info, .Drop place target unwind replace asyncDrop⟩ post onError before =
      if asyncDrop.isSome then
        onError (.invalidProgram "Async Drop must be expanded or reset to sync") before
      else dropPre config limits choice place target unwind post onError before := by
  simp only [CanonicalStepWP.selectedTerminatorPre, dropEffect_eq]

/-- A dynamic place is checked before its metadata is interpreted. The recovered
type supplies the layout, and the zero-offset rebase clears metadata. -/
theorem actionPre_unpackVTable {F A : Type}
    (hooks : VTableHooks Provenance S C F A) (choice : C)
    (place : MPlaceTy Provenance) (predicates : PredicateList)
    (post : OpTy Provenance → S → Prop) (onError : Errors) :
    actionPre (VTable.unpackDynTrait hooks choice ⟨.indirect place.mplace, place.layout⟩ predicates)
      post onError =
      actionPre (hooks.isDynamic choice place.layout.ty) (fun dynamic =>
        if !dynamic then onError (.invalidProgram "unpack_dyn_trait requires dynamic type")
        else match place.mplace.metadata.unwrapMeta with
        | .error _ => onError (.invalidProgram "dynamic place has no metadata")
        | .ok scalar => match scalar.toPointer hooks.target with
          | .error error => onError (ScalarOps.scalarError error)
          | .ok pointer =>
            actionPre (VTable.getPtrVTableType hooks choice pointer (some predicates)) (fun ty =>
              actionPre (hooks.layoutOf choice ty) (fun layout =>
                actionPre (hooks.memoryOffset choice place.mplace Size.ZERO .wrapping .none)
                  (fun memory => post ⟨.indirect memory, layout⟩) onError) onError) onError)
        onError := by
  simp only [VTable.unpackDynTrait, actionPre_bind_fun]
  congr 1
  funext dynamic
  cases dynamic
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases place.mplace.metadata.unwrapMeta with
    | error => rfl
    | ok scalar =>
      simp only [pure_bind]
      cases scalar.toPointer hooks.target <;> simp only [actionPre_bind_fun] <;> rfl

/-- A dynamic drop must get its predicates from the dropped type before
unpacking the vtable. The unpacked representation must remain indirect. -/
theorem actionPre_unpackDyn (hooks : VirtualCalls.Hooks Provenance S C E) (choice : C)
    (place : MPlaceTy Provenance) (post : MPlaceTy Provenance → S → Prop) (onError : Errors) :
    actionPre (VirtualCalls.unpackDynForDrop hooks choice place) post onError =
      actionPre (hooks.compiler.dynamicData place.layout.ty) (fun
        | none => onError (.invalidProgram "drop dynamic data missing")
        | some data =>
          actionPre (VTable.unpackDynTrait hooks.vtable choice
            ⟨.indirect place.mplace, place.layout⟩ data.predicates) (fun unpacked =>
              match unpacked.op with
              | .indirect memory => post ⟨memory, unpacked.layout⟩
              | .immediate _ => onError (.invalidProgram "unpacked dyn drop became immediate")) onError)
        onError := by
  simp only [VirtualCalls.unpackDynForDrop, actionPre_bind_fun]
  congr 1
  funext data
  cases data
  · rfl
  · simp only [actionPre_bind_fun]
    congr 1
    funext unpacked
    cases unpacked.op <;> rfl

/-- Form the erased mutable reference with the original pointer and metadata.
The reference layout is queried only after the pointee check passes. -/
theorem actionPre_mutRef (hooks : VirtualCalls.Hooks Provenance S C E)
    (place : MPlaceTy Provenance) (post : OpTy Provenance → S → Prop) (onError : Errors) :
    actionPre (VirtualCalls.mplaceToMutRef hooks place) post onError =
      actionPre (hooks.compiler.mutReferenceType place.layout.ty) (fun refTy =>
        match place.mplace.toRef hooks.target with
        | .error error => onError (.invalidProgram (reprStr error))
        | .ok immediate => actionPre (hooks.compiler.builtinDeref refTy) (fun pointee =>
          if pointee != some place.layout.ty then onError (.invalidProgram "mutable drop reference pointee mismatch")
          else actionPre (hooks.compiler.layoutOf refTy)
            (fun layout => post ⟨.immediate immediate, layout⟩) onError) onError) onError := by
  simp only [VirtualCalls.mplaceToMutRef, actionPre_bind_fun, VirtualCalls.scalarError_eq]
  congr 1
  funext refTy
  cases place.mplace.toRef hooks.target with
  | error => rfl
  | ok immediate =>
    have purePre : actionPre (pure immediate) =
        (fun (post : Immediate Provenance → S → Prop) _ => post immediate) := rfl
    rw [purePre]
    dsimp only
    congr 1
    funext pointee
    by_cases mismatch : (pointee != some place.layout.ty) = true <;>
      simp only [mismatch, Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun] <;> rfl

/-- Canonical drop-specific leaves, reusing compiler and memory hooks from the
ordinary execution configuration. -/
theorem canonicalDropHooks (config : Config) (limits : Limits) :
    let checked := ExecutionMachine.withValidation config limits
    let hooks := ExecutionMachine.callHooks checked limits
    let virtual := ExecutionCalls.virtualHooks checked.virtual checked.access
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation checked limits))
      checked.compiler.debugAssertions
    hooks.isDynamic = (fun ty => do return (← virtual.compiler.classifyReceiver ty) == .dynamic) ∧
    hooks.unpackDynForDrop = VirtualCalls.unpackDynForDrop virtual ∧
    hooks.mplaceToMutRef = (fun _ => VirtualCalls.mplaceToMutRef virtual) ∧
    hooks.resolveDropGlue = (fun _ => virtual.compiler.resolveDropGlue) ∧
    hooks.fakeUnitReturn = (fun _ => do
      let layout ← virtual.compiler.unitLayout
      match FunctionCalls.fakeAllocZst (P := Provenance) layout with
      | .ok memory => pure (.memory memory)
      | .error error => throw error) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem canonicalResolveDrop (config : Config) (limits : Limits) (choice : C) (ty : TyId) :
    (ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits).resolveDropGlue choice ty = config.virtual.compiler.resolveDropGlue ty := rfl

private theorem actionPre_pure_fun {A : Type} (value : A) (post : A → S → Prop)
    (onError : Errors) :
    actionPre (pure value) post onError = post value := rfl

theorem actionPre_unitReturn (config : Config) (limits : Limits) (choice : C)
    (post : RuntimeStackPlace Provenance → State → Prop) (onError : MachineErrors) :
    actionPre ((ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits).fakeUnitReturn choice) post onError =
      actionPre config.virtual.compiler.unitLayout (fun layout =>
        match FunctionCalls.fakeAllocZst (P := Provenance) layout with
        | .ok memory => post (.memory memory)
        | .error error => onError error) onError := by
  rw [(canonicalDropHooks config limits).2.2.2.2, actionPre_bind_fun]
  congr 1
  funext layout
  cases FunctionCalls.fakeAllocZst (P := Provenance) layout <;> rfl

/-- Open the selected drop, then its glue and typed setup. The remaining call
dispatch can be reduced with `miri_call_dispatch_wp`. -/
macro "miri_drop_wp" : tactic =>
  `(tactic|
    simp (config := { failIfUnchanged := false }) only
      [selectedDrop_eq, dropEffect_eq, actionPre_initDrop, dropPre, gluePre, initDropPre, receiverPre,
        actionPre_unitReturn, (canonicalDropHooks _ _).1, (canonicalDropHooks _ _).2.1,
        (canonicalDropHooks _ _).2.2.1, canonicalResolveDrop,
        actionPre_unpackDyn, actionPre_unpackVTable, actionPre_mutRef, actionPre_bind_fun, actionPre_pure_fun,
        Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte])

end Miri.Verification.DropWP

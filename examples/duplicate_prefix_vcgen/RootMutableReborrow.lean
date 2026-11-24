import Representative
import Miri.Interpreter.ExecutionMachine
import Miri.Verification.MutableTypedRetag
import Lean

namespace DuplicatePrefix.RootMutableReborrow
open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open RetagPolicy

variable {K U C O X Host : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

def policy : NewPermission := ⟨.ReservedFrz false, .ReservedIM, .ReservedFrz false, none⟩

def initialFrozen : Tree.LocationState := ⟨.ReservedFrz false, true, .Read⟩

theorem initialFrozen_eq : initialLocationState policy true = .ok initialFrozen := by rfl

/-- The compiler selects an unprotected reservation for a two-phase mutable
borrow. Unlike FnEntry this path does not query the implicit-write settings. -/
theorem selectPolicy (hooks : TypedRetag.Hooks K U) (pointee : TyId)
    (state : State)
    (unpin : hooks.isUnpin pointee state = .ok true state)
    (unsafeUnpin : hooks.isUnsafeUnpin pointee state = .ok true state)
    (freeze : hooks.typeIsFreeze pointee state = .ok true state) :
    TypedRetag.newPermission hooks pointee .Mutable .TwoPhase state =
      .ok (some policy) state := by
  simp [TypedRetag.newPermission, unpin, unsafeUnpin, freeze,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rfl

theorem frozenPermissions (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (before : State)
    (precise : hooks.preciseInteriorMut before = .ok false before)
    (freeze : hooks.typeIsFreeze place.layout.ty before = .ok true before) :
    TypedRetag.insidePermissions hooks budget place size policy before =
      .ok (DedupRangeMap.new size initialFrozen) before := by
  simp [TypedRetag.insidePermissions, precise, freeze, initialFrozen_eq, TypedRetag.checked,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

theorem noProtector (location : RetagPipeline.ResolvedLocation) (tag : BorTag) (state : State) :
    Miri.Verification.TypedRetagWP.registerProtector location policy tag state = .ok () state := by rfl

theorem retagMutablePointer [DecidableEq K]
    (hooks : TypedRetag.Hooks K U) (budget : Nat) (value output : RvalueImmTy Provenance)
    (ty pointee : TyId) (before shapeState referenceState placeState retaggedState after : State)
    (place retagged : MPlaceTy Provenance) (tracker : MachineHooks.BorrowState)
    (trackerPresent : before.machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .TwoPhase)
    (shape : hooks.typeShape ty before = .ok RetagPipeline.RetagTypeShape.reference shapeState)
    (reference : hooks.referencePointee ty shapeState = .ok (pointee, .Mut) referenceState)
    (unpin : hooks.isUnpin pointee referenceState = .ok true referenceState)
    (unsafeUnpin : hooks.isUnsafeUnpin pointee referenceState = .ok true referenceState)
    (freeze : hooks.typeIsFreeze pointee referenceState = .ok true referenceState)
    (position : hooks.immPtrToMPlace value referenceState = .ok place placeState)
    (styled : TypedRetag.retagPlace hooks budget place policy placeState = .ok retagged retaggedState)
    (reassemble : hooks.reconstruct value retagged retaggedState = .ok output after) :
    TypedRetag.machineRetagPtrValue hooks budget value ty before = .ok (some output) after := by
  have selected := selectPolicy hooks pointee referenceState unpin unsafeUnpin freeze
  simp [TypedRetag.machineRetagPtrValue, TypedRetag.retagPtrValue, RetagPipeline.RetagTypeShape.reference,
    RetagPipeline.RetagTypeShape.classify, trackerPresent, mode, shape, reference, selected,
    position, styled, reassemble, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

private def sourcePlace : Place := ⟨1, #[.Deref]⟩
private def destPlace : Place := ⟨16, #[]⟩

theorem code :
    (do
      let source ← GeneratedBodySafety.input.document.bodies[0]?
      let block ← source.mir.basicBlocks[6]?
      pure (← block.statements[7]?).kind) =
        some (.Assign destPlace (.Ref .Erased (.Mut .TwoPhaseBorrow) sourcePlace)) := by rfl

open Lean Elab Tactic in
elab "unfold_reference_lift" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".ExecutionMachine.lift" then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one execution-machine result lifter"

/-- The emitted mutable reference expression evaluates the source and
destination, reconstructs the actual fat reference, and writes it with
validity enabled inside the source's TwoPhase scope. -/
theorem writeReference [DecidableEq K]
    (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (before prepared formed : State) (destination : RuntimePlace Provenance)
    (source : MPlaceTy Provenance) (value : Immediate Provenance)
    (placed : (ExecutionMachine.rvalueHooks config limits).evalPlace choice destPlace true before =
      .ok destination prepared)
    (projected : (ExecutionMachine.rvalueHooks config limits).evalPlace choice sourcePlace true prepared =
      .ok ⟨.memory source.mplace, source.layout⟩ formed)
    (reference : source.mplace.toRef config.access.runtime.base = .ok value)
    (tracker : MachineHooks.BorrowState) (tracked : formed.machine.borrowTracker = some tracker)
    (validating : let entered := {formed with machine := {formed.machine with
        borrowTracker := some {tracker with retagMode := .TwoPhase}}}
      (ExecutionMachine.rvalueHooks config limits).enforceValidity
        choice destination.layout entered = .ok true entered) :
    let hooks := ExecutionMachine.rvalueHooks config limits
    evalRvalueIntoPlace hooks choice (.Ref .Erased (.Mut .TwoPhaseBorrow) sourcePlace) destPlace before =
      MachineHooks.withRetagMode .TwoPhase (hooks.writeImmediate choice value destination) formed := by
  intro hooks
  have memory : hooks.forceAllocation choice ⟨.memory source.mplace, source.layout⟩ formed =
      .ok source.mplace formed := by cases source; rfl
  have assembled : hooks.toRef choice source.mplace formed = .ok value formed := by
    change (ExecutionMachine.rvalueHooks config limits).toRef choice source.mplace formed = _
    unfold ExecutionMachine.rvalueHooks
    dsimp only
    unfold_reference_lift
    rw [show (ExecutionMachine.withValidation config limits).access = config.access from rfl, reference]
    rfl
  have layout : hooks.placeLayout destination = destination.layout := rfl
  have mode : (BorrowKind.Mut .TwoPhaseBorrow == BorrowKind.Mut .TwoPhaseBorrow) = true := rfl
  change hooks.evalPlace choice destPlace true before = _ at placed
  change hooks.evalPlace choice sourcePlace true prepared = _ at projected
  simp only [evalRvalueIntoPlace, bind, Bind.bind, EStateM.bind, placed, projected, memory, assembled,
    layout, mode, ↓reduceIte]
  change MachineHooks.withRetagMode .TwoPhase _ formed = _
  unfold MachineHooks.withRetagMode
  rw [tracked]
  dsimp only at validating ⊢
  change hooks.enforceValidity choice destination.layout _ = _ at validating
  simp only [EStateM.bind, validating, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

open Lean Elab Tactic in
elab "unfold_pointer_place_lift" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".PointerPlaceMachine.liftResult" then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one pointer-place result lifter"

/-- Form the slice place from the actual fat-pointer representation. The
byte alignment bypasses resolution in the constructor; the reborrow's
later access check remains in TypedRetag. -/
theorem fromFatReference
    (access : ValidityMachine.Access K U) (compiler : PointerPlaceMachine.Compiler K U C)
    (choice : C) (reference slice : LocalLayout) (pointer : Pointer Provenance) (length : UInt64)
    (before : ValidityMachine.State K U)
    (pointee : compiler.builtinDeref choice reference.ty before = .ok (some slice.ty) before)
    (layout : compiler.layoutOf choice slice.ty before = .ok slice before)
    (alignment : slice.layout.align.abi.pow2 = 0) :
    let base := access.runtime.base
    let metadata : Miri.Memory.Scalar Provenance := .fromScalarInt (.ofUInt64 length)
    let value : RvalueImmTy Provenance := ⟨.scalarPair (.fromPointer base pointer) metadata, reference⟩
    PointerPlaceMachine.fromImmediate access compiler choice value before =
      .ok ⟨⟨pointer.withOptionalProvenance, .metadata metadata, none⟩, slice⟩ before := by
  intro base metadata value
  unfold PointerPlaceMachine.fromImmediate
  simp only [value, pointee, layout, Immediate.toScalarAndMeta, bind, Bind.bind, EStateM.bind]
  unfold_pointer_place_lift
  have decoded : (Miri.Memory.Scalar.fromPointer base pointer).toPointer base =
      .ok pointer.withOptionalProvenance := by
    simp [Miri.Memory.Scalar.toPointer, Miri.Memory.Scalar.toBitsOrPtrInternal,
      Miri.Memory.Scalar.fromPointer, bind, Bind.bind, pure, Pure.pure, Except.bind, Except.pure]
  simp only [base] at decoded
  simp [base, decoded, Except.mapError, PointerPlaceMachine.withMetadata, PointerPlaceMachine.misalignment,
    PointerPlaceMachine.misalignmentWith, alignment, bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get]

end DuplicatePrefix.RootMutableReborrow

#print axioms DuplicatePrefix.RootMutableReborrow.selectPolicy
#print axioms DuplicatePrefix.RootMutableReborrow.frozenPermissions
#print axioms DuplicatePrefix.RootMutableReborrow.retagMutablePointer
#print axioms DuplicatePrefix.RootMutableReborrow.writeReference

#print axioms DuplicatePrefix.RootMutableReborrow.fromFatReference

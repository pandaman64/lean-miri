import duplicate_prefix.RootBody
import duplicate_prefix.SourceSteps
import Miri.Interpreter.ExecutionMachine
import Miri.Verification.MutableTypedRetag
import Lean

namespace DuplicatePrefix.RootSharedRef
open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open RetagPolicy

variable {K U C O X Host : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

def policy : NewPermission := ⟨.Frozen, .Cell, .Frozen, none⟩

def initialShared : Tree.LocationState := ⟨.Frozen, true, .Read⟩

theorem initialShared_eq : initialLocationState policy true = .ok initialShared := by rfl

/-- The compiler selects the unprotected shared freeze policy for a
shared reference expression. -/
theorem selectPolicy (hooks : TypedRetag.Hooks K U) (pointee : TyId)
    (state : State)
    (unpin : hooks.isUnpin pointee state = .ok true state)
    (unsafeUnpin : hooks.isUnsafeUnpin pointee state = .ok true state)
    (freeze : hooks.typeIsFreeze pointee state = .ok true state) :
    TypedRetag.newPermission hooks pointee .Shared .Default state =
      .ok (some policy) state := by
  simp [TypedRetag.newPermission, unpin, unsafeUnpin, freeze,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rfl

theorem sharedPermissions (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (before : State)
    (precise : hooks.preciseInteriorMut before = .ok false before)
    (freeze : hooks.typeIsFreeze place.layout.ty before = .ok true before) :
    TypedRetag.insidePermissions hooks budget place size policy before =
      .ok (DedupRangeMap.new size initialShared) before := by
  simp [TypedRetag.insidePermissions, precise, freeze, initialShared_eq, TypedRetag.checked,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

theorem noProtector (location : RetagPipeline.ResolvedLocation) (tag : BorTag) (state : State) :
    Miri.Verification.TypedRetagWP.registerProtector location policy tag state = .ok () state := by rfl

theorem retagSharedPointer [DecidableEq K]
    (hooks : TypedRetag.Hooks K U) (budget : Nat) (value output : RvalueImmTy Provenance)
    (ty pointee : TyId) (before shapeState referenceState placeState retaggedState after : State)
    (place retagged : MPlaceTy Provenance) (tracker : MachineHooks.BorrowState)
    (trackerPresent : before.machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (shape : hooks.typeShape ty before = .ok RetagPipeline.RetagTypeShape.reference shapeState)
    (reference : hooks.referencePointee ty shapeState = .ok (pointee, .Not) referenceState)
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
private def destPlace : Place := ⟨12, #[]⟩

theorem code :
    (do
      let block ← RootBody.reflected.body.body.basicBlocks[2]?
      pure (← block.statements[11]?).kind) =
        some (.Assign destPlace (.Ref .Erased .Shared sourcePlace)) := by
  with_unfolding_all rfl

open Lean Elab Tactic in
elab "unfold_reference_lift" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".ExecutionMachine.lift" then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one execution-machine result lifter"

/-- The emitted shared reference expression evaluates both places,
reconstructs the reference, and writes it with validity in the default mode. -/
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
        borrowTracker := some {tracker with retagMode := .Default}}}
      (ExecutionMachine.rvalueHooks config limits).enforceValidity
        choice destination.layout entered = .ok true entered) :
    let hooks := ExecutionMachine.rvalueHooks config limits
    evalRvalueIntoPlace hooks choice (.Ref .Erased .Shared sourcePlace) destPlace before =
      MachineHooks.withRetagMode .Default (hooks.writeImmediate choice value destination) formed := by
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
  have mode : (BorrowKind.Shared == BorrowKind.Mut .TwoPhaseBorrow) = false := rfl
  change hooks.evalPlace choice destPlace true before = _ at placed
  change hooks.evalPlace choice sourcePlace true prepared = _ at projected
  simp only [evalRvalueIntoPlace, bind, Bind.bind, EStateM.bind, placed, projected, memory, assembled,
    layout, mode, Bool.false_eq_true, ↓reduceIte]
  change MachineHooks.withRetagMode .Default _ formed = _
  unfold MachineHooks.withRetagMode
  rw [tracked]
  dsimp only at validating ⊢
  change hooks.enforceValidity choice destination.layout _ = _ at validating
  simp only [EStateM.bind, validating, Bool.not_true, Bool.false_eq_true, ↓reduceIte]


/-- Step the emitted bb2.11 instruction using the selected place stages
and the stack write. The borrow tracker and all changed memory flow out
of the physical write and the actual retag-mode scope. -/
theorem statement [DecidableEq K]
    (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine afterMachine : MachineHooks.MachineState K U)
    (prepared formed : State) (destination : RuntimePlace Provenance)
    (source : MPlaceTy Provenance) (value : Immediate Provenance)
    (body : frame.body = RootBody.reflected.body.body)
    (beforeLoc : frame.location = .mir ⟨2,11⟩)
    (afterLoc : afterFrame.location = .mir ⟨2,11⟩)
    (placed : (ExecutionMachine.rvalueHooks config limits).evalPlace choice destPlace true
      (Storage.withCurrent frames frame machine) = .ok destination prepared)
    (projected : (ExecutionMachine.rvalueHooks config limits).evalPlace choice sourcePlace true prepared =
      .ok ⟨.memory source.mplace, source.layout⟩ formed)
    (reference : source.mplace.toRef config.access.runtime.base = .ok value)
    (tracker afterTracker : MachineHooks.BorrowState)
    (tracked : formed.machine.borrowTracker = some tracker) (mode : tracker.retagMode = .Default)
    (afterTracked : afterMachine.borrowTracker = some afterTracker)
    (afterMode : afterTracker.retagMode = .Default)
    (validating : (ExecutionMachine.rvalueHooks config limits).enforceValidity choice destination.layout formed =
      .ok true formed)
    (written : (ExecutionMachine.rvalueHooks config limits).writeImmediate choice value destination formed =
      .ok () (Storage.withCurrent frames afterFrame afterMachine)) :
    ExecutionMachine.step config limits choice (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames {afterFrame with location := .mir ⟨2,12⟩} afterMachine, .ok true) := by
  let block := RootBody.reflected.body.body.basicBlocks[2]'(by with_unfolding_all decide +kernel)
  let stmt := block.statements[11]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[2]? = some block := by
    rw [body]
    simp [block]
  have statementAt : block.statements[11]? = some stmt := by simp [stmt]
  have kind : stmt.kind = .Assign destPlace (.Ref .Erased .Shared sourcePlace) := by
    with_unfolding_all rfl
  have beforeMode : {formed with machine := {formed.machine with borrowTracker := some {tracker with retagMode := .Default}}} = formed := by
    have same : {tracker with retagMode := .Default} = tracker := by
      cases tracker
      cases mode
      rfl
    rw [same, ← tracked]
  have afterModeEq : {afterTracker with retagMode := .Default} = afterTracker := by
    cases afterTracker
    cases afterMode
    rfl
  have effect := writeReference config limits choice (Storage.withCurrent frames frame machine)
    prepared formed destination source value placed projected reference tracker tracked
      (by simpa only [beforeMode] using validating)
  have scope : MachineHooks.withRetagMode .Default
      ((ExecutionMachine.rvalueHooks config limits).writeImmediate choice value destination) formed =
        .ok () (Storage.withCurrent frames afterFrame afterMachine) := by
    unfold MachineHooks.withRetagMode
    rw [tracked]
    dsimp only
    rw [beforeMode, written]
    simp only [Storage.withCurrent, afterTracked, mode, afterModeEq]
    rw [← afterTracked]
  exact SourceSteps.assign_exact config limits choice frames frame afterFrame machine afterMachine
    ⟨2,11⟩ block stmt destPlace (.Ref .Erased .Shared sourcePlace) beforeLoc blockAt statementAt kind
    (effect.trans scope) afterLoc

#print axioms statement
#print axioms selectPolicy
#print axioms retagSharedPointer
#print axioms code
#print axioms writeReference
end DuplicatePrefix.RootSharedRef

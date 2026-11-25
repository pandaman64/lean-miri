import Lean
import Miri.Verification.PointerFormationWP

namespace MiriTests.Verification.PointerFormationWP

open Lean Elab Tactic Meta
open Miri.ABI Miri.Interpreter Miri.MIR Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.RetagPolicy Miri.Verification RvalueWP PointerFormationWP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Value" => RvalueImmTy Provenance

/-- In a raw formation, a raw type query keeps the input value and the
original retag mode. The query is run with Raw mode installed. -/
example (hooks : TypedRetag.Hooks K U) (value : Value) (budget : Nat)
    (before : State) (tracker : MachineHooks.BorrowState)
    (tracked : before.machine.borrowTracker = some tracker)
    (query : hooks.typeShape value.layout.ty = pure RetagPipeline.RetagTypeShape.rawPointer)
    (post : Value → State → Prop) (failure : StepError → State → Prop) :
    actionPre (MachineHooks.withRetagMode .Raw do
      return (← TypedRetag.machineRetagPtrValue hooks budget value value.layout.ty).getD value)
      post failure before = post value before := by
  rw [actionPre_withRetagMode]
  simp only [retagModePre, retagModePullback, tracked, actionPre_bind,
    actionPre_machineRetagPtrValue, pointerRetagPre, query, actionPre_pure]
  change post value {before with machine.borrowTracker := some tracker} = _
  rw [← tracked]

/-- A type query failure is reported with its retained machine state.
Restoring the mode does not undo earlier machine changes from the query. -/
example (hooks : TypedRetag.Hooks K U) (value : Value) (budget : Nat)
    (before failed : State) (tracker retained : MachineHooks.BorrowState)
    (tracked : before.machine.borrowTracker = some tracker)
    (error : StepError)
    (query : hooks.typeShape value.layout.ty
      {before with machine.borrowTracker := some {tracker with retagMode := .Raw}} =
        .error error failed)
    (trackedAfter : failed.machine.borrowTracker = some retained)
    (post : Value → State → Prop) (failure : StepError → State → Prop) :
    actionPre (MachineHooks.withRetagMode .Raw do
      return (← TypedRetag.machineRetagPtrValue hooks budget value value.layout.ty).getD value)
      post failure before =
      failure error {failed with machine.borrowTracker := some {retained with retagMode := tracker.retagMode}} := by
  rw [actionPre_withRetagMode]
  simp only [retagModePre, retagModePullback, tracked, actionPre_bind,
    actionPre_machineRetagPtrValue, pointerRetagPre]
  simp only [actionPre, query]
  change (match failed.machine.borrowTracker with
    | none => failure (.invalidProgram "borrow tracker removed during retag mode scope") failed
    | some current => failure error {failed with machine.borrowTracker := some {current with retagMode := tracker.retagMode}}) = _
  rw [trackedAfter]

/-- The shared and mutable frozen reference policies are unprotected and
initialize byte permissions differently. -/
example :
    match create ⟨true, true, true⟩ .Shared .Default ⟨false, false⟩,
        create ⟨true, true, true⟩ .Mutable .Default ⟨false, false⟩ with
    | some shared, some exclusive =>
      shared.freezePermission = .Frozen ∧ exclusive.freezePermission = .ReservedFrz false ∧
        shared.protector = none ∧ exclusive.protector = none
    | _, _ => False := by
  exact ⟨rfl, rfl, rfl, rfl⟩

local elab "guard_pointer_retag" : tactic => do
  let target ← getMainTarget
  unless (target.find? (·.isConstOf ``pointerRetagPre)).isSome do
    throwError "normalized pointer assignment did not reach typed pointer retag"

/-- An actual MIR assignment reaches the scoped typed pointer precondition
through the registered normalization rules. -/
example (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (source dest : LocalId) (borrow : BorrowKind) (post : State → Prop) (failure : StepError → State → Prop)
    (before : State) :
    let pre := evalPre (ExecutionMachine.rvalueHooks config limits) choice
      (.Ref .Erased borrow ⟨source, #[]⟩) ⟨dest, #[]⟩ post failure before
    pre → pre := by
  dsimp only
  intro h
  simp only [miri_initial_wp] at h ⊢
  guard_pointer_retag
  exact h

example (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (source dest : LocalId) (post : State → Prop) (failure : StepError → State → Prop)
    (before : State) :
    let pre := evalPre (ExecutionMachine.rvalueHooks config limits) choice
      (.RawPtr .Const ⟨source, #[]⟩) ⟨dest, #[]⟩ post failure before
    pre → pre := by
  dsimp only
  intro h
  simp only [miri_initial_wp] at h ⊢
  guard_pointer_retag
  exact h

#print axioms evalPre_ref
#print axioms evalPre_rawPtr
#print axioms actionPre_rawAdjustment
#print axioms actionPre_machineRetagPtrValue
#print axioms actionPre_retagPlace
#print axioms production_reconstruct

end MiriTests.Verification.PointerFormationWP

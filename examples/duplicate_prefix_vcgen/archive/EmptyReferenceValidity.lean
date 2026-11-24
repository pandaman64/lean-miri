import duplicate_prefix.ReferenceVisitorFields
import duplicate_prefix.EmptyReferenceSteps
import duplicate_prefix.RootFatRawPointerValidity

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyReferenceValidity
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows

/-- Read-only provider identities used by the shallow empty-reference visitor. -/
structure VisitorFields {K U C F A : Type} [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (choice : C) (budget : Nat) : Prop where
  toOp : hooks.toOp = fun c place => placeToOp (ValidityMachine.placeHooks access allocation compiler) c place
  ghost : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
    @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance)
  read : hooks.readImmediate = fun c place expected => do
    let op ← placeToOp (ValidityMachine.placeHooks access allocation compiler) c place
    ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected
  write : hooks.writeNoValidate = fun c value destination => do
    let validate ← ValidityMachine.enforceValidity
    ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation compiler) c (fun _ => validate) value destination
  check : hooks.checkPointerAccess = fun _ => ValidityMachine.checkPointerAccessResult access
  align : hooks.checkPointerAlignResult = fun _ => ValidityMachine.checkPointerAlignResult access
  nonnull : hooks.scalarMayBeNull = fun _ => ValidityMachine.scalarMayBeNull
  retagAction : hooks.retagPointer choice = TypedRetag.machineRetagPtrValue retag budget
  sizing : hooks.sizeAndAlign choice = retag.sizeAndAlign

/-- Retagging a zero-width no-provenance place preserves the pointer and advances the tag supply. -/
theorem no_provenance_zero_retag_place_at {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (align : Align)
    (before : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (noProv : place.mplace.ptr.provenance = none)
    (sizing : h.sizeAndAlign place before = .ok (some (Size.ZERO, align)) before)
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok none (TypedRetagEmpty.afterTag before tracker fresh)) :
    TypedRetag.retagPlace h budget place policy before =
      .ok place (TypedRetagEmpty.afterTag before tracker fresh) := by
  unfold TypedRetag.retagPlace
  simp only [bind, EStateM.bind]
  rw [sizing]
  simp only [pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [noProv, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← noProv]

#print axioms no_provenance_zero_retag_place_at
end DuplicatePrefix.EmptyReferenceValidity

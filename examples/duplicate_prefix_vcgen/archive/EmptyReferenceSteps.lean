import duplicate_prefix.TypedRetagFields
import duplicate_prefix.Storage

namespace DuplicatePrefix.EmptyReferenceSteps
open Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Input Miri.Interpreter
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem reference_pointer_of_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (value output : RvalueImmTy Provenance)
    (place changed : MPlaceTy Provenance) (pointee : TyId) (mutability : Miri.MIR.Mutability)
    (mode : RetagPolicy.RetagMode) (policy : RetagPolicy.NewPermission)
    (before after : MachineHooks.State K U)
    (shape : h.typeShape value.layout.ty = pure .reference)
    (pointeeQuery : h.referencePointee value.layout.ty = pure (pointee, mutability))
    (permission : TypedRetag.newPermission h pointee
      (if mutability == .Mut then .Mutable else .Shared) mode before = .ok (some policy) before)
    (construct : h.immPtrToMPlace value = pure place)
    (retag : TypedRetag.retagPlace h budget place policy before = .ok changed after)
    (reconstruct : h.reconstruct value changed = pure output) :
    TypedRetag.retagPtrValue h budget value value.layout.ty mode before = .ok (some output) after := by
  unfold TypedRetag.retagPtrValue
  simp only [shape, pointeeQuery, RetagPipeline.RetagTypeShape.reference,
    RetagPipeline.RetagTypeShape.classify, Bool.false_eq_true, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure, permission, construct, retag, reconstruct]

#print axioms reference_pointer_of_steps
/-- Zero-length integer provenance never allocates a tree child or protector. -/
theorem no_provenance_zero_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (state : MachineHooks.State K U)
    (noProv : place.mplace.ptr.provenance = none)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state)
    (resolve : h.resolveAllocation place.mplace.ptr state = .ok none state)
    (log : h.logCreation place Size.ZERO policy tag none = pure ()) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state = .ok none state := by
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  simp [Size.ZERO, noProv, bind, EStateM.bind, pure, EStateM.pure]

theorem no_provenance_zero_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (policy : RetagPolicy.NewPermission)
    (tag : BorTag) (state : ValidityMachine.State K U)
    (noProv : place.mplace.ptr.provenance = none) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state = .ok none state := by
  apply no_provenance_zero_reborrow
  · exact noProv
  · rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
  · rw [sources.resolve]
    exact RetagPointerChecks.resolve_allocation_none pointers place.mplace.ptr state noProv
  · rw [sources.log]

/-- The real zero-sized no-provenance retag preserves the pointer and consumes one tag. -/
theorem no_provenance_zero_retag_place {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (align : Align)
    (before : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (noProv : place.mplace.ptr.provenance = none)
    (sizing : h.sizeAndAlign place = pure (some (Size.ZERO, align)))
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok none (TypedRetagEmpty.afterTag before tracker fresh)) :
    TypedRetag.retagPlace h budget place policy before =
      .ok place (TypedRetagEmpty.afterTag before tracker fresh) := by
  unfold TypedRetag.retagPlace
  simp only [sizing, bind, EStateM.bind, pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [noProv, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← noProv]

#print axioms no_provenance_zero_from_fields
#print axioms no_provenance_zero_retag_place

end DuplicatePrefix.EmptyReferenceSteps

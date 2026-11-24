import duplicate_prefix.EmptyReferenceAllocation
import duplicate_prefix.EmptyReferenceValidity
import duplicate_prefix.EmptyReferenceSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyIntegerBorrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open EmptyReferenceAllocation

theorem no_provenance_zero_pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (reference pointee : LocalLayout) (address : UInt64)
    (mutability : Miri.MIR.Mutability) (retagMode : RetagPolicy.RetagMode) (policy : RetagPolicy.NewPermission)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (pointee.ty,mutability))
    (unpin : h.isUnpin pointee.ty = pure true) (unsafeUnpin : h.isUnsafeUnpin pointee.ty = pure true)
    (frozen : h.typeIsFreeze pointee.ty = pure true)
    (created : RetagPolicy.create ⟨true,true,true⟩ (if mutability == .Mut then .Mutable else .Shared)
      retagMode ⟨false,false⟩ = some policy)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (width : access.runtime.base.pointerWidth = .w64)
    (state : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (frameShape : state.stack.frames = frames.push frame)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (modeEq : tracker.retagMode = retagMode)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (sizingAt : h.sizeAndAlign (RetagReferencePlace.integerSlicePlace address 0 pointee) state =
      .ok (some (Size.ZERO, Align.ONE)) state)
    (definitionReady : retagMode = .FnEntry → ∃ definition, h.instanceDefinition frame.functionInstance = pure definition := by
      first | assumption | (intro _; assumption) | exact ⟨_, by with_unfolding_all rfl⟩) :
    TypedRetag.machineRetagPtrValue h budget (RetagReferencePlace.integerSliceValue address 0 reference)
      reference.ty state = .ok (some (RetagReferencePlace.integerSliceValue address 0 reference))
        (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  let place := RetagReferencePlace.integerSlicePlace address 0 pointee
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact RetagReferencePlace.canonical_from_integer access prepared choice address 0 reference pointee
      dereference pointeeLayout pointeeAlign width
  have reborrow := EmptyReferenceSteps.no_provenance_zero_from_fields h prepared access projection vtable
    pointers choice sources budget place policy tracker.global.nextPointerTag
    (TypedRetagEmpty.afterTag state tracker fresh) rfl
  have retag := EmptyReferenceValidity.no_provenance_zero_retag_place_at h budget place policy
    Align.ONE state tracker enabled fresh rfl sizingAt reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h pointee.ty
    (if mutability == .Mut then .Mutable else .Shared) retagMode state frames frame frameShape
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have reconstruct : h.reconstruct value place = pure value := by
    rw [sources.reconstruct]
    funext after
    simp [TypedMachineBindings.retagHooks, value, place, RetagReferencePlace.integerSlicePlace,
      RetagReferencePlace.integerSliceValue, MemPlace.toRef, Immediate.newPointerWithMeta,
      RetagReferencePlace.integer_from_pointer access.runtime.base address width,
      Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]
  have result := EmptyReferenceSteps.reference_pointer_of_steps h budget value value place place pointee.ty mutability
    retagMode policy state (TypedRetagEmpty.afterTag state tracker fresh)
    shape pointeeQuery permission construct retag reconstruct
  unfold TypedRetag.machineRetagPtrValue
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled, modeEq]
  exact result

end DuplicatePrefix.EmptyIntegerBorrow

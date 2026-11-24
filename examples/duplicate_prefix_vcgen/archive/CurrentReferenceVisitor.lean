import duplicate_prefix.ReferenceValidity

namespace DuplicatePrefix.CurrentReferenceVisitor
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ReferenceValidity
set_option maxHeartbeats 4000000

abbrev ghost {K U : Type} (state : ValidityMachine.State K U) (enabled : Bool) :
    ValidityMachine.State K U :=
  {state with machine := {state.machine with user :=
    {state.machine.user with payload := {state.machine.user.payload with ghost := enabled}}}}

theorem shallow {K U C F A : Type}
    (h : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C
      MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (choice : C) (fuel : Nat) (name : String) (mutable : Bool)
    (destination : RuntimePlace Provenance) (input adjusted : RvalueImmTy Provenance)
    (place : MPlaceTy Provenance) (size : Size) (align : Align)
    (scalar : Miri.Memory.Scalar Provenance)
    (state afterRetag afterWrite : ValidityMachine.State K U)
    (initialGhost : state.machine.user.payload.ghost = false)
    (writtenGhost : afterWrite.machine.user.payload.ghost = true)
    (named : h.typeName choice destination.layout.ty = pure name)
    (classified : h.classify choice destination.layout.ty = pure (.reference mutable))
    (ghostField : h.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance))
    (toOp : h.toOp choice destination (ghost state true) =
      .ok ⟨.immediate input.imm, destination.layout⟩ (ghost state true))
    (read : h.readImmediate choice destination .reference (ghost state true) =
      .ok input (ghost state true))
    (construct : h.ptrToPlace choice input = pure place)
    (unsized : place.layout.layout.isSized = false)
    (metadata : source_check_metadata h choice place = pure ())
    (dynamic : h.sizeAndAlign choice place (ghost state true) =
      .ok (some (size, align)) (ghost state true))
    (checked : h.checkPointerAccess choice place.mplace.ptr size (ghost state true) =
      .ok (.ok ()) (ghost state true))
    (retag : h.retagPointer choice input destination.layout.ty (ghost state true) =
      .ok (some adjusted) afterRetag)
    (write : h.writeNoValidate choice adjusted.imm destination afterRetag = .ok () afterWrite)
    (encoded : Scalar.fromMaybePointer h.target.base place.mplace.ptr = .ok scalar)
    (nonnull : h.scalarMayBeNull choice scalar = pure false)
    (inhabited : h.opsemInhabited choice place.layout.ty = pure true)
    (aligned : h.checkPointerAlignResult choice place.mplace.ptr align afterWrite =
      .ok (.ok ()) afterWrite) :
    ValidityVisitor.validatePlace h choice (fuel + 1) destination false true state =
      .ok () (ghost afterWrite false) := by
  have checkedReference := check_reference_stage_for h choice name mutable destination
    input adjusted place size align scalar (ghost state true) afterRetag afterWrite
    read construct unsized metadata dynamic checked retag write encoded nonnull inhabited aligned
  have visited := visit_reference_of_check_for h choice fuel name mutable destination
    (ghost state true) afterWrite classified checkedReference
  exact validate_reference_shallow_of_visit h choice fuel name destination state afterWrite
    input.imm initialGhost writtenGhost named ghostField toOp visited

theorem runtimeShallow {K U C F A : Type} [DecidableEq K]
    (h : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C
      MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (choice : C) (fuel : Nat) (destination : RuntimePlace Provenance)
    (state after : ValidityMachine.State K U)
    (mode : state.machine.user.payload.validation = .Shallow)
    (validated : ValidityVisitor.validatePlace h choice fuel destination false true state = .ok () after) :
    ValidityMachine.validateRuntime h choice fuel destination true state = .ok () after := by
  simp only [ValidityMachine.validateRuntime, ValidityMachine.enforceValidityRecursively,
    mode, show (ValidityMachine.ValidationMode.Shallow == .Deep) = false from rfl,
    bind, Bind.bind, pure, Pure.pure, get, getThe, MonadStateOf.get, EStateM.get,
    EStateM.bind, EStateM.pure]
  exact validated

end DuplicatePrefix.CurrentReferenceVisitor

#print axioms DuplicatePrefix.CurrentReferenceVisitor.shallow
#print axioms DuplicatePrefix.CurrentReferenceVisitor.runtimeShallow

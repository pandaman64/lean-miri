import Miri.Verification.CanonicalStepWP
import Miri.Verification.MemoryWP

/-! Exact continuations for a selected MIR discriminant write. -/
namespace Miri.Verification.DiscriminantWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Std.WP
open RvalueWP

variable {P S C V : Type} [PointerProvenance P]

/-- Convert the compiler's discriminant value to the discriminant layout width. -/
def discriminantScalar (layout : TyAndLayout TyId) (variant : Nat)
    (value : Option (TyId × U128)) : Except StepError (RvalueImmTy P) := do
  let bits ← match value with
    | some (ty, bits) =>
      if ty != layout.ty then .error (.invalidProgram "discriminant type disagrees with layout")
      else .ok bits
    | none =>
      if variant != 0 then .error (.invalidProgram "non-enum discriminant variant must be zero")
      else .ok 0
  let scalar ← Scalar.fromUInt bits layout.layout.size |>.mapError ScalarOps.scalarError
  return ⟨.scalar scalar, layout⟩

/-- Direct tags use the low bits of the compiler discriminant at tag width. -/
def directTag (target : RuntimeTargetDataLayout) (tag : ABI.Scalar) (field : Nat)
    (discr : RvalueImmTy P) : Except StepError (Option (ScalarInt × Nat)) := do
  let scalar ← discr.imm.toScalar |>.mapError ScalarOps.immediateError
  let bits ← scalar.toBits discr.layout.layout.size |>.mapError ScalarOps.scalarError
  let size ← tag.size target |>.mapError (fun error => .invalidProgram s!"tag scalar size: {repr error}")
  let bits ← size.truncate bits |>.mapError (fun error => .invalidProgram (toString error))
  let scalar ← Scalar.fromUInt (Prov := P) bits size |>.mapError ScalarOps.scalarError
  let value ← scalar.toScalarInt |>.mapError ScalarOps.scalarError
  return some (value, field)

/-- A niche tag uses wrapping addition after validating both operands at tag width. -/
def nicheTag (P : Type) [PointerProvenance P] (size : Size) (field variant start : Nat)
    (nicheStart : U128) : Except StepError (Option (ScalarInt × Nat)) := do
  let _ ← Scalar.fromUInt (Prov := P) nicheStart size |>.mapError ScalarOps.scalarError
  let relative := BitVec.ofNat 128 (variant - start)
  let _ ← Scalar.fromUInt (Prov := P) relative size |>.mapError ScalarOps.scalarError
  let bits ← size.truncate (relative + nicheStart) |>.mapError (fun error => .invalidProgram (toString error))
  let scalar ← Scalar.fromUInt (Prov := P) bits size |>.mapError ScalarOps.scalarError
  let value ← scalar.toScalarInt |>.mapError ScalarOps.scalarError
  return some (value, field)

omit [PointerProvenance P] in
@[miri_rvalue] theorem actionPre_discriminantForVariant (hooks : DiscriminantHooks P S C V)
    (choice : C) (ty : TyId) (variant : Nat)
    (post : RvalueImmTy P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (Discriminant.discriminantForVariant hooks choice ty variant) post onError =
      actionPre (hooks.discriminantLayout choice ty) (fun layout =>
        actionPre (hooks.discriminantValue choice ty variant) (fun value =>
          scalarCheckPre (discriminantScalar layout variant value) post onError) onError) onError := by
  simp only [Discriminant.discriminantForVariant, actionPre_bind_fun]
  congr 1
  funext layout
  congr 1
  funext value state
  cases value with
  | none =>
    by_cases different : variant = 0
    · cases encoded : Scalar.fromUInt (Prov := P) 0#128 layout.layout.size <;>
        simp [discriminantScalar, different, actionPre, scalarCheckPre, bind, Bind.bind,
          EStateM.bind, pure, Pure.pure, EStateM.pure, Except.bind, encoded] <;> rfl
    · simp [discriminantScalar, different, actionPre, scalarCheckPre, bind, Bind.bind,
        EStateM.bind] <;> rfl
  | some value =>
    obtain ⟨ty, bits⟩ := value
    by_cases different : ty = layout.ty
    · cases encoded : Scalar.fromUInt (Prov := P) bits layout.layout.size <;>
        simp [discriminantScalar, different, actionPre, scalarCheckPre, bind, Bind.bind,
          EStateM.bind, pure, Pure.pure, EStateM.pure, Except.bind, encoded] <;> rfl
    · simp [discriminantScalar, different, actionPre, scalarCheckPre, bind, Bind.bind,
        EStateM.bind] <;> rfl

/-- Tag selection dispatches on the destination layout before issuing compiler queries. -/
@[miri_rvalue] def tagPre (hooks : DiscriminantHooks P S C V) (choice : C)
    (layout : TyAndLayout TyId) (variant : Nat)
    (post : Option (ScalarInt × Nat) → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  if layout.layout.isVariantUninhabited variant then
    onError (.undefinedBehavior s!"UninhabitedEnumVariantWritten({variant})")
  else
    match layout.layout.variants with
    | .Empty => onError (.invalidProgram "inhabited empty layout")
    | .Single _ => post none
    | .Multiple tag .Direct field _ =>
      actionPre (Discriminant.discriminantForVariant hooks choice layout.ty variant) (fun discr =>
        scalarCheckPre (directTag hooks.runtimeTarget tag field discr) post onError) onError
    | .Multiple tag (.Niche untagged start last nicheStart) field _ =>
      if variant == untagged then post none
      else if variant < start || variant > last then onError (.invalidProgram "variant outside niche range")
      else if variant >= 2^32 || start >= 2^32 || last >= 2^32 then
        onError (.invalidProgram "variant index exceeds u32")
      else actionPre (hooks.tagLayout choice tag) (fun tagLayout =>
        scalarCheckPre (nicheTag P tagLayout.layout.size field variant start nicheStart) post onError) onError

private theorem actionPre_liftResult_bind {A B : Type} (result : Except StepError A)
    (next : A → RvalueM S B) (post : B → S → Prop) (onError : StepError → S → Prop) :
    actionPre (Discriminant.liftResult result >>= next) post onError =
      scalarCheckPre result (fun value => actionPre (next value) post onError) onError := by
  funext before
  cases result <;> rfl

private theorem actionPre_liftResult {A : Type} (result : Except StepError A)
    (post : A → S → Prop) (onError : StepError → S → Prop) :
    actionPre (Discriminant.liftResult result) post onError = scalarCheckPre result post onError := by
  cases result <;> rfl

private theorem actionPre_pure_fun {A : Type} (value : A) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (pure value) post onError = post value := rfl

private theorem scalarCheckPre_bind {A B : Type} (result : Except StepError A)
    (next : A → Except StepError B) (post : B → S → Prop) (onError : StepError → S → Prop) :
    scalarCheckPre (result >>= next) post onError =
      scalarCheckPre result (fun value => scalarCheckPre (next value) post onError) onError := by
  cases result <;> rfl

private theorem scalarCheckPre_pure {A : Type} (value : A) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    scalarCheckPre (pure value) post onError = post value := rfl

omit [PointerProvenance P] in
private theorem tagSize_eq (hooks : DiscriminantHooks P S C V) (tag : ABI.Scalar) :
    Discriminant.tagSize hooks tag =
      Discriminant.liftResult ((tag.size hooks.runtimeTarget).mapError
        (fun error => .invalidProgram s!"tag scalar size: {repr error}")) := by
  unfold Discriminant.tagSize
  cases tag.size hooks.runtimeTarget <;> rfl

@[miri_rvalue] theorem actionPre_tagForVariant (hooks : DiscriminantHooks P S C V) (choice : C)
    (layout : TyAndLayout TyId) (variant : Nat)
    (post : Option (ScalarInt × Nat) → S → Prop) (onError : StepError → S → Prop) :
    actionPre (Discriminant.tagForVariant hooks choice layout variant) post onError =
      tagPre hooks choice layout variant post onError := by
  by_cases dead : layout.layout.isVariantUninhabited variant = true
  · simp [Discriminant.tagForVariant, tagPre, dead]
    rfl
  · simp only [Discriminant.tagForVariant, tagPre, dead, Bool.false_eq_true, ↓reduceIte]
    cases variants : layout.layout.variants with
    | Empty => rfl
    | Single => rfl
    | Multiple tag encoding field layouts =>
      cases encoding with
      | Direct =>
        rw [actionPre_bind_fun]
        congr 1
        funext discr
        simp only [directTag, Discriminant.scalarOf, Discriminant.scalarBits, tagSize_eq,
          Discriminant.sizeResult, actionPre_liftResult_bind, scalarCheckPre_bind,
          actionPre_pure_fun, scalarCheckPre_pure]
      | Niche untagged start last nicheStart =>
        by_cases implicit : (variant == untagged) = true
        · simp [implicit]
          rfl
        · simp only [implicit, Bool.false_eq_true, ↓reduceIte]
          by_cases outside : (decide (variant < start) || decide (variant > last)) = true
          · simp only [outside, ↓reduceIte]
            rfl
          · simp only [outside, Bool.false_eq_true, ↓reduceIte]
            by_cases large : (decide (variant ≥ 2 ^ 32) ||
                decide (start ≥ 2 ^ 32) || decide (last ≥ 2 ^ 32)) = true
            · simp only [large, ↓reduceIte]
              rfl
            · simp only [large, Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun]
              congr 1
              funext tagLayout
              simp only [nicheTag, Discriminant.sizeResult, actionPre_liftResult,
                scalarCheckPre_bind, actionPre_pure_fun, scalarCheckPre_pure]

/-- Readback queries the discriminant type before inspecting the operand's
layout. A tagged layout projects and reads the existing tag before decoding it. -/
@[miri_rvalue] theorem actionPre_readDiscriminant (hooks : DiscriminantHooks P S C V)
    (choice : C) (operand : OpTy P) (post : Nat → S → Prop) (onError : StepError → S → Prop) :
    actionPre (Discriminant.readDiscriminant hooks choice operand) post onError =
      actionPre (hooks.discriminantLayout choice operand.layout.ty) (fun discrLayout =>
        match operand.layout.layout.variants with
        | .Empty => onError (.undefinedBehavior "UninhabitedEnumVariantRead(None)")
        | .Single index =>
          if operand.layout.layout.isUninhabited then
            onError (.undefinedBehavior s!"UninhabitedEnumVariantRead({index})")
          else post index
        | .Multiple tag encoding field _ =>
          actionPre (hooks.tagLayout choice tag) (fun tagLayout =>
            actionPre (hooks.projectRead choice operand field) (fun tagOp =>
              actionPre (hooks.readImmediate choice tagOp) (fun value =>
                actionPre (Discriminant.readTag hooks choice operand discrLayout tagLayout
                  tag encoding value) post onError) onError) onError) onError) onError := by
  simp only [Discriminant.readDiscriminant, actionPre_bind_fun]
  congr 1
  funext discrLayout
  cases operand.layout.layout.variants with
  | Empty => rfl
  | Single index =>
    by_cases dead : operand.layout.layout.isUninhabited = true <;> simp [dead] <;> rfl
  | Multiple => simp only [actionPre_bind_fun]

/-- A tagged variant projects and writes its tag. An implicit variant reads
back the destination and succeeds exactly when it already encodes that variant. -/
@[miri_rvalue] def writePre (hooks : DiscriminantHooks P S C V) (choice : C)
    (variant : Nat) (dest : V) (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  tagPre hooks choice (hooks.destLayout dest) variant (fun result =>
    match result with
    | some (tag, field) =>
      actionPre (hooks.projectWrite choice dest field)
        (fun tagDest => actionPre (hooks.writeScalar choice (.fromScalarInt tag) tagDest) post onError) onError
    | none =>
      actionPre (hooks.toOp choice dest) (fun operand =>
        actionPre (Discriminant.readDiscriminant hooks choice operand) (fun actual =>
          if actual != variant then onError (.undefinedBehavior "InvalidNichedEnumVariantWritten")
          else post ()) onError) onError) onError

@[miri_rvalue] theorem actionPre_writeDiscriminant (hooks : DiscriminantHooks P S C V) (choice : C)
    (variant : Nat) (dest : V) (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    actionPre (Discriminant.writeDiscriminant hooks choice variant dest) post onError =
      writePre hooks choice variant dest post onError := by
  simp only [Discriminant.writeDiscriminant, writePre, actionPre_bind_fun, actionPre_tagForVariant]
  congr 1
  funext result
  cases result with
  | some value =>
    obtain ⟨tag, field⟩ := value
    simp only [actionPre_bind_fun]
  | none =>
    simp only [actionPre_bind_fun]
    congr 1
    funext operand
    congr 1
    funext actual before
    by_cases same : actual = variant <;>
      simp [same, actionPre] <;> rfl

omit [PointerProvenance P] in
/-- A successful tag write runs the destination's validity check in the
state left by the write. The selected destination can be an immediate local
or an allocation-backed place. -/
@[miri_rvalue] theorem actionPre_writePlaceScalar {E : Type} (hooks : PlaceHooks P S C E)
    (choice : C) (scalar : Scalar P) (dest : RuntimePlace P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    actionPre (writePlaceImmediate hooks choice (.scalar scalar) dest) post onError =
      if !dest.layout.layout.isSized then onError (.invalidProgram "unsized immediate destination")
      else
        actionPre (asMplaceOrMutableLocal hooks choice dest) (fun target =>
          let validate := actionPre (hooks.enforceValidity choice dest.layout) (fun enforce =>
            if enforce then actionPre (hooks.validate choice dest) post onError else post ()) onError
          match target with
          | .memory place =>
            actionPre (hooks.writeMemoryNoValidate choice (.scalar scalar) place)
              (fun _ => validate) onError
          | .immediateLocal id layout =>
            actionPre (hooks.writeLocalImmediate choice id layout (.scalar scalar))
              (fun _ => validate) onError) onError := by
  by_cases sized : dest.layout.layout.isSized = true
  · simp only [writePlaceImmediate, writePlaceImmediateNoValidate, sized, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun]
    congr 1
    funext target
    cases target <;>
      congr 1 <;> funext _ <;> congr 1 <;> funext enforce <;> cases enforce <;> rfl
  · simp [writePlaceImmediate, writePlaceImmediateNoValidate, sized]
    rfl

omit [PointerProvenance P] in
/-- An already projected memory place keeps the destination allocation and
layout from the projection. -/
@[miri_rvalue] theorem actionPre_asMplace_memory {E : Type} (hooks : PlaceHooks P S C E)
    (choice : C) (dest : RuntimePlace P) (memory : MemPlace P)
    (post : MutablePlace P → S → Prop) (onError : StepError → S → Prop)
    (target : dest.ref = .memory memory) :
    actionPre (asMplaceOrMutableLocal hooks choice dest) post onError =
      post (.memory ⟨memory, dest.layout⟩) := by
  simp only [asMplaceOrMutableLocal, target, actionPre_pure_fun]

section Memory

variable {K U : Type} [DecidableEq K]

@[miri_rvalue] theorem actionPre_readImmediate (access : PlaceMachine.AccessConfig K U)
    (operand : OpTy Provenance) (post : RvalueImmTy Provenance → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) :
    actionPre (PlaceMachine.readImmediate access operand) post onError before =
      MemoryWP.immediateReadPre access operand before post onError := by
  rw [actionPre_eq_wp]
  exact propext (MemoryWP.immediateReadPre_iff access operand before post onError).symm

@[miri_rvalue] theorem actionPre_writeMemoryScalar (access : PlaceMachine.AccessConfig K U)
    (later : MemoryOperandLayout → Bool) (scalar : Scalar Provenance) (place : MPlaceTy Provenance)
    (post : Unit → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) :
    actionPre (PlaceMachine.writeMemory access later (.scalar scalar) place) post onError before =
      MemoryWP.immediateWritePre access later (.scalar scalar) place before post onError := by
  rw [actionPre_eq_wp]
  exact propext (MemoryWP.immediateWritePre_iff access later (.scalar scalar)
    place before post onError).symm

/-- The source-owned memory hook samples ghost scope and validity policy
from the state at the tag write. -/
@[miri_rvalue] theorem actionPre_scopedWriteMemoryScalar
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C) (scalar : Scalar Provenance)
    (place : MPlaceTy Provenance) (post : Unit → ValidityMachine.State K U → Prop)
    (onError : StepError → ValidityMachine.State K U → Prop) (before : ValidityMachine.State K U) :
    actionPre ((ValidityMachine.placeHooks access allocation compiler).writeMemoryNoValidate choice
      (.scalar scalar) place) post onError before =
      MemoryWP.immediateWritePre { access with ghostMode := before.machine.user.payload.ghost }
        (fun _ => before.machine.user.payload.validation != .No)
        (.scalar scalar) place before post onError := by
  change actionPre (PlaceMachine.writeMemory {access with ghostMode := before.machine.user.payload.ghost}
    (fun _ => before.machine.user.payload.validation != .No) (.scalar scalar) place)
    post onError before = _
  exact actionPre_writeMemoryScalar _ _ _ _ _ _ _

end Memory

section Canonical
variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U
local notation "Errors" => StepError → State → Prop
local notation "Hooks" => ExecutionMachine.discriminantHooks

@[miri_rvalue high] theorem statementPre_setDiscriminant (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (place : Place) (variant : Nat) (post : Bool → State → Prop)
    (onError : Errors) (before : State) :
    CanonicalStepWP.statementPre config limits choice (.SetDiscriminant place variant) post onError before =
      let checked := ExecutionMachine.withValidation config limits
      actionPre (PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks checked) choice place false)
        (fun dest => writePre (Hooks checked) choice variant dest
          (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError)
          onError) onError before := by
  simp only [CanonicalStepWP.statementPre, ← actionPre_eq_wp, actionPre_writeDiscriminant]

omit [DecidableEq K] in
/-- The same selected rewrite also applies after the generic statement
precondition has already unfolded. -/
@[miri_rvalue] theorem wp_project_writeDiscriminant
    (projection : PlaceProjectionHooks Provenance State C MachineHooks.FrameExtra)
    (hooks : DiscriminantHooks Provenance State C (RuntimePlace Provenance))
    (choice : C) (place : Place) (variant : Nat) (post : Unit → State → Prop)
    (onError : Errors) (before : State) :
    wp (PlaceDynamic.evalPlace projection choice place false) (fun dest =>
      wp (Discriminant.writeDiscriminant hooks choice variant dest) post onError) onError before =
      actionPre (PlaceDynamic.evalPlace projection choice place false) (fun dest =>
        writePre hooks choice variant dest post onError) onError before := by
  simp only [← actionPre_eq_wp, actionPre_writeDiscriminant]

@[miri_rvalue] theorem canonical_destLayout (config : Config) (dest : RuntimePlace Provenance) :
    (Hooks config).destLayout dest = dest.layout := rfl

@[miri_rvalue] theorem canonical_projectWrite (config : Config) (choice : C)
    (dest : RuntimePlace Provenance) (field : Nat) :
    (Hooks config).projectWrite choice dest field =
      PlaceDynamic.field (ExecutionMachine.projectionHooks config) choice dest field := rfl

@[miri_rvalue] theorem canonical_toOp (config : Config) (choice : C) (dest : RuntimePlace Provenance) :
    (Hooks config).toOp choice dest =
      placeToOp (ExecutionMachine.projectionHooks config).place choice dest := rfl

@[miri_rvalue] theorem canonical_projectRead (config : Config) (choice : C)
    (operand : OpTy Provenance) (field : Nat) :
    (Hooks config).projectRead choice operand field =
      OperandMachine.field (ExecutionMachine.operandHooks config) choice operand field := rfl

@[miri_rvalue] theorem canonical_readImmediate (config : Config) (choice : C)
    (operand : OpTy Provenance) :
    (Hooks config).readImmediate choice operand = PlaceMachine.readImmediate config.access operand := rfl

attribute [miri_rvalue] CanonicalStepWP.canonical_discriminant_writeScalar

end Canonical
end Miri.Verification.DiscriminantWP

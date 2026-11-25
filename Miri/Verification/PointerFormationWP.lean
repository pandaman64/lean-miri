import Miri.Verification.CanonicalStepWP
import Miri.Verification.OperandPlaceWP
import Miri.Verification.TypedRetagWP
import Miri.Input.EvalRetagMachine

/-! Initial-state rules for the typed retag reached by MIR pointer formation.
The existing rvalue rule supplies destination/source evaluation, allocation,
validity and the mode scope. These rules continue through the concrete typed
retag and pass the reconstructed value to the ordinary place write. -/
namespace Miri.Verification.PointerFormationWP

open Miri.ABI Miri.Interpreter Miri.MIR Miri.Memory
open Miri.TreeBorrows.RetagPolicy RvalueWP

variable {K U C O X Host : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Failure" => StepError → State → Prop
local notation "Value" => RvalueImmTy Provenance

/-- Allocate a tag after the size query, then pull back through the actual
reborrow at that byte range. Success updates just the input pointer's
provenance. A tag allocated before a failing reborrow remains allocated. -/
def retagPlacePre [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (policy : NewPermission)
    (post : MPlaceTy Provenance → State → Prop) (failure : Failure) : State → Prop :=
  actionPre (hooks.sizeAndAlign place) (fun sizeAndAlign =>
    actionPre TypedRetag.tracker (fun old =>
      actionPre (TypedRetag.checked "new pointer tag" old.global.newPointerTag) (fun (global, tag) state =>
        let size := (sizeAndAlign.map Prod.fst).getD place.layout.layout.size
        let allocated := {state with machine.borrowTracker := some {old with global}}
        TypedRetagWP.reborrowPre hooks budget place size policy tag (fun provenance after =>
          match place.mplace.ptr.provenance, provenance with
          | none, _ =>
            post {place with mplace.ptr.provenance := none} after
          | some _, some new =>
            post {place with mplace.ptr.provenance := some new} after
          | some _, none => failure (.invalidProgram "retag lost existing provenance") after)
          failure allocated) failure) failure) failure

@[miri_initial_wp] theorem actionPre_retagPlace [DecidableEq K] (hooks : TypedRetag.Hooks K U)
    (budget : Nat) (place : MPlaceTy Provenance) (policy : NewPermission)
    (post : MPlaceTy Provenance → State → Prop) (failure : Failure) :
    actionPre (TypedRetag.retagPlace hooks budget place policy) post failure =
      retagPlacePre hooks budget place policy post failure := by
  rw [TypedRetag.retagPlace, actionPre_bind_fun]
  unfold retagPlacePre
  congr 1
  funext sizeAndAlign
  simp only [actionPre_bind_fun]
  congr 1
  funext old
  congr 1
  funext tagResult state
  rcases tagResult with ⟨global, tag⟩
  change actionPre (TypedRetag.reborrow hooks budget place _ policy tag) _ failure _ = _
  rw [propext (TypedRetagWP.reborrowPre_iff _ _ _ _ _ _ _ _ _), ← actionPre_eq_wp]
  congr 1
  funext provenance after
  cases place.mplace.ptr.provenance <;> cases provenance <;> rfl

/-- The typed dispatch uses the pointee mutability query to choose a shared
or mutable policy. The raw branch checks the scoped mode and keeps the
original immediate. The disabled tracker skips compiler queries. -/
def pointerRetagPre [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (value : Value) (ty : TyId) (post : Option Value → State → Prop)
    (failure : Failure) (before : State) : Prop :=
  match before.machine.borrowTracker with
  | none => post none before
  | some tracker =>
    actionPre (hooks.typeShape ty) (fun shape =>
      let withPolicy := fun policy =>
        match policy with
        | none => post none
        | some permission =>
          actionPre (hooks.immPtrToMPlace value) (fun place =>
            retagPlacePre hooks budget place permission
              (fun newPlace => actionPre (hooks.reconstruct value newPlace)
                (fun result => post (some result)) failure) failure) failure
      match shape.classify with
      | .globalBox =>
        actionPre (hooks.builtinDeref ty) (fun pointee =>
          actionPre (TypedRetag.newPermission hooks pointee .Box tracker.retagMode)
            withPolicy failure) failure
      | .reference =>
        actionPre (hooks.referencePointee ty) (fun (pointee, mutability) =>
          actionPre (TypedRetag.newPermission hooks pointee
            (if mutability == .Mut then .Mutable else .Shared) tracker.retagMode)
            withPolicy failure) failure
      | .rawPointer =>
        if tracker.retagMode != .Raw then
          failure (.invalidProgram "raw pointer retag outside Raw mode")
        else post none
      | .customAllocatorBox => post none
      | .invalidType => failure (.invalidProgram "tb_retag_ptr_value invalid type"))
      failure before

@[miri_initial_wp] theorem actionPre_machineRetagPtrValue [DecidableEq K]
    (hooks : TypedRetag.Hooks K U) (budget : Nat) (value : Value) (ty : TyId)
    (post : Option Value → State → Prop) (failure : Failure) (before : State) :
    actionPre (TypedRetag.machineRetagPtrValue hooks budget value ty) post failure before =
      pointerRetagPre hooks budget value ty post failure before := by
  unfold pointerRetagPre TypedRetag.machineRetagPtrValue
  rw [actionPre_bind, actionPre_ok (show (get : MachineHooks.M K U State) before = .ok before before from rfl)]
  cases before.machine.borrowTracker with
  | none => rfl
  | some tracker =>
    change actionPre (TypedRetag.retagPtrValue hooks budget value ty tracker.retagMode)
      post failure before = _
    rw [TypedRetag.retagPtrValue, actionPre_bind]
    congr 1
    funext shape
    have purePre {A : Type} (item : A) (next : A → State → Prop) :
        actionPre (pure item) next failure = next item := rfl
    have throwPre {A : Type} (error : StepError) (next : A → State → Prop) :
        actionPre (throw error) next failure = failure error := rfl
    have tail (policy : Option NewPermission) :
        actionPre (do
          let some permission := policy | return none
          let place ← hooks.immPtrToMPlace value
          let updated ← TypedRetag.retagPlace hooks budget place permission
          return some (← hooks.reconstruct value updated)) post failure =
        match policy with
        | none => post none
        | some permission =>
          actionPre (hooks.immPtrToMPlace value) (fun place =>
            retagPlacePre hooks budget place permission
              (fun updated => actionPre (hooks.reconstruct value updated)
                (fun result => post (some result)) failure) failure) failure := by
      cases policy <;>
        simp only [purePre, actionPre_bind_fun, actionPre_retagPlace]
    cases shape.classify with
    | reference | globalBox =>
      simp only [actionPre_bind_fun]
      congr 1
      funext pointee
      congr 1
      funext policy
      exact tail policy
    | rawPointer =>
      by_cases invalid : (tracker.retagMode != .Raw) = true <;>
        simp only [invalid, Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun, purePre, throwPre]
    | customAllocatorBox =>
      simp only [actionPre_bind_fun, purePre]
    | invalidType =>
      simp only [actionPre_bind_fun, throwPre]

attribute [miri_initial_wp] CanonicalStepWP.canonical_rvalue_retagPtrValue

@[miri_initial_wp] theorem canonical_forceAllocation [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (place : RuntimePlace Provenance)
    (post : MemPlace Provenance → State → Prop) (failure : Failure) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).forceAllocation choice place) post failure =
      actionPre (forceAllocation (ExecutionMachine.projectionHooks
        (ExecutionMachine.withValidation config limits)).place choice place)
        (fun memory => post memory.mplace) failure := by
  change actionPre ((forceAllocation _ choice place) >>= _) post failure = _
  rw [actionPre_bind_fun]
  rfl

@[miri_initial_wp] theorem canonical_toRef [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (memory : MemPlace Provenance)
    (post : Immediate Provenance → State → Prop) (failure : Failure) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).toRef choice memory) post failure =
      scalarCheckPre (memory.toRef config.access.runtime.base |>.mapError
        fun error => .invalidProgram s!"place reference: {reprStr error}") post failure := by
  have references : (ExecutionMachine.withValidation config limits).access.runtime.base =
      config.access.runtime.base := rfl
  cases result : memory.toRef config.access.runtime.base <;>
    simp only [ExecutionMachine.rvalueHooks, references, result] <;> rfl

/-- The first projection determines whether the raw adjustment runs. For
an indirect place, the raw-type query reads the current MIR local type. -/
@[miri_initial_wp] theorem canonical_placeBaseRaw [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (place : Place)
    (post : Bool → State → Prop) (failure : Failure) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).placeBaseRaw choice place) post failure =
      if place.projection[0]? == some .Deref then
        StorageLiveWP.currentFramePre (fun frame =>
          match frame.body.locals[place.localId]? with
          | some ty => actionPre (config.isRawPointer choice ty) post failure
          | none => failure (.invalidProgram "raw place base local missing")) failure
      else post false := by
  by_cases deref : (place.projection[0]? == some .Deref) = true
  · simp only [ExecutionMachine.rvalueHooks, deref, ↓reduceIte, actionPre_bind_fun,
      StorageLiveWP.actionPre_currentFrame]
    congr 1
    funext frame
    cases frame.body.locals[place.localId]? <;> rfl
  · simp only [ExecutionMachine.rvalueHooks, deref, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The RawPtr write is outside this scope. A successful raw type query
returns the initial immediate and never allocates a new tag. -/
@[miri_initial_wp ↓ high] theorem actionPre_rawAdjustment [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (value : Value)
    (post : Value → State → Prop) (failure : Failure) :
    let hooks := ExecutionMachine.rvalueHooks config limits
    actionPre (hooks.withRetagMode choice .Raw do
      return (← hooks.retagPtrValue choice value value.layout.ty).getD value) post failure =
      retagModePullback .Raw (fun next onError before =>
        pointerRetagPre config.retag limits.retag value value.layout.ty
          (fun adjusted => next (adjusted.getD value)) onError before) post failure := by
  dsimp only
  rw [actionPre_rvalueHooks_withRetagMode]
  unfold retagModePre
  apply congrArg (fun pull => retagModePullback .Raw pull post failure)
  funext next onError before
  rw [actionPre_bind, CanonicalStepWP.canonical_rvalue_retagPtrValue, actionPre_machineRetagPtrValue]
  rfl

/-- Normalize the actual Ref rvalue before the generic retag scope can hide
its body from the typed pointer rule. -/
@[miri_initial_wp ↓ high] theorem evalPre_ref [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (region : Region) (borrow : BorrowKind)
    (source dest : Place) (post : State → Prop) (failure : Failure) (before : State) :
    let hooks := ExecutionMachine.rvalueHooks config limits
    evalPre hooks choice (.Ref region borrow source) dest post failure before =
      actionPre (hooks.evalPlace choice dest true) (fun target =>
        actionPre (hooks.evalPlace choice source true) (fun input =>
          actionPre (hooks.forceAllocation choice input) (fun memory =>
            actionPre (hooks.toRef choice memory) (fun immediate =>
              let value : Value := ⟨immediate, target.layout⟩
              let mode := if borrow == .Mut .TwoPhaseBorrow then .TwoPhase else .Default
              retagModePullback mode (fun next onError =>
                actionPre (hooks.enforceValidity choice value.layout) (fun enforce =>
                  if enforce then actionPre (hooks.writeImmediate choice value.imm target) next onError
                  else fun entered =>
                    pointerRetagPre config.retag limits.retag value value.layout.ty (fun adjusted =>
                      actionPre (hooks.writeImmediate choice (adjusted.getD value).imm target)
                        next onError) onError entered) onError) (fun _ => post) failure)
              failure) failure) failure) failure before := by
  simp only [evalPre]
  congr 1
  funext target
  congr 1
  funext input
  congr 1
  funext memory
  congr 1
  funext immediate
  rw [actionPre_rvalueHooks_withRetagMode]
  unfold retagModePre
  apply congrArg (fun pull => retagModePullback _ pull (fun _ => post) failure)
  funext next onError
  rw [actionPre_bind_fun]
  congr 1
  funext enforce
  cases enforce
  · simp only [Bool.not_false, ↓reduceIte, actionPre_bind_fun]
    funext entered
    rw [CanonicalStepWP.canonical_rvalue_retagPtrValue, actionPre_machineRetagPtrValue]
    rfl
  · rfl

/-- A raw address-of checks whether the source already has a raw base before
evaluating that place. If adjustment is required, it runs before the write. -/
@[miri_initial_wp ↓ high] theorem evalPre_rawPtr [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (kind : RawPtrKind) (source dest : Place)
    (post : State → Prop) (failure : Failure) (before : State) :
    let hooks := ExecutionMachine.rvalueHooks config limits
    evalPre hooks choice (.RawPtr kind source) dest post failure before =
      actionPre (hooks.evalPlace choice dest true) (fun target =>
        actionPre (hooks.placeBaseRaw choice source) (fun baseRaw =>
          actionPre (hooks.evalPlace choice source false) (fun input =>
            actionPre (hooks.forceAllocation choice input) (fun memory =>
              actionPre (hooks.toRef choice memory) (fun immediate =>
                let value : Value := ⟨immediate, target.layout⟩
                let write := fun adjusted : Value =>
                  actionPre (hooks.writeImmediate choice adjusted.imm target) (fun _ => post) failure
                if !baseRaw && kind != .FakeForPtrMetadata then
                  retagModePullback .Raw (fun next onError entered =>
                    pointerRetagPre config.retag limits.retag value value.layout.ty
                      (fun adjusted => next (adjusted.getD value)) onError entered) write failure
                else write value) failure) failure) failure) failure) failure before := by
  simp only [evalPre]
  congr 1
  funext target
  congr 1
  funext baseRaw
  congr 1
  funext input
  congr 1
  funext memory
  congr 1
  funext immediate
  by_cases adjust : (!baseRaw && kind != .FakeForPtrMetadata) = true
  · simp only [adjust, ↓reduceIte]
    exact actionPre_rawAdjustment config limits choice ⟨immediate, target.layout⟩ _ failure
  · simp only [adjust]
    rfl

/-- The write's validation hook reaches the same machine retag. Validation
continues to own the reference checks and the actual replacement write. -/
@[miri_initial_wp] theorem validity_retagPointer [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance State C MachineHooks.FrameExtra F A Pad)
    (retag : TypedRetag.Hooks K U) (budget : Nat) (choice : C) (value : Value) (ty : TyId) :
    (TypedMachineBindings.bindValidity hooks retag budget).retagPointer choice value ty =
      TypedRetag.machineRetagPtrValue retag budget value ty := rfl

/-- Production reconstruction re-encodes the adjusted pointer, preserving
the original immediate layout and the adjusted place's metadata. -/
@[miri_initial_wp] theorem production_reconstruct [DecidableEq K]
    (prepared : Miri.Input.CompilerFactAdapters.Prepared)
    (runtime : Miri.Input.CompilerRuntimeQueries.Prepared) (leaves : Miri.Input.EvalRetagMachine.Leaves K U)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (value : Value) (place : MPlaceTy Provenance)
    (post : Value → ValidityMachine.State K U → Prop)
    (failure : StepError → ValidityMachine.State K U → Prop) :
    actionPre ((Miri.Input.EvalRetagMachine.hooks prepared runtime leaves access projection vtable pointers
      choice).reconstruct value place) post failure =
      scalarCheckPre (place.mplace.toRef access.runtime.base |>.mapError
        fun error => .invalidProgram s!"retagged reference: {reprStr error}")
        (fun immediate => post ⟨immediate, value.layout⟩) failure := by
  cases encoded : place.mplace.toRef access.runtime.base <;>
    simp only [Miri.Input.EvalRetagMachine.hooks, encoded] <;> rfl

/-- Policy queries for explicit reference formation. The caller selects the
mode from the MIR borrow kind; only function entry can register a protector. -/
@[miri_initial_wp] theorem actionPre_newPermission_formed (hooks : TypedRetag.Hooks K U)
    (ty : TyId) (kind : ReferenceKind) (mode : RetagMode)
    (formation : mode = .Default ∨ mode = .TwoPhase)
    (post : Option NewPermission → State → Prop) (failure : Failure) :
    actionPre (TypedRetag.newPermission hooks ty kind mode) post failure =
      actionPre (hooks.isUnpin ty) (fun unpin =>
        actionPre (if unpin then hooks.isUnsafeUnpin ty else pure false) (fun unsafeUnpin =>
          actionPre (hooks.typeIsFreeze ty) (fun freeze =>
            post (create ⟨unpin, unsafeUnpin, freeze⟩ kind mode ⟨false, false⟩))
            failure) failure) failure := by
  rcases formation with rfl | rfl <;>
    simp only [TypedRetag.newPermission, show (RetagMode.Default == .None) = false from rfl,
      show (RetagMode.TwoPhase == .None) = false from rfl,
      show (RetagMode.Default == .FnEntry) = false from rfl,
      show (RetagMode.TwoPhase == .FnEntry) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun]
  all_goals
    congr 1
    funext unpin
    cases unpin <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun] <;> rfl

theorem formed_policy_unprotected (facts : TypeFacts) (kind : ReferenceKind)
    (mode : RetagMode) (policy : NewPermission) (formation : mode = .Default ∨ mode = .TwoPhase)
    (selected : create facts kind mode ⟨false, false⟩ = some policy) :
    policy.protector = none := by
  rcases facts with ⟨unpin, unsafeUnpin, freeze⟩
  rcases formation with rfl | rfl <;> cases kind <;> cases unpin <;> cases unsafeUnpin <;>
    cases freeze <;> cases selected <;> rfl

/-- The raw-pointer branch returns no replacement. The type-shape query
still runs under Raw mode and can fail with its own state. -/
theorem rawPointerPre [DecidableEq K] (hooks : TypedRetag.Hooks K U)
    (budget : Nat) (value : Value) (ty : TyId)
    (post : Option Value → State → Prop) (failure : Failure)
    (before after : State) (tracker : MachineHooks.BorrowState)
    (tracking : before.machine.borrowTracker = some tracker) (mode : tracker.retagMode = .Raw)
    (shape : Miri.TreeBorrows.RetagPipeline.RetagTypeShape)
    (query : hooks.typeShape ty before = .ok shape after) (raw : shape.classify = .rawPointer) :
    actionPre (TypedRetag.machineRetagPtrValue hooks budget value ty) post failure before =
      post none after := by
  rw [actionPre_machineRetagPtrValue]
  simp only [pointerRetagPre, tracking, actionPre_ok query, raw, mode,
    show (RetagMode.Raw != .Raw) = false from rfl, Bool.false_eq_true, ↓reduceIte]

end Miri.Verification.PointerFormationWP

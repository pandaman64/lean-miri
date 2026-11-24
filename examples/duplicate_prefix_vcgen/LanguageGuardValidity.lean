import Miri.Interpreter.ExecutionValidity
import Lean

namespace DuplicatePrefix.LanguageGuardValidity

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
open ValidityVisitor

set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

variable {S C E F A Pad : Type}
local notation "Hooks" => ValidityVisitor.Hooks Provenance S C E F A Pad

open Lean Elab Tactic in
elab "unfold_validity_helper " suffix:str : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".ValidityVisitor." ++ suffix.getString) then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one validity helper named {suffix.getString}"

/-- A legal scalar Boolean with no memory ranges does not leave work for
provenance reset, padding writes or recursive validation. -/
theorem visitBooleanImmediate (value : Bool) (h : Hooks) (choice : C) (fuel : Nat)
    (session : Session Provenance) (place : RuntimePlace Provenance) (state : S)
    (ranges : session.dataBytes = none)
    (classified : h.classify choice place.layout.ty state = .ok .boolean state)
    (read : h.readImmediate choice place .boolean state =
      .ok ⟨.scalar (Scalar.fromBool value), place.layout⟩ state)
    (cleared : h.clearProvenance choice place state = .ok () state) :
    visit h choice (fuel + 1) session place state = .ok session state := by
  simp only [visit, bind, Bind.bind, EStateM.bind, classified]
  unfold_validity_helper "primitive"
  unfold_validity_helper "scalarOf"
  unfold_validity_helper "liftResult"
  unfold_validity_helper "markPlace"
  have scalar : (Immediate.scalar (Scalar.fromBool value : Scalar Provenance)).toScalar =
      .ok (Scalar.fromBool value) := rfl
  have boolean : (Scalar.fromBool value : Scalar Provenance).toBool = .ok value := by cases value <;> rfl
  simp only [bind, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
    beq_self_eq_true, ↓reduceIte, read, scalar, boolean, Except.mapError, ranges]
  cases session.flags.resetProvenanceAndPadding <;>
    simp [EStateM.pure, EStateM.bind, cleared]

def booleanValue (value : Bool) (layout : LocalLayout) : OpTy Provenance :=
  ⟨.immediate (.scalar (Scalar.fromBool value)), layout⟩

/-- Source scalar provenance reset is a no-op for a Boolean immediate. -/
theorem clearBooleanImmediate {K Extra H X : Type} [DecidableEq K] (value : Bool)
    (env : ValidityMemory.Environment Provenance Extra K H X S)
    (places : PlaceHooks Provenance S C E) (choice : C)
    (validation : ValidityVisitor.M S Bool)
    (write : LocalId → Bool → ValidityVisitor.M S Unit)
    (place : RuntimePlace Provenance) (state : S)
    (operand : placeToOp places choice place state = .ok (booleanValue value place.layout) state) :
    ValidityMemory.clearPlaceProvenance env places choice validation write place state = .ok () state := by
  simp only [ValidityMemory.clearPlaceProvenance, bind, Bind.bind, EStateM.bind, operand]
  cases value <;> rfl

variable {K U : Type}
local notation "State" => ValidityMachine.State K U
local notation "MachineVisitor" => ValidityVisitor.Hooks Provenance State C MachineHooks.FrameExtra F A Pad

private def ghostOn (before : State) : State :=
  {before with machine := {before.machine with user := {before.machine.user with
    payload := {before.machine.user.payload with ghost := true}}}}

/-- The production validity decoder checks the actual scalar value from
the local and commits the no-allocation read. -/
theorem readBooleanImmediate [DecidableEq K] (value : Bool)
    (access : ValidityMachine.Access K U) (layout : LocalLayout) (state : State)
    (sized : isPrimitiveReadable layout.layout.backendRepr = true)
    (retain : access.retainTouched state.machine none = state.machine) :
    ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access)
      (booleanValue value layout) .boolean state =
      .ok ⟨.scalar (Scalar.fromBool value), layout⟩ state := by
  simp only [ValidityMemory.readImmediate, booleanValue, localMemoryLayout,
    Miri.Interpreter.readImmediate, sized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  conv => lhs; cbv
  cbv at retain
  rw [retain]
  rfl

/-- Discharge the complete shallow visitor action for a Boolean local using
the canonical ghost-state transition. The input observations are only
compiler metadata and the immediate local's value. -/
theorem validateBooleanPlace (value : Bool) (h : MachineVisitor) (choice : C) (fuel : Nat)
    (place : RuntimePlace Provenance) (before : State) (name : String)
    (inactive : before.machine.user.payload.ghost = false)
    (ghost : ∀ action : ValidityVisitor.M State (Session Provenance),
      h.withGhostValidation action = ValidityMachine.withGhostValidation action)
    (typeName : h.typeName choice place.layout.ty before = .ok name before)
    (operand : h.toOp choice place (ghostOn before) = .ok (booleanValue value place.layout) (ghostOn before))
    (classified : h.classify choice place.layout.ty (ghostOn before) = .ok .boolean (ghostOn before))
    (read : h.readImmediate choice place .boolean (ghostOn before) =
      .ok ⟨.scalar (Scalar.fromBool value), place.layout⟩ (ghostOn before))
    (cleared : h.clearProvenance choice place (ghostOn before) = .ok () (ghostOn before)) :
    validatePlace h choice (fuel+1) place false true before = .ok () before := by
  let initial : Session Provenance :=
    { path := ⟨name, #[]⟩, flags := ⟨true, false⟩, ctfeMode := none, refTracking := none, dataBytes := none }
  have visited := visitBooleanImmediate value h choice fuel initial place (ghostOn before) rfl classified read cleared
  simp only [validatePlace, bind, Bind.bind, EStateM.bind, typeName, ghost]
  have noPadding := resetPadding_no_ranges h choice initial place rfl
  simp only [ValidityMachine.withGhostValidation, inactive, Bool.false_eq_true, ↓reduceIte,
    EStateM.bind, pure, Pure.pure, EStateM.pure, ghostOn] at operand visited ⊢
  simp only [initial] at visited noPadding
  rw [operand]
  simp only [booleanValue, EStateM.bind]
  rw [visited]
  simp only
  rw [noPadding]
  cases before with
  | mk stack machine =>
    cases machine with
    | mk _ _ _ _ _ _ user =>
      cases user with
      | mk _ payload _ =>
        cases payload
        simp_all [pure, Pure.pure, EStateM.pure, ghostOn]

/-- Specialize the shallow scalar proof to the actual production dictionary.
Layout readability, compiler queries, and reading the known local are the
only input facts. The visitor reads and checks the Boolean, restores ghost
mode, and performs no provenance or padding writes. -/
theorem validateCanonicalBooleanPlace [DecidableEq K] (value : Bool)
    (queries : ExecutionValidity.Leaves State C)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (projection : PlaceProjectionHooks Provenance State C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance State C F A)
    (discriminant : DiscriminantHooks Provenance State C (RuntimePlace Provenance))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (retagBudget fuel : Nat) (choice : C) (place : RuntimePlace Provenance)
    (before : State) (name : String) (inactive : before.machine.user.payload.ghost = false)
    (typeName : queries.typeName choice place.layout.ty before = .ok name before)
    (classified : queries.classify choice place.layout.ty (ghostOn before) = .ok .boolean (ghostOn before))
    (operand : placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler))
        choice place (ghostOn before) = .ok (booleanValue value place.layout) (ghostOn before))
    (readable : isPrimitiveReadable place.layout.layout.backendRepr = true)
    (retainGhost : access.retainTouched (ghostOn before).machine none = (ghostOn before).machine) :
    validatePlace (ExecutionValidity.hooks queries access allocation compiler projection vtable
      discriminant retag retagBudget) choice (fuel + 1) place false true before = .ok () before := by
  apply validateBooleanPlace value _ choice fuel place before name inactive (fun _ => rfl) typeName operand classified
  · change ((do
      let operand ← placeToOp (ValidityMachine.placeHooks access allocation
        (ValidityMachine.compilerPolicy compiler)) choice place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) operand .boolean)
        (ghostOn before)) = _
    simp only [bind, Bind.bind, EStateM.bind, operand]
    exact readBooleanImmediate value access place.layout (ghostOn before) readable retainGhost
  · exact clearBooleanImmediate value (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler))
      choice ValidityMachine.validationInProgress MachineHooks.afterLocalWrite place (ghostOn before) operand

/-- The copied value is read from the indexed caller slot, through the
ordinary typed place and local-layout cache. Ghost validation suppresses
local read hooks independently of the caller's local clock state. -/
theorem ghostLocalBoolean [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (value : Bool) (choice : C)
    (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (index : LocalId) (layout : LocalLayout) (slot : LocalState Provenance LocalLayout)
    (atSlot : caller.locals[index]? = some slot)
    (cached : slot.layout = some layout)
    (stored : slot.value = .live (.immediate (.scalar (Scalar.fromBool value))))
    (sized : layout.layout.isSized = true)
    (ghost : machine.user.payload.ghost = true)
    (debugOff : compiler.debugAssertions = false) :
    let before : State := ⟨⟨older.push caller⟩, machine⟩
    let dest : RuntimePlace Provenance := ⟨.local older.size index none caller.localsIdentity, layout⟩
    placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler))
      choice dest before = .ok (booleanValue value layout) before := by
  have bound := (Array.getElem?_eq_some_iff.mp atSlot).1
  have found := (Array.getElem?_eq_some_iff.mp atSlot).2
  have getSlot : Frame.getLocal caller index = .ok slot := by
    simp [Frame.getLocal, bound, found, pure, Pure.pure, Except.pure]
  have operand : Frame.getLocalOperand caller index =
      .ok (.immediate (.scalar (Scalar.fromBool value))) := by
    simp [Frame.getLocalOperand, getSlot, LocalState.access, stored,
      bind, Bind.bind, Except.bind, Except.mapError]
  simp [placeToOp, placeToOpCore, ValidityMachine.placeHooks, ValidityMachine.compilerPolicy,
    PlaceMachine.placeHooks, PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
    ValidityMachine.validationInProgress, Stack.frameIndex, MachineHooks.currentFrame, Stack.currentFrame?,
    getSlot, cached, operand, sized, debugOff, ghost, booleanValue,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Except.pure]

/-- The canonical visitor validates a live immediate Boolean in the real
current frame. The remaining facts are readonly compiler and layout data. -/
theorem validateCachedBoolean [DecidableEq K]
    (queries : ExecutionValidity.Leaves State C)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (projection : PlaceProjectionHooks Provenance State C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance State C F A)
    (discriminant : DiscriminantHooks Provenance State C (RuntimePlace Provenance))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (retagBudget fuel : Nat) (value : Bool) (choice : C)
    (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (index : LocalId) (layout : LocalLayout) (slot : LocalState Provenance LocalLayout)
    (atSlot : caller.locals[index]? = some slot)
    (cached : slot.layout = some layout)
    (stored : slot.value = .live (.immediate (.scalar (Scalar.fromBool value))))
    (sized : layout.layout.isSized = true)
    (inactive : machine.user.payload.ghost = false)
    (debugOff : compiler.debugAssertions = false)
    (readable : isPrimitiveReadable layout.layout.backendRepr = true)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (name : String) :
    let before : State := ⟨⟨older.push caller⟩, machine⟩
    let destination : RuntimePlace Provenance := ⟨.local older.size index none caller.localsIdentity, layout⟩
    queries.typeName choice layout.ty before = .ok name before →
    queries.classify choice layout.ty (ghostOn before) = .ok .boolean (ghostOn before) →
    validatePlace (ExecutionValidity.hooks queries access allocation compiler projection vtable
      discriminant retag retagBudget) choice (fuel + 1) destination false true before = .ok () before := by
  intro before destination typeName classified
  apply validateCanonicalBooleanPlace value queries access allocation compiler projection vtable
    discriminant retag retagBudget fuel choice destination before name inactive typeName classified
  · exact ghostLocalBoolean access allocation compiler value choice older caller (ghostOn before).machine
      index layout slot atSlot cached stored sized rfl debugOff
  · exact readable
  · exact retain _

end DuplicatePrefix.LanguageGuardValidity

#print axioms DuplicatePrefix.LanguageGuardValidity.validateCanonicalBooleanPlace

#print axioms DuplicatePrefix.LanguageGuardValidity.ghostLocalBoolean

#print axioms DuplicatePrefix.LanguageGuardValidity.validateCachedBoolean

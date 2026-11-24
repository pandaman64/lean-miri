import Miri.Verification.EffectSpecs
import Miri.Verification.InstructionWP
import Lean.Meta.Tactic.Simp.RegisterCommand

/-! Exact preconditions for assignment, following the order of the rvalue
dispatcher and preserving the state at every failed effect. -/
/-- Opt-in simplification rules for a selected MIR rvalue and the production
hooks used by its continuation. -/
register_simp_attr miri_rvalue

namespace Miri.Verification.RvalueWP

open Miri.ABI Miri.Interpreter Miri.MIR Miri.Memory
open Miri.TreeBorrows.RetagPolicy Std.WP

variable {P S C V A B : Type}

/-- Pull back a success and an error continuation through a single effect. -/
def actionPre (action : RvalueM S A) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) : Prop :=
  match action before with
  | .ok value after => post value after
  | .error error failed => onError error failed

theorem actionPre_bind (action : RvalueM S A) (next : A → RvalueM S B)
    (post : B → S → Prop) (onError : StepError → S → Prop) (before : S) :
    actionPre (action >>= next) post onError before =
      actionPre action (fun value => actionPre (next value) post onError) onError before := by
  unfold actionPre
  cases result : action before <;> simp [bind, Bind.bind, EStateM.bind, result]

theorem actionPre_ok {action : RvalueM S A} {before after : S} {value : A}
    (ran : action before = .ok value after) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre action post onError before = post value after := by
  simp only [actionPre, ran]

theorem actionPre_pure (value : A) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    actionPre (pure value) post onError before = post value before := rfl

theorem actionPre_throw (error : StepError) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    actionPre (throw error) post onError before = onError error before := rfl

theorem actionPre_run (action : RvalueM S A) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    actionPre action post onError before ↔
      InstructionWP.resultPre post onError (runRvalue action before) := by
  unfold actionPre runRvalue
  cases action before <;> rfl

theorem actionPre_bind_fun (action : RvalueM S A) (next : A → RvalueM S B)
    (post : B → S → Prop) (onError : StepError → S → Prop) :
    actionPre (action >>= next) post onError =
      actionPre action (fun value => actionPre (next value) post onError) onError :=
  funext (actionPre_bind action next post onError)

theorem actionPre_ite (guard : Prop) [Decidable guard] (yes no : RvalueM S A)
    (post : A → S → Prop) (onError : StepError → S → Prop) :
    actionPre (if guard then yes else no) post onError =
      if guard then actionPre yes post onError else actionPre no post onError := by
  by_cases guard <;> simp [*]

private theorem actionPre_congr (action : RvalueM S A) (onError : StepError → S → Prop) (before : S)
    {left right : A → S → Prop} (same : ∀ value state, left value state = right value state) :
    actionPre action left onError before = actionPre action right onError before := by
  rw [show left = right from funext fun value => funext (same value)]

/-- The symbolic pullback is Lean's error-state WP, so registered effect
rules can continue from any remaining rvalue action. -/
theorem actionPre_eq_wp (action : RvalueM S A) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre action post onError = wp action post onError := by
  funext before
  simp only [actionPre, wp, WP.wpTrans]
  cases action before <;> rfl

/-- Check the operand representation and its scalar width against the typed
layout before passing it to the interpreter's integer arithmetic. -/
def integerOperand [PointerProvenance P] (value : RvalueImmTy P)
    (kind : IntegerKind) : Except StepError IntegerValue := do
  let raw ← value.imm.toScalar.mapError ScalarOps.immediateError
  let scalar ← raw.toScalarInt.mapError ScalarOps.scalarError
  let _ ← scalar.toBits value.layout.layout.size |>.mapError ScalarOps.scalarIntError
  return ⟨scalar, ⟨value.layout.layout.size, kind⟩⟩

/-- Route a pure scalar check to the success or typed error continuation in
the current state. -/
def scalarCheckPre (result : Except StepError A) (post : A → S → Prop)
    (onError : StepError → S → Prop) (state : S) : Prop :=
  match result with
  | .ok value => post value state
  | .error error => onError error state

private def liftScalarCheck (result : Except StepError A) : RvalueM S A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

private theorem actionPre_scalarCheck (result : Except StepError A) (next : A → RvalueM S B)
    (post : B → S → Prop) (onError : StepError → S → Prop) :
    actionPre (liftScalarCheck result >>= next) post onError =
      scalarCheckPre result (fun value => actionPre (next value) post onError) onError := by
  cases result <;> rfl

private theorem liftScalarCheck_bind (result : Except StepError A) (next : A → Except StepError B) :
    (liftScalarCheck (result >>= next) : RvalueM S B) =
      liftScalarCheck result >>= fun value => liftScalarCheck (next value) := by
  cases result <;> rfl

private def integerOperandAction [PointerProvenance P] (value : RvalueImmTy P)
    (kind : IntegerKind) : RvalueM S IntegerValue := do
  let raw ← liftScalarCheck (value.imm.toScalar.mapError ScalarOps.immediateError)
  let scalar ← liftScalarCheck (raw.toScalarInt.mapError ScalarOps.scalarError)
  let _ ← liftScalarCheck (scalar.toBits value.layout.layout.size |>.mapError ScalarOps.scalarIntError)
  pure ⟨scalar, ⟨value.layout.layout.size, kind⟩⟩

private theorem liftIntegerOperand [PointerProvenance P] (value : RvalueImmTy P)
    (kind : IntegerKind) :
    (integerOperandAction value kind : RvalueM S IntegerValue) =
    liftScalarCheck (integerOperand value kind) := by
  simp only [integerOperandAction, integerOperand, liftScalarCheck_bind]
  rfl

/-- Pull unary evaluation back through classification, scalar representation
checks, and the concrete integer operator. Layout queries, float execution,
and pointer validation use their own success and failure states. -/
theorem actionPre_unary [PointerProvenance P] (h : ScalarOpsHooks P S C)
    (choice : C) (op : UnOp) (operand : RvalueImmTy P) (post : RvalueImmTy P → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (ScalarOps.unary h choice op operand) post onError =
      actionPre (h.classify choice operand.layout.ty) (fun type =>
        match type with
        | .boolean =>
          scalarCheckPre (operand.imm.toScalar.mapError ScalarOps.immediateError) (fun scalar =>
            scalarCheckPre (scalar.toBool.mapError ScalarOps.scalarError) (fun value =>
              if op != .Not then onError (.invalidProgram "invalid boolean unary operation")
              else actionPre (h.boolLayout choice) (fun layout =>
                post ⟨.scalar (.fromBool (!value)), layout⟩) onError) onError) onError
        | .integer kind =>
          scalarCheckPre (integerOperand operand kind) (fun value =>
            scalarCheckPre (IntegerOps.unary op value |>.mapError ScalarOps.integerError)
              (fun scalar => post ⟨.scalar (.fromScalarInt scalar), operand.layout⟩)
              onError) onError
        | .floating =>
          scalarCheckPre (operand.imm.toScalar.mapError ScalarOps.immediateError) (fun _ =>
            if op != .Neg then onError (.invalidProgram "invalid float unary operation")
            else actionPre (h.floatUnary choice op operand) post onError) onError
        | .pointer =>
          if op != .PtrMetadata then onError (.invalidProgram "invalid pointer unary operation")
          else actionPre (h.derefValidity choice operand) (fun _ =>
            scalarCheckPre (operand.imm.toScalarAndMeta.mapError ScalarOps.immediateError)
              (fun (_, metadata) =>
                match metadata with
                | .metadata scalar =>
                  actionPre (h.metadataLayout choice operand.layout.ty)
                    (fun layout => post ⟨.scalar scalar, layout⟩) onError
                | .none =>
                  actionPre (h.unitLayout choice) (fun layout => post ⟨.uninit, layout⟩) onError)
              onError) onError
        | .character => onError (.invalidProgram "invalid character unary operation")
        | .functionPointer => onError (.invalidProgram "invalid function-pointer unary operation"))
        onError := by
  rw [ScalarOps.unary, actionPre_bind_fun]
  congr 1
  funext type
  cases type with
  | boolean =>
    change actionPre (liftScalarCheck (operand.imm.toScalar.mapError ScalarOps.immediateError) >>= _) _ _ = _
    rw [actionPre_scalarCheck]
    congr 1
    funext scalar
    change actionPre (liftScalarCheck (scalar.toBool.mapError ScalarOps.scalarError) >>= _) _ _ = _
    rw [actionPre_scalarCheck]
    congr 1
    funext value
    split
    · rfl
    · exact actionPre_bind_fun (h.boolLayout choice) _ _ _
  | integer kind =>
    change actionPre (integerOperandAction operand kind >>= _) _ _ = _
    rw [liftIntegerOperand, actionPre_scalarCheck]
    congr 1
    funext value
    change actionPre (liftScalarCheck (IntegerOps.unary op value |>.mapError ScalarOps.integerError) >>= _) _ _ = _
    rw [actionPre_scalarCheck]
    rfl
  | floating =>
    change actionPre (liftScalarCheck (operand.imm.toScalar.mapError ScalarOps.immediateError) >>= _) _ _ = _
    rw [actionPre_scalarCheck]
    congr 1
    funext _
    split <;> rfl
  | pointer =>
    by_cases invalid : (op != .PtrMetadata) = true
    · simp only [invalid, ↓reduceIte]; rfl
    · simp only [invalid]
      change actionPre (h.derefValidity choice operand >>= _) _ _ = _
      rw [actionPre_bind_fun]
      congr 1
      funext _
      change actionPre (liftScalarCheck (operand.imm.toScalarAndMeta.mapError ScalarOps.immediateError) >>= _) _ _ = _
      rw [actionPre_scalarCheck]
      congr 1
      funext pair
      rcases pair with ⟨_, metadata⟩
      cases metadata <;> apply actionPre_bind_fun
  | character | functionPointer => rfl

/-- Pull a successful integer result back through its selected layout query.
Overflow-reporting operations write a pair, even when the overflow bit is set. -/
def integerResultPre [PointerProvenance P] (h : ScalarOpsHooks P S C) (choice : C)
    (input : LocalLayout) (post : RvalueImmTy P → S → Prop)
    (onError : StepError → S → Prop) : IntegerResult → S → Prop
  | .scalar scalar => post ⟨.scalar (.fromScalarInt scalar), input⟩
  | .withOverflow scalar overflow =>
    actionPre (h.overflowLayout choice input) (fun layout =>
      post ⟨.scalarPair (.fromScalarInt scalar) (.fromBool overflow), layout⟩) onError
  | .boolean value =>
    actionPre (h.boolLayout choice) (fun layout => post ⟨.scalar (.fromBool value), layout⟩) onError
  | .ordering value =>
    actionPre (h.orderingLayout choice) (fun layout =>
      let encoded : Int := match value with | .lt => -1 | .eq => 0 | .gt => 1
      scalarCheckPre (Scalar.fromInt encoded (Size.ofBytes 1) |>.mapError ScalarOps.scalarError)
        (fun scalar => post ⟨.scalar scalar, layout⟩) onError) onError

private theorem actionPre_finishInteger [PointerProvenance P] (h : ScalarOpsHooks P S C)
    (choice : C) (input : LocalLayout) (post : RvalueImmTy P → S → Prop)
    (onError : StepError → S → Prop) (result : IntegerResult) :
    actionPre (ExecutionScalar.finish (ExecutionScalar.Leaves.ofHooks h) choice input result)
      post onError = integerResultPre h choice input post onError result := by
  cases result with
  | scalar => rfl
  | withOverflow | boolean => exact actionPre_bind_fun _ _ _ _
  | ordering ordering =>
    change actionPre (h.orderingLayout choice >>= _) _ _ = _
    rw [actionPre_bind_fun]
    congr 1
    funext layout
    change actionPre (liftScalarCheck _ >>= _) _ _ = _
    rw [actionPre_scalarCheck]
    rfl

/-- After left classification selects the integral branch, read both checked
scalar widths, enforce matching non-shift type IDs, and use the interpreter's
integer result. Division by zero, signed division overflow, and unchecked
arithmetic overflow reach the typed error continuation before any write. -/
theorem actionPre_binary_integer [PointerProvenance P] (h : ScalarOpsHooks P S C)
    (choice : C) (op : BinOp) (left right : RvalueImmTy P)
    (post : RvalueImmTy P → S → Prop) (onError : StepError → S → Prop)
    (before classified : S) (leftKind : IntegerKind)
    (classification : h.classify choice left.layout.ty before = .ok (.integer leftKind) classified) :
    actionPre (ScalarOps.binary h choice op left right) post onError before =
      actionPre (h.classify choice right.layout.ty) (fun rightType =>
        match rightType with
        | .integer rightKind =>
          scalarCheckPre (integerOperand left leftKind) (fun lhs =>
            scalarCheckPre (integerOperand right rightKind) (fun rhs =>
              if !(op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked) &&
                  left.layout.ty != right.layout.ty then
                onError (.invalidProgram "asymmetric scalar operand types")
              else
                scalarCheckPre (IntegerOps.binary op lhs rhs |>.mapError ScalarOps.integerError)
                  (integerResultPre h choice left.layout post onError) onError) onError) onError
        | _ => onError (.invalidProgram "integer binary RHS is not integral"))
        onError classified := by
  rw [ScalarOps.binary, actionPre_bind_fun, actionPre_ok classification]
  change actionPre (h.classify choice right.layout.ty >>= _) _ _ _ = _
  rw [actionPre_bind_fun]
  congr 1
  funext type
  cases type with
  | integer rightKind =>
    change actionPre (integerOperandAction left leftKind >>= _) _ _ = _
    rw [liftIntegerOperand, actionPre_scalarCheck]
    congr 1
    funext lhs
    change actionPre (integerOperandAction right rightKind >>= _) _ _ = _
    rw [liftIntegerOperand, actionPre_scalarCheck]
    congr 1
    funext rhs
    let isShift := op == .Shl || op == .ShlUnchecked || op == .Shr || op == .ShrUnchecked
    let same := left.layout.ty == right.layout.ty
    let compute : RvalueM S (RvalueImmTy P) :=
      liftScalarCheck (IntegerOps.binary op lhs rhs |>.mapError ScalarOps.integerError) >>=
      ExecutionScalar.finish (ExecutionScalar.Leaves.ofHooks h) choice left.layout
    change actionPre (if !isShift then
      (if same then pure () else throw (.invalidProgram "asymmetric scalar operand types")) >>= fun _ => compute
      else compute) post onError =
      if !isShift && !same then onError (.invalidProgram "asymmetric scalar operand types") else _
    cases isShift <;> cases same <;>
      simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and,
        Bool.false_and, compute, actionPre_scalarCheck, actionPre_finishInteger]
    all_goals first
      | rfl
      | change actionPre compute post onError = _
        simp only [compute, actionPre_scalarCheck, actionPre_finishInteger]
  | _ => rfl

/-- Check the destination first and pull the postcondition through each
operation selected by the rvalue. A retag scope is a higher-order hook, so its
body remains an action until a concrete implementation of the scope is known. -/
def evalPre (hooks : RvalueHooks P S C V) (choice : C)
    (value : Rvalue) (place : Place) (post : S → Prop)
    (onError : StepError → S → Prop) (before : S) : Prop :=
  let pull := fun {A : Type} (action : RvalueM S A) (next : A → S → Prop) =>
    actionPre action next onError
  let finish := fun action => pull (A := Unit) action (fun _ => post)
  (pull (hooks.evalPlace choice place true) fun dest =>
    let layout := hooks.placeLayout dest
    let write := fun (result : RvalueImmTy P) => finish (hooks.writeImmediate choice result.imm dest)
    let writeChecked := fun (result : RvalueImmTy P) =>
      if result.layout == layout then write result
      else onError (.invalidProgram "rvalue result layout mismatch")
    match value with
    | .ThreadLocalRef definition =>
      pull (hooks.threadLocalPointer choice definition) fun pointer =>
        finish (hooks.writePointer choice pointer dest)
    | .Use operand retag =>
      pull (hooks.evalOperand choice operand (some layout)) fun op =>
        finish (hooks.withRetagMode choice (if retag == .Yes then .Default else .None)
          (hooks.copyOp choice op dest))
    | .CopyForDeref _ => onError (.invalidProgram "CopyForDeref in runtime MIR")
    | .BinaryOp operator left right =>
      pull (hooks.evalOperand choice left (if operator.leftHomogeneous then some layout else none)) fun left =>
      pull (hooks.readImmediate choice left) fun left =>
      pull (hooks.evalOperand choice right (if operator.rightHomogeneous then some left.layout else none)) fun right =>
      pull (hooks.readImmediate choice right) fun right =>
      pull (hooks.binaryOp choice operator left right) writeChecked
    | .UnaryOp operator operand =>
      pull (hooks.evalOperand choice operand (if operator.homogeneous then some layout else none)) fun op =>
      pull (hooks.readImmediate choice op) fun operand =>
      pull (hooks.unaryOp choice operator operand) writeChecked
    | .Aggregate kind operands => finish (hooks.writeAggregate choice kind operands dest)
    | .Repeat operand _ => finish (hooks.writeRepeat choice operand dest)
    | .Ref _ borrow src =>
      pull (hooks.evalPlace choice src true) fun src =>
      pull (hooks.forceAllocation choice src) fun memory =>
      pull (hooks.toRef choice memory) fun imm =>
        let val : RvalueImmTy P := ⟨imm, layout⟩
        let mode := if borrow == .Mut .TwoPhaseBorrow then RetagMode.TwoPhase else .Default
        finish (hooks.withRetagMode choice mode do
          let mut val := val
          if !(← hooks.enforceValidity choice val.layout) then
            if let some newVal ← hooks.retagPtrValue choice val val.layout.ty then val := newVal
          hooks.writeImmediate choice val.imm dest)
    | .Reborrow _ mutability src =>
      pull (hooks.evalPlaceToOp choice src none) fun op =>
        if mutability == .Not then finish (hooks.copyOpAllowTransmute choice op dest)
        else finish (hooks.copyOp choice op dest)
    | .RawPtr kind src =>
      pull (hooks.placeBaseRaw choice src) fun baseRaw =>
      pull (hooks.evalPlace choice src false) fun src =>
      pull (hooks.forceAllocation choice src) fun memory =>
      pull (hooks.toRef choice memory) fun imm =>
        let val : RvalueImmTy P := ⟨imm, layout⟩
        if !baseRaw && kind != .FakeForPtrMetadata then
          pull (hooks.withRetagMode choice .Raw do
            return (← hooks.retagPtrValue choice val val.layout.ty).getD val) write
        else write val
    | .Cast kind operand ty =>
      pull (hooks.evalOperand choice operand none) fun src =>
        finish (hooks.cast choice src kind ty dest)
    | .Discriminant src =>
      pull (hooks.evalPlaceToOp choice src none) fun op =>
      pull (hooks.readDiscriminant choice op) fun variant =>
      pull (hooks.discriminantForVariant choice op.layout.ty variant) write
    | .WrapUnsafeBinder operand _ =>
      pull (hooks.evalOperand choice operand none) fun op =>
        finish (hooks.copyOpAllowTransmute choice op dest)) before

theorem evalPre_iff (hooks : RvalueHooks P S C V) (choice : C)
    (value : Rvalue) (place : Place) (post : S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    evalPre hooks choice value place post onError before ↔
      actionPre (evalRvalueIntoPlace hooks choice value place) (fun _ => post) onError before := by
  cases value <;> simp only [evalPre, evalRvalueIntoPlace, actionPre_bind_fun, actionPre_ite]
  all_goals try with_unfolding_all rfl
  all_goals
    apply iff_of_eq
    apply actionPre_congr
    intro dest afterDest
    repeat' (apply actionPre_congr; intro _ _)
    rename_i result state
    change _ = actionPre
      (if result.layout == hooks.placeLayout dest then pure ()
       else throw (.invalidProgram "rvalue result layout mismatch")) _ _ state
    split <;> simp_all only [actionPre_pure, actionPre_throw]

section Canonical

variable {K U O X Host : Type}
local notation "State" => MachineHooks.State K U

private def restoreModePre (old : RetagMode) (post : State → Prop)
    (onError : StepError → State → Prop) (after : State) : Prop :=
  match after.machine.borrowTracker with
  | none => onError (.invalidProgram "borrow tracker removed during retag mode scope") after
  | some tracker => post { after with machine.borrowTracker := some { tracker with retagMode := old } }

/-- Enter the requested Tree Borrows mode and restore the caller's mode in
both continuations. A missing tracker in the resulting state overrides the
body outcome with the interpreter's invariant error. -/
def retagModePre (mode : RetagMode) (action : RvalueM State A) (post : A → State → Prop)
    (onError : StepError → State → Prop) (before : State) : Prop :=
  match before.machine.borrowTracker with
  | none => actionPre action post onError before
  | some tracker =>
    let entered := { before with machine.borrowTracker := some { tracker with retagMode := mode } }
    actionPre action (fun value => restoreModePre tracker.retagMode (post value) onError)
      (fun error => restoreModePre tracker.retagMode (onError error) onError) entered

theorem actionPre_withRetagMode (mode : RetagMode) (action : RvalueM State A)
    (post : A → State → Prop) (onError : StepError → State → Prop) (before : State) :
    actionPre (MachineHooks.withRetagMode mode action) post onError before =
      retagModePre mode action post onError before := by
  cases tracking : before.machine.borrowTracker with
  | none => simp only [retagModePre, actionPre, MachineHooks.withRetagMode, tracking]
  | some tracker =>
    simp only [retagModePre, actionPre, MachineHooks.withRetagMode, tracking]
    let entered : State := { before with machine.borrowTracker := some { tracker with retagMode := mode } }
    generalize action entered = result
    cases result with
    | ok value after => cases restored : after.machine.borrowTracker <;> simp [restoreModePre, restored]
    | error error after => cases restored : after.machine.borrowTracker <;> simp [restoreModePre, restored]

@[spec] theorem spec_withRetagMode (mode : RetagMode) (action : RvalueM State A)
    (post : A → State → Prop) (onError : StepError → State → Prop) :
    Triple (MachineHooks.withRetagMode mode action) (retagModePre mode action post onError)
      post onError :=
  Triple.iff.mpr fun before checked => by
    rw [← actionPre_eq_wp, actionPre_withRetagMode]
    exact checked

@[spec] theorem canonical_withRetagMode [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (mode : RetagMode) (action : RvalueM State A) :
    (ExecutionMachine.rvalueHooks config limits).withRetagMode choice mode action =
      MachineHooks.withRetagMode mode action := rfl

theorem canonical_placeLayout [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).placeLayout dest = dest.layout := rfl

@[spec] theorem canonical_readImmediate [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : OpTy Provenance) :
    (ExecutionMachine.rvalueHooks config limits).readImmediate choice operand =
      PlaceMachine.readImmediate config.access operand := rfl

@[spec] theorem canonical_writeImmediate [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (value : Immediate Provenance) (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).writeImmediate choice value dest =
      writePlaceImmediate (ExecutionMachine.projectionHooks config).place choice value dest := rfl

@[spec] theorem canonical_copyOp [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (source : OpTy Provenance) (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).copyOp choice source dest =
      copyRuntimePlace (ExecutionMachine.projectionHooks config).place
        (ExecutionMachine.withValidation config limits).copy choice source dest false := rfl

@[spec] theorem canonical_copyOpAllowTransmute [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (source : OpTy Provenance) (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).copyOpAllowTransmute choice source dest =
      copyRuntimePlace (ExecutionMachine.projectionHooks config).place
        (ExecutionMachine.withValidation config limits).copy choice source dest true := rfl

@[spec] theorem canonical_memoryCopy [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (source dest : MPlaceTy Provenance) :
    (ExecutionMachine.withValidation config limits).copy.memoryCopy choice source dest =
      GlobalMemoryCopyMachine.typedCopy config.access config.addresses config.arithmetic
        config.projection.dynamic config.projection.dynamicFuel config.compiler.debugAssertions
        choice source dest := rfl

/-- Specialize the retag scope rule without unfolding the other rvalue
hooks of the execution machine. -/
theorem actionPre_rvalueHooks_withRetagMode [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (mode : RetagMode) (action : RvalueM State A)
    (post : A → State → Prop) (onError : StepError → State → Prop) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).withRetagMode choice mode action)
      post onError = retagModePre mode action post onError :=
  funext (actionPre_withRetagMode mode action post onError)

end Canonical

end Miri.Verification.RvalueWP

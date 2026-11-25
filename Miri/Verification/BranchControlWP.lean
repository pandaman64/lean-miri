import Miri.Interpreter.ExecutionMachine
import Miri.Verification.RvalueWP

/-! Canonical branch rules that retain operand evaluation and compiler queries. -/
namespace Miri.Verification.BranchControlWP

open Miri.Interpreter Miri.MIR Miri.Memory Miri.ABI
open Miri.Verification

variable {K U C O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U
local notation "Errors" => StepError → State → Prop
local notation "Value" => RvalueImmTy Provenance

private def liftResult {S A : Type} (result : Except StepError A) : RvalueM S A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- Decode an assertion immediate using the same representation and boolean
checks as the machine. -/
def readBool (value : Value) : Except StepError Bool := do
  let scalar ← value.imm.toScalar.mapError ScalarOps.immediateError
  scalar.toBool.mapError ScalarOps.scalarError

/-- A switch and an assertion both evaluate an operand and read its immediate
before branching. -/
def readOperand (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (operand : Operand) : MachineHooks.M K U Value := do
  let checked := ExecutionMachine.withValidation config limits
  let value ← OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) choice operand none
  PlaceMachine.readImmediate checked.access value

private theorem lift_bind {S A B : Type} (result : Except StepError A)
    (next : A → Except StepError B) :
    ((liftResult result >>= fun value => liftResult (next value)) : RvalueM S B) =
      liftResult (result >>= next) := by
  cases result <;> rfl

/-- Read the assertion operand then route its pure boolean conversion to
the continuation. Even an ignored overflow assertion must read its operand. -/
def assertCondition (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (operand : Operand) : MachineHooks.M K U Bool := do
  liftResult (readBool (← readOperand config limits choice operand))

theorem assertCondition_eq (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (operand : Operand) :
    EffectSpecs.toEffect
      ((ExecutionMachine.terminatorHooks config limits).readAssertCondition choice operand) =
      assertCondition config limits choice operand := by
  rw [EffectSpecs.machine_run_effect]
  change (readOperand config limits choice operand >>= fun value =>
    liftResult (value.imm.toScalar.mapError ScalarOps.immediateError) >>= fun scalar =>
      liftResult (scalar.toBool.mapError ScalarOps.scalarError)) = _
  simp only [assertCondition, lift_bind, readBool]

@[miri_rvalue] theorem assertConditionPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : Operand) (post : Bool → State → Prop) (onError : Errors) :
    RvalueWP.actionPre (assertCondition config limits choice operand) post onError =
      RvalueWP.actionPre (readOperand config limits choice operand)
        (fun value => RvalueWP.scalarCheckPre (readBool value) post onError) onError := by
  rw [assertCondition, RvalueWP.actionPre_bind_fun]
  congr 1
  funext value
  cases readBool value <;> rfl

/-- Construct the case constant at the operand layout, invoke the production
comparison, then decode the comparison result. This path also covers
pointer cases. -/
def compareCase (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (value : Value) (bits : Nat) : MachineHooks.M K U Bool := do
  let checked := ExecutionMachine.withValidation config limits
  let scalar ← liftResult (Scalar.fromUInt (BitVec.ofNat 128 bits) value.layout.layout.size
    |>.mapError ScalarOps.scalarError)
  let result ← ScalarOps.binary (ExecutionMachine.scalarHooks checked) choice .Eq
    value ⟨.scalar scalar, value.layout⟩
  liftResult (readBool result)

private theorem compareCase_eq (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (value : Value) (bits : Nat) :
    EffectSpecs.toEffect
      ((ExecutionMachine.terminatorHooks config limits).compareSwitchCase choice value bits) =
      compareCase config limits choice value bits := by
  rw [EffectSpecs.machine_run_effect]
  change (liftResult _ >>= fun scalar =>
    ScalarOps.binary _ choice .Eq value ⟨.scalar scalar, value.layout⟩ >>= fun result =>
    liftResult (result.imm.toScalar.mapError ScalarOps.immediateError) >>= fun scalar =>
      liftResult (scalar.toBool.mapError ScalarOps.scalarError)) = compareCase _ _ _ _ _
  simp only [compareCase, lift_bind, readBool]

section Scalar

variable {S : Type}

@[miri_rvalue] theorem readBool_scalar (layout : LocalLayout) (value : Bool) :
    readBool ⟨.scalar (.fromBool value), layout⟩ = .ok value := by
  cases value <;> rfl

/-- When classification returns integral at both checks and both operands
decode at their common width, the comparison result is equality of the
decoded inputs. The boolean layout query still contributes its effects. -/
private theorem integerEqPre (hooks : ScalarOpsHooks Provenance S C) (choice : C) (layout : LocalLayout)
    (left right : Immediate Provenance) (kind : IntegerKind)
    (leftValue rightValue : IntegerValue) (leftInt rightInt : Int)
    (classify : hooks.classify choice layout.ty = pure (.integer kind))
    (leftChecked : RvalueWP.integerOperand ⟨left, layout⟩ kind = .ok leftValue)
    (rightChecked : RvalueWP.integerOperand ⟨right, layout⟩ kind = .ok rightValue)
    (sameType : leftValue.type = rightValue.type)
    (leftDecoded : IntegerOps.decode leftValue = .ok leftInt)
    (rightDecoded : IntegerOps.decode rightValue = .ok rightInt)
    (post : Bool → S → Prop) (onError : StepError → S → Prop) :
    RvalueWP.actionPre (do
        let result ← ScalarOps.binary hooks choice .Eq ⟨left, layout⟩ ⟨right, layout⟩
        liftResult (readBool result)) post onError =
      RvalueWP.actionPre (hooks.boolLayout choice) (fun _ => post (leftInt == rightInt)) onError := by
  have binary : IntegerOps.binary .Eq leftValue rightValue = .ok (.boolean (leftInt == rightInt)) := by
    simp [IntegerOps.binary, leftDecoded, rightDecoded, sameType, bind, Bind.bind, Except.bind, pure,
      Pure.pure, Except.pure]
  rw [RvalueWP.actionPre_bind_fun]
  funext before
  have classified : hooks.classify choice layout.ty before = .ok (.integer kind) before := by
    rw [classify]
    rfl
  rw [RvalueWP.actionPre_binary_integer hooks choice .Eq ⟨left, layout⟩ ⟨right, layout⟩
    (fun value => RvalueWP.actionPre (liftResult (readBool value)) post onError) onError
    before before kind classified, RvalueWP.actionPre_ok classified]
  simp only [RvalueWP.scalarCheckPre, leftChecked, rightChecked, RvalueWP.integerResultPre,
    beq_self_eq_true, bne, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    binary, Except.mapError, readBool_scalar, liftResult]
  rfl

/-- Specialize a canonical switch comparison after its case constant has
passed construction and both integer immediates decode successfully. -/
theorem compareCase_integerPre (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (value : Value) (bits : Nat) (caseScalar : Scalar Provenance) (kind : IntegerKind)
    (leftValue rightValue : IntegerValue) (leftInt rightInt : Int)
    (caseOk : Scalar.fromUInt (BitVec.ofNat 128 bits) value.layout.layout.size = .ok caseScalar)
    (classify : config.scalar.classify choice value.layout.ty = pure (.integer kind))
    (leftChecked : RvalueWP.integerOperand value kind = .ok leftValue)
    (rightChecked : RvalueWP.integerOperand ⟨.scalar caseScalar, value.layout⟩ kind = .ok rightValue)
    (sameType : leftValue.type = rightValue.type)
    (leftDecoded : IntegerOps.decode leftValue = .ok leftInt)
    (rightDecoded : IntegerOps.decode rightValue = .ok rightInt)
    (post : Bool → State → Prop) (onError : Errors) :
    RvalueWP.actionPre (compareCase config limits choice value bits) post onError =
      RvalueWP.actionPre (config.scalar.boolLayout choice)
        (fun _ => post (leftInt == rightInt)) onError := by
  rcases value with ⟨imm, layout⟩
  simp only [compareCase, caseOk, Except.mapError, liftResult, pure_bind]
  exact integerEqPre _ _ _ _ _ _ _ _ _ _ classify leftChecked rightChecked
    sameType leftDecoded rightDecoded _ _

/-- When both scalar integers fit the unsigned operand layout, compare their
extracted bits. The source's classification and result-layout queries remain
observable through the classification premise and the continuation. -/
theorem compareCase_unsignedBitsPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (layout : LocalLayout) (left right : ScalarInt) (caseBits : Nat)
    (leftBits rightBits : BitVec 128) (kind : IntegerKind)
    (caseOk : Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 caseBits) layout.layout.size =
      .ok (.fromScalarInt right))
    (classify : config.scalar.classify choice layout.ty = pure (.integer kind))
    (unsigned : kind.signed = false)
    (leftWidth : left.toBits layout.layout.size = .ok leftBits)
    (rightWidth : right.toBits layout.layout.size = .ok rightBits)
    (post : Bool → State → Prop) (onError : Errors) :
    RvalueWP.actionPre
        (compareCase config limits choice ⟨.scalar (.fromScalarInt left), layout⟩ caseBits)
        post onError =
      RvalueWP.actionPre (config.scalar.boolLayout choice) (fun _ => post (leftBits == rightBits))
        onError := by
  let leftValue : IntegerValue := ⟨left, ⟨layout.layout.size, kind⟩⟩
  let rightValue : IntegerValue := ⟨right, ⟨layout.layout.size, kind⟩⟩
  have leftChecked :
      RvalueWP.integerOperand (P := Provenance) ⟨.scalar (.fromScalarInt left), layout⟩ kind = .ok leftValue := by
    change (left.toBits layout.layout.size |>.mapError ScalarOps.scalarIntError) >>= _ = _
    rw [leftWidth]
    rfl
  have rightChecked :
      RvalueWP.integerOperand (P := Provenance) ⟨.scalar (.fromScalarInt right), layout⟩ kind = .ok rightValue := by
    change (right.toBits layout.layout.size |>.mapError ScalarOps.scalarIntError) >>= _ = _
    rw [rightWidth]
    rfl
  have leftDecoded : IntegerOps.decode leftValue = .ok (Int.ofNat leftBits.toNat) := by
    simp only [IntegerOps.decode, leftValue, IntegerType.signed, unsigned, Bool.false_eq_true,
      ↓reduceIte, ScalarInt.toUInt, leftWidth]
    rfl
  have rightDecoded : IntegerOps.decode rightValue = .ok (Int.ofNat rightBits.toNat) := by
    simp only [IntegerOps.decode, rightValue, IntegerType.signed, unsigned, Bool.false_eq_true,
      ↓reduceIte, ScalarInt.toUInt, rightWidth]
    rfl
  have bitsEq : (Int.ofNat leftBits.toNat == Int.ofNat rightBits.toNat) = (leftBits == rightBits) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨fun h => BitVec.toNat_inj.mp (Int.ofNat.inj h),
      fun h => congrArg (fun bits : BitVec 128 => Int.ofNat bits.toNat) h⟩
  rw [← bitsEq]
  exact compareCase_integerPre config limits choice ⟨.scalar (.fromScalarInt left), layout⟩
    caseBits (.fromScalarInt right) kind leftValue rightValue (Int.ofNat leftBits.toNat)
    (Int.ofNat rightBits.toNat) caseOk classify leftChecked rightChecked rfl leftDecoded rightDecoded
    post onError

/-- A boolean switch comparison checks both representations before comparing
their values. The bool result-layout query can still succeed or fail. -/
theorem compareCase_boolPre (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (value : Value) (caseBits : Nat) (caseScalar : Scalar Provenance) (left right : Bool)
    (caseOk : Scalar.fromUInt (BitVec.ofNat 128 caseBits) value.layout.layout.size = .ok caseScalar)
    (classify : config.scalar.classify choice value.layout.ty = pure .boolean)
    (leftChecked : readBool value = .ok left)
    (rightChecked : readBool ⟨.scalar caseScalar, value.layout⟩ = .ok right)
    (post : Bool → State → Prop) (onError : Errors) :
    RvalueWP.actionPre (compareCase config limits choice value caseBits) post onError =
      RvalueWP.actionPre (config.scalar.boolLayout choice) (fun _ => post (left == right)) onError := by
  let checked := ExecutionMachine.withValidation config limits
  let h := ExecutionMachine.scalarHooks checked
  let caseValue : Value := ⟨.scalar caseScalar, value.layout⟩
  have classEq : h.classify choice value.layout.ty = pure .boolean := classify
  have compareEq : ScalarOps.binary h choice .Eq value caseValue =
      (do let layout ← config.scalar.boolLayout choice
          pure ⟨.scalar (.fromBool (left == right)), layout⟩) := by
    simp only [ScalarOps.binary, classEq, pure_bind]
    change ((if value.layout.ty == value.layout.ty then pure () else
        throw (StepError.invalidProgram "asymmetric scalar operand types")) >>= fun _ =>
        liftResult (value.imm.toScalar.mapError ScalarOps.immediateError) >>= fun l =>
        liftResult (caseValue.imm.toScalar.mapError ScalarOps.immediateError) >>= fun r =>
        liftResult (l.toBool.mapError ScalarOps.scalarError) >>= fun lhs =>
        liftResult (r.toBool.mapError ScalarOps.scalarError) >>= fun rhs =>
        liftResult ((IntegerOps.binaryBool .Eq lhs rhs).mapError ScalarOps.integerError) >>= fun _ => _) = _
    have rightScalar : caseValue.imm.toScalar.mapError ScalarOps.immediateError = .ok caseScalar := rfl
    simp only [beq_self_eq_true, ite_true, pure_bind, rightScalar]
    change (liftResult (value.imm.toScalar.mapError ScalarOps.immediateError) >>= fun l =>
        liftResult (l.toBool.mapError ScalarOps.scalarError) >>= fun lhs =>
        liftResult (caseScalar.toBool.mapError ScalarOps.scalarError) >>= fun rhs =>
        liftResult ((IntegerOps.binaryBool .Eq lhs rhs).mapError ScalarOps.integerError) >>= fun _ => _) = _
    have rightBool : caseScalar.toBool.mapError ScalarOps.scalarError = .ok right := rightChecked
    have leftAction :
        ((liftResult (value.imm.toScalar.mapError ScalarOps.immediateError) >>= fun l =>
          liftResult (l.toBool.mapError ScalarOps.scalarError)) : RvalueM State Bool) = pure left := by
      rw [lift_bind]
      change liftResult (readBool value) = _
      rw [leftChecked]
      rfl
    rw [← bind_assoc, leftAction, pure_bind, rightBool]
    rfl
  unfold compareCase
  simp only [caseOk, Except.mapError, liftResult, pure_bind]
  change RvalueWP.actionPre
    (ScalarOps.binary h choice .Eq value caseValue >>= fun result => liftResult (readBool result)) _ _ = _
  rw [compareEq, RvalueWP.actionPre_bind_fun, RvalueWP.actionPre_bind_fun]
  congr 1
  funext layout after
  rw [RvalueWP.actionPre_pure, readBool_scalar]
  rfl

end Scalar

/-- Select the first successful matching case, preserving the comparison's
error and state at every prefix. -/
def switchCasesPre (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (value : Value) (otherwise : BasicBlockId) (post : BasicBlockId → State → Prop)
    (onError : Errors) : List SwitchTarget → State → Prop
  | [], state => post otherwise state
  | .Case bits target :: rest, state =>
    RvalueWP.actionPre (compareCase config limits choice value bits)
      (fun passed after =>
        if passed then post target after
        else switchCasesPre config limits choice value otherwise post onError rest after) onError state

theorem switchCasesPre_iff (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (value : Value) (otherwise : BasicBlockId) (post : BasicBlockId → State → Prop)
    (onError : Errors) (cases : List SwitchTarget) (state : State) :
    switchCasesPre config limits choice value otherwise post onError cases state ↔
      InstructionWP.switchCasesPre (ExecutionMachine.terminatorHooks config limits) choice value
        otherwise post onError cases state := by
  induction cases generalizing state with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | Case bits target =>
      simp only [switchCasesPre, InstructionWP.switchCasesPre, ← compareCase_eq]
      let run := (ExecutionMachine.terminatorHooks config limits).compareSwitchCase choice value bits
      change RvalueWP.actionPre (EffectSpecs.toEffect run) _ _ state ↔
        InstructionWP.resultPre _ _ (run state)
      unfold EffectSpecs.toEffect RvalueWP.actionPre InstructionWP.resultPre
      dsimp only
      generalize run state = result
      rcases result with ⟨after, outcome⟩
      cases outcome with
      | error => rfl
      | ok passed =>
        cases passed
        · exact ih after
        · rfl

/-- Run the canonical discriminant read and branch to the first matching
target or the default target. -/
def switchPre (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (operand : Operand) (targets : SwitchTargets) (post : State → Prop) (onError : Errors)
    (state : State) : Prop :=
  RvalueWP.actionPre (readOperand config limits choice operand)
    (fun value after => switchCasesPre config limits choice value targets.otherwise
      (fun target => InstructionWP.jumpPre target post onError) onError targets.cases.toList after)
    onError state

theorem switchPre_iff (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (operand : Operand) (targets : SwitchTargets) (post : State → Prop) (onError : Errors)
    (state : State) :
    switchPre config limits choice operand targets post onError state ↔
      InstructionWP.switchPre (ExecutionMachine.terminatorHooks config limits) choice operand targets
        post onError state := by
  unfold switchPre InstructionWP.switchPre RvalueWP.actionPre
  have readEq : (ExecutionMachine.terminatorHooks config limits).evalDiscriminant choice operand =
      MachineHooks.run (readOperand config limits choice operand) := rfl
  rw [readEq]
  unfold MachineHooks.run Call.run
  cases readOperand config limits choice operand state
  · exact switchCasesPre_iff _ _ _ _ _ _ _ _ _
  · rfl

end Miri.Verification.BranchControlWP

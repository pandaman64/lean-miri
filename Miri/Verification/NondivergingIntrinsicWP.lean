import Miri.Verification.CanonicalStepWP

/-! Continuations for nondiverging MIR statement intrinsics. -/
namespace Miri.Verification.NondivergingIntrinsicWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Std.WP
open RvalueWP (actionPre actionPre_bind_fun scalarCheckPre)

variable {P S C A : Type}

private def liftCheck (result : Except StepError A) : RvalueM S A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

private theorem liftCheck_pre (result : Except StepError A)
    (post : A → S → Prop) (onError : StepError → S → Prop) :
    actionPre (liftCheck result) post onError = scalarCheckPre result post onError := by
  cases result <;> rfl

/-- Read an immediate, then convert its scalar result without losing the
state reached by the read. -/
def readPre (hooks : MemoryIntrinsicHooks P S C) (choice : C) (operand : OpTy P)
    (convert : Scalar P → Except StepError A) (post : A → S → Prop)
    (onError : StepError → S → Prop) : S → Prop :=
  actionPre (hooks.readImmediate choice operand) (fun value =>
    scalarCheckPre (value.imm.toScalar.mapError ScalarOps.immediateError) (fun scalar =>
      scalarCheckPre (convert scalar) post onError) onError) onError

/-- Check the copy count and size, read pointers, and check both alignments
before calling the checked memory copy. A zero count takes the same path. -/
def copyPre [PointerProvenance P] (hooks : MemoryIntrinsicHooks P S C) (choice : C)
    (source dest count : OpTy P) (nonoverlap : Bool) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) : S → Prop :=
  readPre hooks choice count
    (fun scalar => scalar.toTargetUsize (Size.fromBits hooks.target.pointerWidth.bits)
      |>.mapError ScalarOps.scalarError)
    (fun count => actionPre (hooks.pointeeType choice source.layout.ty) (fun ty =>
      actionPre (hooks.layoutOf choice ty) (fun layout state =>
        match IntegerOps.computeSizeInBytes layout.layout.size count hooks.maxSizeOfVal with
        | none => onError (.undefinedBehavior "overflow computing total size of copy") state
        | some size =>
          let toPointer := fun scalar : Scalar P =>
            scalar.toPointer hooks.target |>.mapError ScalarOps.scalarError
          readPre hooks choice source toPointer (fun source =>
            readPre hooks choice dest toPointer (fun dest =>
              actionPre (hooks.checkAlign choice source layout.layout.align.abi) (fun _ =>
                actionPre (hooks.checkAlign choice dest layout.layout.align.abi) (fun _ =>
                  actionPre (hooks.memCopy choice source dest size nonoverlap) post onError)
                  onError) onError) onError) onError state) onError) onError)
    onError

theorem copyPre_eq [PointerProvenance P] (hooks : MemoryIntrinsicHooks P S C) (choice : C)
    (source dest count : OpTy P) (nonoverlap : Bool) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) :
    copyPre hooks choice source dest count nonoverlap post onError =
      actionPre (Intrinsics.copyWith hooks choice source dest count nonoverlap) post onError := by
  unfold Intrinsics.copyWith
  change _ = actionPre (do
    let read := fun operand => do
      let value ← hooks.readImmediate choice operand
      liftCheck (value.imm.toScalar.mapError ScalarOps.immediateError)
    let count ← liftCheck ((← read count).toTargetUsize (Size.fromBits hooks.target.pointerWidth.bits)
      |>.mapError ScalarOps.scalarError)
    let ty ← hooks.pointeeType choice source.layout.ty
    let layout ← hooks.layoutOf choice ty
    let some size := IntegerOps.computeSizeInBytes layout.layout.size count hooks.maxSizeOfVal
      | throw (.undefinedBehavior "overflow computing total size of copy")
    let source ← liftCheck ((← read source).toPointer hooks.target |>.mapError ScalarOps.scalarError)
    let dest ← liftCheck ((← read dest).toPointer hooks.target |>.mapError ScalarOps.scalarError)
    hooks.checkAlign choice source layout.layout.align.abi
    hooks.checkAlign choice dest layout.layout.align.abi
    hooks.memCopy choice source dest size nonoverlap) post onError
  simp only [copyPre, readPre, actionPre_bind_fun, liftCheck_pre]
  congr 1
  funext value
  congr 1
  funext scalar
  congr 1
  funext count
  congr 1
  funext ty
  congr 1
  funext layout state
  cases IntegerOps.computeSizeInBytes layout.layout.size count hooks.maxSizeOfVal
  · rfl
  · simp only [actionPre_bind_fun, liftCheck_pre]

/-- The exact nondiverging intrinsic cases, with operand evaluation and
subsequent scalar checks in their original order. -/
def evalPre [PointerProvenance P] (hooks : MemoryIntrinsicHooks P S C)
    (evalOperand : C → Operand → RvalueM S (OpTy P)) (choice : C)
    (intrinsic : NonDivergingIntrinsic) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) : S → Prop :=
  match intrinsic with
  | .Assume condition =>
    actionPre (evalOperand choice condition) (fun operand =>
      readPre hooks choice operand (fun scalar => scalar.toBool.mapError ScalarOps.scalarError)
        (fun condition state =>
          if condition then post () state else onError (.undefinedBehavior "assume called with false") state)
        onError) onError
  | .CopyNonOverlapping args =>
    actionPre (evalOperand choice args.source) (fun source =>
      actionPre (evalOperand choice args.destination) (fun dest =>
        actionPre (evalOperand choice args.count) (fun count =>
          copyPre hooks choice source dest count true post onError) onError) onError) onError

theorem evalPre_eq [PointerProvenance P] (hooks : MemoryIntrinsicHooks P S C)
    (evalOperand : C → Operand → RvalueM S (OpTy P)) (choice : C)
    (intrinsic : NonDivergingIntrinsic) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) :
    evalPre hooks evalOperand choice intrinsic post onError =
      actionPre (Intrinsics.evalNondivergingWith hooks evalOperand choice intrinsic) post onError := by
  cases intrinsic with
  | CopyNonOverlapping args =>
    simp only [evalPre, Intrinsics.evalNondivergingWith, actionPre_bind_fun, copyPre_eq]
  | Assume condition =>
    unfold Intrinsics.evalNondivergingWith
    change _ = actionPre (do
      let operand ← evalOperand choice condition
      let value ← hooks.readImmediate choice operand
      let scalar ← liftCheck (value.imm.toScalar.mapError ScalarOps.immediateError)
      let condition ← liftCheck (scalar.toBool.mapError ScalarOps.scalarError)
      if !condition then throw (.undefinedBehavior "assume called with false")) post onError
    simp only [evalPre, readPre, actionPre_bind_fun, liftCheck_pre]
    congr 1
    funext operand
    congr 1
    funext value
    congr 1
    funext scalar
    congr 1
    funext condition state
    cases condition <;> rfl

theorem wp_copy [PointerProvenance P]
    (hooks : MemoryIntrinsicHooks P S C) (choice : C) (source dest count : OpTy P)
    (nonoverlap : Bool) (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    wp (Intrinsics.copyWith hooks choice source dest count nonoverlap) post onError =
      copyPre hooks choice source dest count nonoverlap post onError := by
  rw [copyPre_eq, RvalueWP.actionPre_eq_wp]

theorem wp_eval [PointerProvenance P]
    (hooks : MemoryIntrinsicHooks P S C) (evalOperand : C → Operand → RvalueM S (OpTy P))
    (choice : C) (intrinsic : NonDivergingIntrinsic) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) :
    wp (Intrinsics.evalNondivergingWith hooks evalOperand choice intrinsic) post onError =
      evalPre hooks evalOperand choice intrinsic post onError := by
  rw [evalPre_eq, RvalueWP.actionPre_eq_wp]

section Canonical

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

/-- Reduce the production statement rule to the intrinsic checks followed by
the driver's statement completion check. -/
theorem statementPre_intrinsic
    (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (intrinsic : NonDivergingIntrinsic) (post : Bool → State → Prop)
    (onError : StepError → State → Prop) (before : State) :
    CanonicalStepWP.statementPre config limits choice (.Intrinsic intrinsic) post onError before =
      let checked := ExecutionMachine.withValidation config limits
      evalPre (ExecutionMachine.memoryIntrinsicHooks checked)
        (fun c operand => OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) c operand none)
        choice intrinsic
        (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError)
        onError before := by
  simp only [CanonicalStepWP.statementPre, wp_eval]

end Canonical

macro "miri_nondiverging_intrinsic_wp" : tactic =>
  `(tactic| simp only [statementPre_intrinsic, wp_eval, wp_copy, evalPre, copyPre, readPre,
    EffectSpecs.canonical_intrinsic_copy])

end Miri.Verification.NondivergingIntrinsicWP

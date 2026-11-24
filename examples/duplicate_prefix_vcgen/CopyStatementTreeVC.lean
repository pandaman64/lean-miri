import Representative
import Miri.Verification.CopyTreeWP

/-! The selected copy statement from the generated duplicate_prefix input. -/
namespace DuplicatePrefix.CopyStatementTreeVC

open Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.Verification Std.WP

set_option maxRecDepth 65536

private def copyBody : Option Body :=
  GeneratedBodySafety.input.document.bodies[5]?.map (·.mir)

private def statementKindAt (body : Body) : Option StatementKind :=
  match body.basicBlocks[7]? with
  | none => none
  | some block => block.statements[8]?.map (·.kind)

private def statementKind : Option StatementKind :=
  copyBody.bind statementKindAt

private def copyArgs : CopyNonOverlapping :=
  ⟨.Move ⟨14, #[]⟩, .Move ⟨15, #[]⟩, .Move ⟨16, #[]⟩⟩

theorem selected_statement :
    statementKind = some (.Intrinsic (.CopyNonOverlapping copyArgs)) := rfl

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U

/-- The emitted operands and the exact tree-aware copy continuation. -/
def loweredPre
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (post : Bool → State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  let checked := ExecutionMachine.withValidation config limits
  let eval := fun operand =>
    OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) choice operand none
  RvalueWP.actionPre (eval (.Move ⟨14, #[]⟩)) (fun source =>
    RvalueWP.actionPre (eval (.Move ⟨15, #[]⟩)) (fun dest =>
      RvalueWP.actionPre (eval (.Move ⟨16, #[]⟩)) (fun count =>
        NondivergingIntrinsicWP.copyPreUsing (ExecutionMachine.memoryIntrinsicHooks checked)
          (fun source dest size nonoverlap =>
            CopyTreeWP.copyPre checked.access checked.addresses checked.arithmetic source dest size 1 nonoverlap)
          choice source dest count true
          (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError)
          onError) onError) onError) onError before

/-- The selected statement's VC through the concrete operand, layout,
alignment and memory-copy rules. Both permission checks remain in the VC
at their actual machine states. -/
theorem statement_vc
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (post : Bool → State → Prop) (onError : StepError → State → Prop) (before : State) :
    (match statementKind with
    | none => False
    | some kind => CanonicalStepWP.statementPre config limits choice kind post onError before) =
    loweredPre config limits choice post onError before := by
  rw [selected_statement]
  simp only [copyArgs, loweredPre]
  miri_copy_tree_wp

set_option experimental.vcgen true in
/-- Starting at the imported helper's copy statement, the canonical driver
requires the lowered continuation for every permitted choice. -/
theorem step_vc
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (before : State)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame) (pc : frame.location = .mir ⟨7, 8⟩)
    (imported : copyBody = some frame.body)
    (checked : ∀ choice, allowed before choice → loweredPre config limits choice post onError before) :
    Triple (StepWP.OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits) (allowed := allowed))
      (· = before) post onError := by
  vcgen
  rename_i state atEntry
  subst state
  intro choice permitted
  have kind : statementKindAt frame.body = some (.Intrinsic (.CopyNonOverlapping copyArgs)) := by
    simpa only [statementKind, imported, Option.bind_some] using selected_statement
  cases selected : frame.body.basicBlocks[7]? with
  | none => simp [statementKindAt, selected] at kind
  | some block =>
    cases slot : block.statements[8]? with
    | none => simp [statementKindAt, selected, slot] at kind
    | some statement =>
      simp only [statementKindAt, selected, slot, Option.map_some, Option.some.injEq] at kind
      simp only [CanonicalStepWP.choicePre, StepWP.driverChoicePreWith, current, pc, selected, slot, kind]
      have lowered := statement_vc config limits choice post onError before
      rw [selected_statement] at lowered
      exact (Eq.mpr lowered) (checked choice permitted)

#print axioms selected_statement
#print axioms statement_vc
#print axioms step_vc

end DuplicatePrefix.CopyStatementTreeVC

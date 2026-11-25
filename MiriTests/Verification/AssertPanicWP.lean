import Miri.Verification.AssertPanicWP

/-! The selected assertion propagates a failing diagnostic operand read. -/
namespace MiriTests.Verification.AssertPanicWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- A failed bounds assertion reads index before length. An error evaluating
length reaches the original error continuation, before resolving a lang item. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before ready tested indexEval indexRead failed : State) (frame : Frame)
    (loc : Location) (block : BasicBlock)
    (condition len index : Operand) (layout : LocalLayout) (target : BasicBlockId)
    (unwind : UnwindAction) (indexValue : OpTy Provenance) (value : RvalueImmTy Provenance)
    (error : StepError) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (noStatement : block.statements[loc.statementIndex]? = none)
    (kind : block.terminator.kind = .Assert condition true (.BoundsCheck len index) target unwind)
    (prepared : TerminatorMachine.beforeTerminatorWithChoice
      (ExecutionMachine.withValidation config limits).terminators
      ((ExecutionMachine.withValidation config limits).preemptionChoice ()) before = .ok () ready)
    (readCondition : BranchControlWP.readOperand config limits () condition ready =
      .ok ⟨.scalar (.fromBool false), layout⟩ tested)
    (evaluateIndex : (AssertPanicWP.canonicalHooks config limits).evalOperand () index tested =
      .ok indexValue indexEval)
    (readIndex : (AssertPanicWP.canonicalHooks config limits).driver.readImmediate () indexValue indexEval =
      .ok value indexRead)
    (evaluateLength : (AssertPanicWP.canonicalHooks config limits).evalOperand () len indexRead =
      .error error failed)
    (accept : onError error failed) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [CanonicalStepWP.choicePre, StepWP.driverChoicePreWith,
    current, position, selected, noStatement, CanonicalStepWP.terminatorPre,
    wp, WP.wpTrans, prepared]
  generalize block.terminator = term at kind ⊢
  obtain ⟨info, original⟩ := term
  change original = .Assert condition true (.BoundsCheck len index) target unwind at kind
  subst original
  miri_assert_panic_wp
  simp only [CanonicalStepWP.canonical_assertConditionPre, RvalueWP.actionPre,
    readCondition, BranchControlWP.readBool_scalar, RvalueWP.scalarCheckPre,
    ControlFlow.isOptionalOverflowCheck, Bool.and_false, evaluateIndex, readIndex, evaluateLength]
  exact accept

/-- The unwind-termination call loads the resolved instance before preparing
its return place. A failed load reaches the existing error continuation. -/
example (config : Config) (limits : ExecutionMachine.Limits) (info : SourceInfo)
    (reason : UnwindTerminateReason) (before resolved failed : State) (callee : CallInstance)
    (error : StepError) (post : State → Prop) (onError : StepError → State → Prop)
    (lookup : (ExecutionMachine.withValidation config limits).unwindTerminateFunction () reason before =
      .ok callee resolved)
    (missingMir : (ExecutionMachine.withValidation config limits).helpers.loadMir () callee resolved =
      .error error failed)
    (accept : onError error failed) :
    CanonicalStepWP.selectedTerminatorPre config limits () ⟨info, .UnwindTerminate reason⟩
      post onError before := by
  miri_assert_panic_wp
  simpa only [RvalueWP.actionPre, lookup, ExecutionCalls.helpers, missingMir] using accept

end MiriTests.Verification.AssertPanicWP

import Representative
import Miri.Interpreter.Aggregate
import Miri.Interpreter.ConstantMachine

namespace DuplicatePrefix.LanguageGuardPrepare
open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

private def emptyTuple : Rvalue := .Aggregate .Tuple #[]

/-- The emitted language-check helper initializes unit temporary 2 with an
empty tuple before calling the runtime guard. -/
theorem languageGuardUnitAssignment :
    (do
      let source ← GeneratedBodySafety.input.document.bodies[9]?
      let block ← source.mir.basicBlocks[0]?
      pure (← block.statements[2]?).kind) = some (.Assign ⟨2, #[]⟩ emptyTuple) := by rfl

omit [DecidableEq K] in
theorem writeUnitDiscriminant (hooks : DiscriminantHooks Provenance State C (RuntimePlace Provenance))
    (choice : C) (before : State) (discrLayout : LocalLayout) (destination : RuntimePlace Provenance) (operand : OpTy Provenance)
    (destLayout : hooks.destLayout destination = destination.layout)
    (operandLayout : operand.layout = destination.layout)
    (single : destination.layout.layout.variants = .Single 0)
    (inhabited : destination.layout.layout.isUninhabited = false)
    (variant : destination.layout.layout.isVariantUninhabited 0 = false)
    (toOp : hooks.toOp choice destination before = .ok operand before)
    (layout : hooks.discriminantLayout choice destination.layout.ty before = .ok discrLayout before) :
    Discriminant.writeDiscriminant hooks choice 0 destination before = .ok () before := by
  simp [Discriminant.writeDiscriminant, Discriminant.tagForVariant, Discriminant.readDiscriminant,
    destLayout, operandLayout, single, inhabited, variant, toOp, layout, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]

omit [DecidableEq K] in
theorem writeEmptyTuple (hooks : AggregateHooks Provenance State C (RuntimePlace Provenance))
    (choice : C) (destination : RuntimePlace Provenance) (before : State) :
    writeAggregate hooks choice .Tuple #[] destination before =
      ((do
        hooks.writeDiscriminant choice 0 destination
        if ← hooks.enforceValidity choice (hooks.placeLayout destination) then
          hooks.validate choice destination) : MachineHooks.M K U Unit) before := by
  simp [writeAggregate, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

theorem prepareEmptyTuple
    (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (before prepared : State) (destination : RuntimePlace Provenance)
    (placed : (ExecutionMachine.rvalueHooks config limits).evalPlace choice ⟨2, #[]⟩ true before =
      .ok destination prepared) :
    let bound := ExecutionMachine.withValidation config limits
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) choice emptyTuple ⟨2, #[]⟩ before =
      ((do
        Discriminant.writeDiscriminant (ExecutionMachine.discriminantHooks bound) choice 0 destination
        if ← bound.compiler.enforceValidity choice destination.layout then
          bound.compiler.validate choice destination) : MachineHooks.M K U Unit) prepared := by
  intro bound
  simp only [evalRvalueIntoPlace, bind, Bind.bind, EStateM.bind, placed, emptyTuple]
  change writeAggregate _ choice .Tuple #[] destination prepared = _
  rw [writeEmptyTuple]
  rfl

private def falseConstant : ConstOperand :=
  ⟨⟨212⟩, none, .Val (.Scalar (.Int 0 1)) 0⟩

theorem languageGuardFalseAssignment :
    (do
      let source ← GeneratedBodySafety.input.document.bodies[9]?
      let block ← source.mir.basicBlocks[3]?
      pure (← block.statements[0]?).kind) =
        some (.Assign ⟨0, #[]⟩ (.Use (.Constant falseConstant) .Yes)) := by rfl

omit [DecidableEq K] in
theorem guardFalseConstant (runtime : Miri.Input.RuntimeMetadata)
    (functions : FunctionPointers.Hooks K U O) (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M K U (Pointer Provenance))
    (error : ConstantError → StepError) (layout : LocalLayout) (state : State) :
    ConstantMachine.evalOperandWithLayout runtime functions arithmetic externStatic error
      falseConstant (some layout) none state =
      .ok ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ state := by
  cases state
  rfl

omit [DecidableEq K] in
theorem sameLayoutCopyWithoutTransmute (place : PlaceHooks Provenance State C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance State C) (choice : C) (source : OpTy Provenance)
    (destination : RuntimePlace Provenance) (live : copy.compatible source.layout destination.layout = .ok true) :
    copyRuntimePlace place copy choice source destination false =
      copyRuntimePlace place copy choice source destination true := by
  funext state
  simp [copyRuntimePlace, copyRuntimePlaceNoValidate, placeLift_ok, live,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

omit [DecidableEq K] in
private theorem defaultRetagScope (action : MachineHooks.M K U Unit) (before after : State)
    (tracker : MachineHooks.BorrowState) (tracked : before.machine.borrowTracker = some tracker)
    (afterTracker : after.machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default) (effect : action before = .ok () after) :
    MachineHooks.withRetagMode .Default action before = .ok () after := by
  have entered : {before with machine := {before.machine with
    borrowTracker := some {tracker with retagMode := .Default}}} = before := by rw [← mode, ← tracked]
  unfold MachineHooks.withRetagMode
  rw [tracked]
  dsimp only
  rw [entered, effect]
  simp only [afterTracker]
  change EStateM.Result.ok () {after with machine := {after.machine with
    borrowTracker := some tracker}} = EStateM.Result.ok () after
  rw [← afterTracker]

theorem prepareGuardFalse
    (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (before prepared after : State) (destination : RuntimePlace Provenance)
    (placed : (ExecutionMachine.rvalueHooks config limits).evalPlace choice ⟨0, #[]⟩ true before =
      .ok destination prepared)
    (constant : (ExecutionMachine.rvalueHooks config limits).evalOperand choice (.Constant falseConstant)
      (some destination.layout) prepared =
        .ok ⟨.immediate (.scalar (Scalar.fromBool false)), destination.layout⟩ prepared)
    (tracker : MachineHooks.BorrowState) (tracked : prepared.machine.borrowTracker = some tracker)
    (afterTracker : after.machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (copied : let bound := ExecutionMachine.withValidation config limits
      copyRuntimePlace config.projection.place bound.copy choice
        ⟨.immediate (.scalar (Scalar.fromBool false)), destination.layout⟩ destination false prepared =
          .ok () after) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) choice
      (.Use (.Constant falseConstant) .Yes) ⟨0, #[]⟩ before = .ok () after := by
  simp only [evalRvalueIntoPlace, bind, Bind.bind, EStateM.bind, placed]
  have layout : (ExecutionMachine.rvalueHooks config limits).placeLayout destination = destination.layout := rfl
  rw [layout]
  rw [constant]
  exact defaultRetagScope _ prepared after tracker tracked afterTracker mode copied

end DuplicatePrefix.LanguageGuardPrepare

#print axioms DuplicatePrefix.LanguageGuardPrepare.writeUnitDiscriminant
#print axioms DuplicatePrefix.LanguageGuardPrepare.prepareEmptyTuple
#print axioms DuplicatePrefix.LanguageGuardPrepare.guardFalseConstant
#print axioms DuplicatePrefix.LanguageGuardPrepare.sameLayoutCopyWithoutTransmute

#print axioms DuplicatePrefix.LanguageGuardPrepare.prepareGuardFalse

import duplicate_prefix.LanguageGuardCurrentFacts
import duplicate_prefix.BoolSwitch
import duplicate_prefix.RootScalarQueries
import duplicate_prefix.RootLocalStages
import duplicate_prefix.LocalOperands
import duplicate_prefix.RootGenericBoolWrite

namespace DuplicatePrefix.LanguageGuardCurrentSwitch
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

inductive Site where
  | languageGuard
  | pointerAdd

noncomputable def bodyAt : Site → Miri.MIR.Body
  | .languageGuard => LanguageGuardCurrentFacts.parentBody.body
  | .pointerAdd => PointerAddCurrentFacts.body.body

def controlIndex : Site → Nat
  | .languageGuard => 1
  | .pointerAdd => 0

def booleanSlot : Site → Miri.MIR.LocalId
  | .languageGuard => 1
  | .pointerAdd => 4

def falseBlock : Site → BasicBlockId
  | .languageGuard => 3
  | .pointerAdd => 5

theorem takeFalse
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (site : Site) (body : frame.body = bodyAt site)
    (located : frame.location = .mir ⟨1, controlIndex site⟩)
    (valid : booleanSlot site < frame.locals.size)
    (live : frame.locals[booleanSlot site].value = .live (.immediate (.scalar (.fromBool false))))
    (cached : frame.locals[booleanSlot site].layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl
      machine.user).gcInterval = 0) :
    let config := PreparedContracts.actualConfig options () remaining span
    let before := Storage.withCurrent older frame machine
    ExecutionMachine.step config limits () before =
      (Storage.withCurrent older {frame with location := .mir ⟨falseBlock site, 0⟩}
        (SourceControl.accounted config.terminators before).machine, .ok true) := by
  intro config before
  let afterTick := SourceControl.accounted config.terminators before
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let value : Scalar Provenance := .fromBool false
  let op : OpTy Provenance := ⟨.immediate (.scalar value), RootCompilerFacts.boolLayout⟩
  have accounting := SourceControl.before_terminator config limits () before
    (CanonicalConfigFacts.actual_term_get_set options () remaining span)
    (CanonicalConfigFacts.actual_term_set_set options () remaining span) unchecked noGc fixed
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have accountedGhost : afterTick.machine.user.payload.ghost = false := by
    change (config.terminators.setControl (TerminatorClock.advance
      (config.terminators.getControl machine.user)) machine.user).payload.ghost = false
    rw [fields.terminators]
    exact ghost
  have getter : hooks.compiler.validationInProgress afterTick = .ok false afterTick := by
    change config.compiler.validationInProgress afterTick = _
    rw [fields.compilerValidationInProgress]
    simp [ValidityMachine.validationInProgress, accountedGhost,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have sized : RootCompilerFacts.boolLayout.layout.backendRepr.isUnsized = false := by decide +kernel
  have read := LocalOperands.cached_immediate hooks () older frame afterTick.machine (booleanSlot site)
    (.scalar value) RootCompilerFacts.boolLayout none valid live cached sized noClocks false getter
  have check := RootLocalStages.operand_check_skipped options limits () remaining span debug
    (OperandDispatch.wholeLocal (booleanSlot site)) op afterTick
  have operand := OperandDispatch.evalOperandAt_move_wholeLocal hooks ()
    (booleanSlot site) none afterTick afterTick op read check
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.boolLayout RootGenericBoolWrite.bool_initialized
  have scalar := RootLocalStages.canonical_read_scalar options limits remaining span afterTick
    value RootCompilerFacts.boolLayout ⟨primitive, range, repr⟩
  let discr := Operand.Move (OperandDispatch.wholeLocal (booleanSlot site))
  have discriminant : MachineHooks.run (do
      let value ← OperandMachine.evalOperand hooks () discr none
      PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access value) afterTick =
      (afterTick,.ok (ScalarOperations.boolImmediate false RootCompilerFacts.boolLayout)) := by
    change MachineHooks.run (do
      let value ← OperandMachine.evalOperand hooks () discr none
      (ExecutionMachine.rvalueHooks config limits).readImmediate () value) afterTick = _
    simp only [MachineHooks.run, Call.run, Bind.bind, EStateM.bind, discr]
    rw [operand]
    exact congrArg (fun result => match result with
      | .ok value after => (after,Except.ok value)
      | .error error after => (after,Except.error error)) scalar
  have blockBound : 1 < (bodyAt site).basicBlocks.size := by
    cases site <;> with_unfolding_all decide +kernel
  let block := (bodyAt site).basicBlocks[1]'blockBound
  have blockAt : frame.body.basicBlocks[1]? = some block := by simp [body, block, blockBound]
  have exhausted : block.statements[controlIndex site]? = none := by
    cases site <;> with_unfolding_all rfl
  have kind : block.terminator.kind = .SwitchInt discr ⟨#[.Case 0 (falseBlock site)],2⟩ := by
    cases site <;> with_unfolding_all rfl
  have classification := RootScalarQueries.bool_classification options remaining span limits
  have boolLayout := RootScalarQueries.bool_layout options remaining span limits
  have width : RootCompilerFacts.boolLayout.layout.size = Size.ofBytes 1 := by decide +kernel
  have dispatch := BoolSwitch.dispatch config limits () block.terminator discr (falseBlock site) 2
    afterTick afterTick RootCompilerFacts.boolLayout false kind discriminant classification boolLayout width
  let after := Storage.withCurrent older {frame with location := .mir ⟨falseBlock site, 0⟩} afterTick.machine
  have effect : (ExecutionMachine.stepHooks config limits).terminator () block.terminator afterTick =
      (after,.ok ()) := by
    rw [dispatch]
    simp [after, afterTick, SourceControl.accounted, before, Storage.withCurrent,
      ControlFlow.goToBlock, ControlFlow.setLocation, Stack.currentFrame?]
  exact StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) () before afterTick after
    frame ⟨1,controlIndex site⟩ block (by simp [before, Storage.withCurrent, Stack.currentFrame?])
    located blockAt exhausted accounting effect

end DuplicatePrefix.LanguageGuardCurrentSwitch

#print axioms DuplicatePrefix.LanguageGuardCurrentSwitch.takeFalse

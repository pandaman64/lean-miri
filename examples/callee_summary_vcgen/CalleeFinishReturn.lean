import CalleeReturn

namespace CalleeSummaryReflected
open Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.Verification PointerObservation.Fixture

set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option cbv.maxSteps 85000
set_option pp.maxSteps 350
set_option pp.deepTerms false
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert
attribute [local cbv_opaque] ValidityVisitor.visit ValidityVisitor.validatePlace
attribute [local cbv_eval] ValidityVisitor.validatePlace_shallow

theorem copyValidityReflected (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    match expectedCopied with
    | .ok (config, after, frame) =>
        let dest := frame.returnPlace.toRuntimePlace
        let validated := ExecutionMachine.withValidation config limits
        let hooks := (ExecutionMachine.projectionHooks validated).place
        RvalueWP.actionPre (hooks.enforceValidity () dest.layout) (fun enabled =>
          if enabled then RvalueWP.actionPre (hooks.validate () dest) post onError
          else post ()) onError after = post () after
    | .error _ => False := by
  conv => cbv
  conv =>
    pattern (ValidityVisitor.visit _ _ 32 _ _ _)
    tactic =>
      refine ValidityVisitor.visit_integer (P := Provenance) _ _ 31 _ _ _ ?value ?layout ?classified ?read ?clear ?ranges
      case classified => cbv <;> rfl
      case read => cbv <;> rfl
      case clear => cbv <;> rfl
      case ranges => cbv <;> rfl
  conv => cbv
  trivial

private theorem canonicalCopyReturnPre (config : Config) (value : OpTy Provenance)
    (dest : RuntimeStackPlace Provenance) (before after : State)
    (copied : let c := ExecutionMachine.withValidation config limits
      ∀ post onError, PlaceReadWriteWP.copyNoValidatePre (ExecutionMachine.projectionHooks c).place
        c.copy () value dest.toRuntimePlace true post onError before = post () after)
    (sameType : value.layout.ty = dest.toRuntimePlace.layout.ty)
    (check : let c := ExecutionMachine.withValidation config limits
      (ExecutionMachine.projectionHooks c).place.enforceValidity () dest.toRuntimePlace.layout after = .ok true after)
    (valid : let c := ExecutionMachine.withValidation config limits
      (ExecutionMachine.projectionHooks c).place.validate () dest.toRuntimePlace after = .ok () after) :
    (ExecutionMachine.terminatorHooks config limits).copyReturn () value dest before = (after, .ok ()) := by
  let c := ExecutionMachine.withValidation config limits
  let hooks := (ExecutionMachine.projectionHooks c).place
  let action := copyRuntimePlace hooks c.copy () value dest.toRuntimePlace true
  have check' : hooks.enforceValidity () dest.toRuntimePlace.layout after = .ok true after := check
  have valid' : hooks.validate () dest.toRuntimePlace after = .ok () after := valid
  have post : RvalueWP.actionPre action (fun _ returned => returned = after) (fun _ _ => False) before := by
    dsimp only [action]
    rw [PlaceReadWriteWP.actionPre_copyRuntimePlace]
    unfold PlaceReadWriteWP.copyPre
    rw [copied]
    simp only [RvalueWP.actionPre_ok check', ↓reduceIte, sameType, bne_self_eq_false, Bool.false_eq_true,
      RvalueWP.actionPre_ok valid']
  change MachineHooks.run action before = _
  cases ran : action before with
  | error error actual =>
    simp only [RvalueWP.actionPre, ran] at post
  | ok value actual =>
    cases value
    simp only [RvalueWP.actionPre, ran] at post
    rw [post] at ran
    simp only [MachineHooks.run, Call.run, ran]



abbrev CalleeFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra

private theorem normalReturnPre (hooks : ControlHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState MiriMemoryKind EmptyFunction.Configuration.RootUser) Unit (OpTy Provenance)) (before read popped copied cleaned : State)
    (frame : CalleeFrame) (loc : Location) (block : BasicBlock) (value : OpTy Provenance)
    (target : BasicBlockId) (unwind : UnwindAction)
    (post : State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (pc : frame.location = .mir loc)
    (found : frame.body.basicBlocks[loc.block]? = some block)
    (notCleanup : block.cleanup = false)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (readReturn : hooks.returnOperand () before = (read, .ok value))
    (popRaw : hooks.popFrame () read = (popped, .ok frame))
    (copyBack : hooks.copyReturn () value frame.returnPlace popped =
      (copied, .ok ()))
    (cleanup : hooks.cleanupFrame () false frame copied =
      (cleaned, .ok .normal)) :
    InstructionWP.returnPre hooks () false post onError before ↔
      InstructionWP.jumpPre target post onError cleaned := by
  unfold InstructionWP.returnPre InstructionWP.returnPreWithEffects
  simp only [current, pc, found, notCleanup, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    readReturn, InstructionWP.resultPre, popRaw, copyBack, cleanup,
    InstructionWP.finishReturnPre, continuation]



private theorem returnAfterPrehook (config : Config) (before ready : State)
    (term : Terminator) (kind : term.kind = .Return)
    (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (hook : (ExecutionMachine.stepHooks config limits).beforeTerminator () before = (ready, .ok ())) :
    BodyCFG.nodePre config limits () post onError before (.terminator term) ↔
      CanonicalStepWP.returnPre config limits () false (post true) onError ready := by
  change CanonicalStepWP.terminatorPre config limits () term post onError before ↔ _
  unfold CanonicalStepWP.terminatorPre
  dsimp only
  rw [← RvalueWP.actionPre_eq_wp, RvalueWP.actionPre_run]
  change InstructionWP.resultPre _ _ ((ExecutionMachine.stepHooks config limits).beforeTerminator () before) ↔ _
  rw [hook]
  change CanonicalStepWP.selectedTerminatorPre config limits () term (post true) onError ready ↔ _
  simp only [CanonicalStepWP.selectedTerminatorPre, InstructionWP.terminatorPreWithReturn, kind]


private theorem effectFromPre (action : RvalueM State Unit) (before after : State)
    (checked : RvalueWP.actionPre action (fun _ next => next = after) (fun _ _ => False) before) :
    action before = .ok () after := by
  cases run : action before with
  | error error state => simp only [RvalueWP.actionPre, run] at checked
  | ok value state =>
    cases value
    simp only [RvalueWP.actionPre, run] at checked
    rw [checked]

open GeneratedBodySafety

theorem returnConfigs :
    match returnEntry, returnReady, expectedPop, expectedCopied, expectedResume with
    | .ok (cfg, _), .ok (ready, _), .ok (pop, _, frame), .ok (copied, _, detached), .ok (resumed, _) =>
      cfg = ready ∧ cfg = pop ∧ cfg = copied ∧ cfg = resumed ∧ detached = frame
    | _, _, _, _, _ => False := by
  conv => cbv
  trivial

theorem jumpReflected :
    match expectedCopied, expectedResume with
    | .ok (_, after, _), .ok (_, resumed) => ControlFlow.goToBlock 1 after = (resumed, .ok ())
    | _, _ => False := by
  conv => cbv
  trivial


/-- Execute the emitted Return using the staged read, pop, copy and cleanup
equations for the protected callee state. -/
theorem returnStepReflected :
    match returnEntry, expectedResume with
    | .ok (config, before), .ok (_, resumed) =>
      ExecutionMachine.step config limits () before = (resumed, .ok true)
    | _, _ => False := by
  have configurations := returnConfigs
  cases entered : returnEntry with
  | error error => simp only [entered] at configurations
  | ok initial =>
    obtain ⟨config, before⟩ := initial
    cases prepared : returnReady with
    | error error => simp only [entered, prepared] at configurations
    | ok pre =>
      obtain ⟨preConfig, ready⟩ := pre
      cases poppedEq : expectedPop with
      | error error => simp only [entered, prepared, poppedEq] at configurations
      | ok p =>
        obtain ⟨popConfig, popped, frame⟩ := p
        cases copiedEq : expectedCopied with
        | error error => simp only [entered, prepared, poppedEq, copiedEq] at configurations
        | ok c =>
          obtain ⟨copyConfig, copied, detached⟩ := c
          cases resumedEq : expectedResume with
          | error error => simp only [entered, prepared, poppedEq, copiedEq, resumedEq] at configurations
          | ok r =>
            obtain ⟨resumeConfig, resumed⟩ := r
            simp only [entered, prepared, poppedEq, copiedEq, resumedEq] at configurations
            obtain ⟨configReady, configPop, configCopy, configResumed, sameFrame⟩ := configurations
            subst preConfig popConfig copyConfig resumeConfig detached
            have checkedShape := returnShape
            simp only [prepared, poppedEq] at checkedShape
            obtain ⟨current, pc, blockShape, continuation⟩ := checkedShape
            obtain ⟨block, found, blockCleanup⟩ := Option.map_eq_some_iff.mp blockShape
            have cached := sameReturnLayout
            simp only [poppedEq] at cached
            let layout := frame.returnPlace.toRuntimePlace.layout
            let value : OpTy Provenance := ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 7))), layout⟩
            have read := returnReadReflected
            simp only [prepared, current, Option.bind_some, cached] at read
            have pop := returnPopReflected
            simp only [prepared, poppedEq] at pop
            have copy (post : Unit → State → Prop) (onError : StepError → State → Prop) := copyNoValidateReflected post onError
            simp only [poppedEq, copiedEq, cached] at copy
            have enforce := returnCopyEnforced
            simp only [copiedEq] at enforce
            let fail : StepError → State → Prop := fun _ _ => False
            have validation := copyValidityReflected (fun _ next => next = copied) fail
            simp only [copiedEq, RvalueWP.actionPre_ok enforce, ↓reduceIte] at validation
            let checked := ExecutionMachine.withValidation config limits
            have validated : (ExecutionMachine.projectionHooks checked).place.validate
                () frame.returnPlace.toRuntimePlace copied = .ok () copied :=
              effectFromPre _ _ _ (Eq.mpr validation True.intro)
            have copiedRun := canonicalCopyReturnPre config value frame.returnPlace popped copied
              copy rfl enforce validated
            have cleanup := returnCleanupReflected
            simp only [copiedEq] at cleanup
            have jump := jumpReflected
            simp only [copiedEq, resumedEq] at jump
            have hook := prehookRuns config config before ready entered prepared
            have selected := returnSelectedReflected
            simp only [entered] at selected
            have node : ∃ info, mir_1_bb0_2 = .terminator ⟨info, .Return⟩ := ⟨_, rfl⟩
            obtain ⟨info, node⟩ := node
            rw [node] at selected
            let post : Bool → State → Prop := fun more next => more = true ∧ next = resumed
            have result : BodyCFG.nodePre config limits () post fail before (.terminator ⟨info, .Return⟩) := by
              rw [returnAfterPrehook config before ready _ rfl post fail hook, CanonicalStepWP.returnPre_iff]
              rw [normalReturnPre (ExecutionMachine.terminatorHooks config limits).toControlHooks
                ready ready popped copied copied frame ⟨0, 2⟩ block value 1 .Unreachable
                (post true) fail current pc found blockCleanup continuation read pop copiedRun cleanup]
              rw [InstructionWP.jumpPre_iff, jump]
              exact ⟨rfl, rfl⟩
            have stepped := (selectedPre_iff config post fail before _ _ selected).mp result
            rcases ran : ExecutionMachine.step config limits () before with ⟨after, outcome⟩
            rw [ran] at stepped
            cases outcome with
            | error error => exact False.elim stepped
            | ok more =>
              change more = true ∧ after = resumed at stepped
              obtain ⟨rfl, rfl⟩ := stepped
              exact ran

open Lean Elab Command in
run_cmd liftTermElabM do
  for dependency in (← collectAxioms ``returnStepReflected) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "returnStepReflected depends on unapproved axiom {dependency}"

#print axioms returnStepReflected
end CalleeSummaryReflected

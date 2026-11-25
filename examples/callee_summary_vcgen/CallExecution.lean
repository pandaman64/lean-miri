import CallFrameEntry
import CallDispatchHandoff

namespace CalleeSummaryReflected
open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.Verification
open PointerObservation.Fixture

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem continueAfterFrame {A : Type} (action : RvalueM State A) (before : State)
    (post' post : A → State → Prop) (failure : StepError → State → Prop)
    (proved : RvalueWP.actionPre action post failure before)
    (advance : ∀ value after, post value after → post' value after) :
    RvalueWP.actionPre action post' failure before := by
  cases finished : action before with
  | error =>
    exact (by simpa only [RvalueWP.actionPre, finished] using proved)
  | ok value after =>
    simp only [RvalueWP.actionPre, finished] at proved ⊢
    exact advance value after proved

/-- The emitted call evaluates its argument and dispatches to the exact
protected callee entry state through the canonical frame rule. -/
theorem protectedCallNode :
    match atBorrowedCall with
    | .error _ => False
    | .ok (config, _, before) =>
      BodyCFG.nodePre config limits ()
        (fun more after => more = true ∧ matchesUpdateEntry after)
        (fun _ _ => False) before GeneratedBodySafety.mir_0_bb0_7 := by
  have initialized := initActualFrame
  cases entered : atBorrowedCall with
  | error reason => simp only [entered] at initialized
  | ok result =>
    obtain ⟨config, program, before⟩ := result
    simp only [entered] at initialized
    cases foundFrame : before.stack.currentFrame? with
    | none => simp only [foundFrame] at initialized
    | some frame =>
      cases foundBody : program.down.bodies.find? (·.identity.index == 1) with
      | none => simp only [foundFrame, foundBody] at initialized
      | some body =>
        rw [callAbiLiteralResolution] at initialized
        cases foundLocal : frame.getLocal 5 with
        | error error => simp only [foundFrame, foundBody, foundLocal] at initialized
        | ok source =>
          obtain ⟨storage, cached⟩ := source
          cases storage with
          | dead => simp only [foundFrame, foundBody, foundLocal] at initialized
          | live operand =>
            cases cached with
            | none => simp only [foundFrame, foundBody, foundLocal] at initialized
            | some layout =>
              cases foundDest : frame.getLocalLayout 4 with
              | error error => simp only [foundFrame, foundBody, foundLocal, foundDest] at initialized
              | ok output =>
                cases output with
                | none => simp only [foundFrame, foundBody, foundLocal, foundDest] at initialized
                | some destinationLayout =>
                  simp only [foundFrame, foundBody, foundLocal, foundDest] at initialized
                  have foundOperand : frame.getLocalOperand 5 = .ok operand := by
                    rw [Frame.getLocalOperand]
                    simp only [bind, Bind.bind, Except.bind, foundLocal]
                    rfl
                  have foundLayout : frame.getLocalLayout 5 = .ok (some layout) := by
                    rw [Frame.getLocalLayout]
                    simp only [bind, Bind.bind, Except.bind, foundLocal]
                    rfl
                  let checked := ExecutionMachine.withValidation config limits
                  let hooks := ExecutionMachine.callHooks checked limits
                  let preamble := TerminatorMachine.beforeTerminatorWithChoice checked.terminators
                    (checked.preemptionChoice ())
                  change RvalueWP.actionPre preamble _ _ before at initialized
                  cases ran : preamble before with
                  | error error failed =>
                    simp only [RvalueWP.actionPre, ran] at initialized
                  | ok val ready =>
                    cases val
                    have ran' : TerminatorMachine.beforeTerminatorWithChoice checked.terminators
                        (checked.preemptionChoice ()) before = .ok () ready := ran
                    simp only [RvalueWP.actionPre, ran] at initialized
                    let failure : StepError → State → Prop := fun _ _ => False
                    let success := matchesUpdateEntry
                    let selectedPost : State → Prop := fun after =>
                      if (some 1 : Option BasicBlockId).isSome &&
                          after.stack.frames.size == ready.stack.frames.size &&
                          after.stack.currentFrame?.map (·.location) == ready.stack.currentFrame?.map (·.location)
                      then False else success after
                    let finish : State → Prop :=
                      RvalueWP.actionPre hooks.stackIsEmpty (fun empty afterEmpty =>
                        if empty then selectedPost afterEmpty
                        else RvalueWP.actionPre hooks.frameIndex (fun index afterIndex =>
                          if index == 0 then
                            RvalueWP.actionPre hooks.getFrame (fun current afterFrame =>
                              if current.location == frame.location then False else selectedPost afterFrame)
                              failure afterIndex
                          else selectedPost afterIndex) failure afterEmpty) failure
                    let dispatch (dest : RuntimeStackPlace Provenance)
                        (evaluated : EvaluatedCall Provenance Unit ExternAbi (FnAbi TyId)) :=
                      CallWP.dispatchPre hooks () finish failure limits.callDispatch
                        ⟨evaluated.callee, evaluated.callerAbi, evaluated.fnAbi, evaluated.args,
                          evaluated.withCallerLocation, dest, some 1, .Unreachable⟩
                    have handed := emittedCallHandoff dispatch failure
                    have dispatched := emittedDispatchHandoff finish failure
                    simp only [entered, foundFrame, foundBody, foundOperand, foundLayout, foundDest,
                      GeneratedBodySafety.mir_0_bb0_7] at handed dispatched
                    rw [RvalueWP.actionPre_ok ran', RvalueWP.actionPre_ok ran'] at handed
                    rw [RvalueWP.actionPre_ok ran'] at dispatched
                    simp only [BodyCFG.nodePre, GeneratedBodySafety.mir_0_bb0_7,
                      CanonicalStepWP.terminatorPre, ← RvalueWP.actionPre_eq_wp]
                    change RvalueWP.actionPre preamble _ _ before
                    simp only [RvalueWP.actionPre_ok ran, CanonicalStepWP.selectedTerminatorPre,
                      CallWP.callPre, ite_self, true_and]
                    have readyShape := emittedCallPreambleDepth
                    simp only [entered] at readyShape
                    rw [RvalueWP.actionPre_ok ran'] at readyShape
                    have readyFrame : ready.stack.currentFrame? = some frame := by
                      rw [readyShape.2]
                      exact foundFrame
                    obtain ⟨index, current⟩ := callCursor config ready readyShape.1 frame readyFrame
                    rw [RvalueWP.actionPre_ok index, RvalueWP.actionPre_ok current]
                    rw [handed]
                    dsimp only [dispatch]
                    rw [dispatched]
                    rw [CallWP.initStackFramePre_eq_wp
                      (scope := CallWP.canonicalRetagPullback checked limits ()), ← RvalueWP.actionPre_eq_wp] at initialized ⊢
                    refine continueAfterFrame _ _ _ _ _ initialized ?_
                    intro _ after observed
                    have progress := protectedCallProgress config ready after readyShape.1
                      observed.1 frame.location success failure
                    change finish after = _ at progress
                    rw [progress]
                    exact observed

/-- The selected canonical call reaches the same state used to verify the
callee's first assignment. -/
theorem protectedCallStep :
    match atBorrowedCall, writeEntry with
    | .ok (config, _, before), .ok (_, expected) =>
      ExecutionMachine.step config limits () before = (expected, .ok true) ∧
        argumentHasStrongProtector expected = true
    | _, _ => False := by
  have proof := protectedCallNode
  have selected := borrowedCallSelected
  cases entered : atBorrowedCall with
  | error reason => simp only [entered] at proof
  | ok result =>
    obtain ⟨config, program, before⟩ := result
    simp only [entered, Except.toOption, Option.bind_some] at proof selected
    rw [selectedPre_iff config _ _ before _ _ selected] at proof
    rcases ran : ExecutionMachine.step config limits () before with ⟨after, result⟩
    rw [ran] at proof
    cases result with
    | error reason => exact False.elim proof
    | ok more =>
      obtain ⟨rfl, observed, exactEntry⟩ := proof
      cases expectedShape : writeEntry with
      | error reason => simp only [expectedShape] at exactEntry
      | ok pair =>
        obtain ⟨expectedConfig, expected⟩ := pair
        simp only [expectedShape] at exactEntry
        rw [← exactEntry]
        exact ⟨ran, observed⟩

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``protectedCallNode, ``protectedCallStep] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms protectedCallNode
#print axioms protectedCallStep
end CalleeSummaryReflected

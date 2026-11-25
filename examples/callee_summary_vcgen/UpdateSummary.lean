import CallExecution
import CalleeAssignments
import CalleeFinishReturn
import CallerWindow

/-! Verify the exported `update(&mut u8)` summary and apply it at the
caller window using its exact returned state. -/

namespace CalleeSummaryExample
open Miri.Interpreter Miri.Verification Miri.Verification.WholeBodyWP
open PointerObservation.Fixture
open CalleeSummaryReflected hiding atBorrowedCall

private theorem uniqueScopeExit {S : Type} {step : Unit → S → StepResult S Bool}
    {depthOf : S → Nat} {depth : Nat} {before resumed after : S}
    {outcome : Except StepError Exit}
    (canonical : Finishes step depthOf (fun _ _ => True) depth before resumed (.ok .scopeExit))
    (observed : Finishes step depthOf (fun _ _ => True) depth before after outcome) :
    outcome = .ok .scopeExit ∧ after = resumed := by
  generalize terminal : (.ok .scopeExit : Except StepError Exit) = result at canonical
  induction canonical generalizing after outcome with
  | scopeExit outside =>
    cases observed with
    | scopeExit _ => exact ⟨rfl, rfl⟩
    | stopped live _ _ | failed live _ _ | next live _ _ _ =>
      exact (Nat.not_le.mpr outside live).elim
  | stopped _ _ _ | failed _ _ _ => cases terminal
  | next live _ canonicalStep _ ih =>
    cases observed with
    | scopeExit outside => exact (Nat.not_le.mpr outside live).elim
    | stopped _ _ observedStep | failed _ _ observedStep =>
      cases ‹Unit›
      rw [canonicalStep] at observedStep
      cases observedStep
    | next _ _ observedStep rest =>
      rename_i selected observedChoice
      cases selected
      have same := congrArg Prod.fst observedStep
      subst same
      rw [canonicalStep] at observedStep
      cases observedStep
      rw [canonicalStep] at rest
      exact ih rest terminal

set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option cbv.maxSteps 200000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
attribute [local cbv_eval] Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert

/-- The callee returns 7, writes 42 and releases its argument protector.
The original caller frame resumes at the first statement of bb1. -/
def updateReturnFacts (after : State) : Prop :=
  scalarAt after 4 = some 7 ∧ bytesAt 0 after = some (.ok #[42]) ∧
  after.machine.borrowTracker.map (fun tracker => tracker.global.protectedTags.get calleeBorrow) =
    some none ∧
  (after.stack.currentFrame?.map fun frame => (frame.localsIdentity, frame.location)) =
    some (LocalsIdentity.ofAllocationToken 1, .mir ⟨1, 0⟩)

private theorem exactScopeFacts :
    match CalleeSummaryReflected.atBorrowedCall, writeEntry, returnEntry, expectedResume with
    | .ok (config, _, caller), .ok (writing, entered), .ok (returning, beforeReturn),
      .ok (resuming, resumed) =>
      config = writing ∧ config = returning ∧ config = resuming ∧
      caller.stack.frames.size = 1 ∧ entered.stack.frames.size = 2 ∧
      beforeReturn.stack.frames.size = 2 ∧ resumed.stack.frames.size = 1 ∧
      updateReturnFacts resumed
    | _, _, _, _ => False := by
  cbv
  exact ⟨rfl, rfl, trivial⟩


/-- The selected exported call is safe through every finite callee exit.
Its exact resumed state carries the observable return and permission facts. -/
theorem updateSummary :
    match CalleeSummaryReflected.atBorrowedCall, expectedResume with
    | .ok (config, program, caller), .ok (resuming, resumed) =>
      config = resuming ∧ CalleeSummaryWP.callPre config limits (BodyCFG.compileProgram program.down.bodies)
        (fun _ _ => True) (fun exit after =>
          exit = .scopeExit ∧ after = resumed ∧ updateReturnFacts after)
        (fun _ _ => False) caller
    | _, _ => False := by
  have facts := exactScopeFacts
  have called := protectedCallStep
  have assigned := assignmentSteps
  have returned := returnStepReflected
  cases hc : CalleeSummaryReflected.atBorrowedCall with
  | error _ => simp only [hc] at called
  | ok input =>
    obtain ⟨config, program, caller⟩ := input
    cases hw : writeEntry with
    | error _ => simp only [hc, hw] at called
    | ok starting =>
      obtain ⟨writing, entered⟩ := starting
      cases hr : returnEntry with
      | error _ => simp only [hw, hr] at assigned
      | ok ending =>
        obtain ⟨returning, beforeReturn⟩ := ending
        cases hs : expectedResume with
        | error _ => simp only [hr, hs] at returned
        | ok finished =>
          obtain ⟨resuming, resumed⟩ := finished
          simp only [hc, hw] at called
          simp only [hw, hr] at assigned
          simp only [hr, hs] at returned
          simp only [hc, hw, hr, hs] at facts
          rcases facts with ⟨rfl, rfl, rfl, callerDepth, entryDepth, returnDepth, resumeDepth,
            observations⟩
          dsimp only
          refine ⟨rfl, ?_⟩
          rw [CalleeSummaryWP.callPre_iff]
          intro choice _
          cases choice
          rw [called.1]
          simp only [InstructionWP.resultPre, ↓reduceIte]
          intro after outcome observed
          rcases first : ExecutionMachine.step config limits () entered with ⟨written, result⟩
          rw [first] at assigned
          rcases assigned with ⟨rfl, writtenDepth, assignment⟩
          have canonical : Finishes (ExecutionMachine.step config limits)
              (fun state => state.stack.frames.size) (fun _ _ => True)
              (caller.stack.frames.size + 1) entered resumed (.ok .scopeExit) := by
            rw [callerDepth]
            exact .next (by simp [entryDepth]) trivial first
              (.next (by simp [writtenDepth]) trivial assignment
                (.next (by simp [returnDepth]) trivial returned (.scopeExit (by simp [resumeDepth]))))
          rcases uniqueScopeExit canonical observed with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, observations⟩

/-- The actual state produced by the call summary satisfies the emitted
caller checks and authorizes the write of 99. -/
theorem updateThenCallerStore :
    match CalleeSummaryReflected.atBorrowedCall with
    | .error _ => False
    | .ok (config, program, caller) =>
      CalleeSummaryWP.callPre config limits (BodyCFG.compileProgram program.down.bodies)
        (fun _ _ => True) (fun exit after =>
          exit = .scopeExit ∧ GeneratedBodyVC.windowPrefixPre config limits
            (fun _ _ => True) (fun final => bytesAt 0 final = some (.ok #[99]))
            (fun _ _ => False) (callerRows config) after)
        (fun _ _ => False) caller := by
  have summary := updateSummary
  cases hc : CalleeSummaryReflected.atBorrowedCall with
  | error _ => simp only [hc] at summary
  | ok input =>
    obtain ⟨config, program, caller⟩ := input
    cases hs : expectedResume with
    | error _ => simp only [hc, hs] at summary
    | ok output =>
      obtain ⟨resuming, resumed⟩ := output
      simp only [hc, hs] at summary
      rcases summary with ⟨rfl, summary⟩
      dsimp only
      refine callerWindow_from_summary _ _ _ _ summary ?_
      rintro after ⟨rfl, _⟩
      simpa only [hs] using generatedCallerObservation

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``updateSummary, ``updateThenCallerStore] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms updateSummary
#print axioms updateThenCallerStore

end CalleeSummaryExample

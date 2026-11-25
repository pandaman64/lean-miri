import CalleeBody
import Miri.Verification.CalleeSummaryWP
import Miri.Verification.GeneratedBodyVC

/-! Observe the two accepting branch targets and the store in the resumed caller. -/
namespace CalleeSummaryExample

open Miri.Interpreter Miri.Verification Miri.Verification.WholeBodyWP PointerObservation.Fixture

def callerRows (config : Config) : List (GeneratedBodyVC.WindowRow config limits) :=
  GeneratedBodySafety.window_0_bb1_0 config limits ++
    GeneratedBodySafety.window_0_bb3_0 config limits ++
    (GeneratedBodySafety.window_0_bb5_0 config limits).take 5

/-- Attach the selected caller observations at the actual state returned by a
call summary. The two switch targets and the final write are in the window. -/
theorem callerWindow_from_summary (config : Config) (program : BodyCFG.CompiledProgram)
    (atCall : State) (returned : State → Prop)
    (summary : CalleeSummaryWP.callPre config limits program (fun _ _ => True)
      (fun exit after => exit = .scopeExit ∧ returned after) (fun _ _ => False) atCall)
    (resume : ∀ after, returned after →
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun final => bytesAt 0 final = some (.ok #[99])) (fun _ _ => False)
        (callerRows config) after) :
    CalleeSummaryWP.callPre config limits program (fun _ _ => True) (fun exit after =>
      exit = .scopeExit ∧
        GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
          (fun final => bytesAt 0 final = some (.ok #[99])) (fun _ _ => False)
          (callerRows config) after) (fun _ _ => False) atCall := by
  rw [CalleeSummaryWP.callPre_iff]
  intro choice permitted
  have entered := (CalleeSummaryWP.callPre_iff config limits program
    (fun _ _ => True) _ _ atCall).mp summary choice permitted
  rcases ran : ExecutionMachine.step config limits choice atCall with ⟨next, outcome⟩
  cases outcome with
  | error _ => simp only [InstructionWP.resultPre, ran] at entered
  | ok more =>
    cases more
    · simp only [InstructionWP.resultPre, ran, Bool.false_eq_true, ↓reduceIte] at entered
      cases entered.1
    · simp only [InstructionWP.resultPre, ran, ↓reduceIte] at entered ⊢
      intro after outcome scope
      have done := entered after outcome scope
      cases outcome with
      | error _ => exact done
      | ok exit => exact ⟨done.1, resume after done.2⟩

/-- Execute the same selected caller rows after the concrete call and return. -/
def checkCallerStore : Except String Unit :=
  match observeUpdateReturn with
  | .error error => .error error
  | .ok (config, resumed) => do
    let result : Option State := (callerRows config).foldl (fun state row =>
      state.bind fun before =>
        if BodyCFG.selected before = some (row.location.pc, row.reduced.node) then
          match ExecutionMachine.step config limits () before with
          | (after, .ok true) => some after
          | _ => none
        else none) (some resumed)
    let some final := result | throw "caller did not follow both accepting branch targets and the store"
    unless decide (bytesAt 0 final = some (.ok #[99])) do
      throw "resumed caller did not store byte 99"

set_option compiler.extract_closed false in
#eval show IO Unit from match checkCallerStore with
  | .ok () => pure ()
  | .error error => throw (IO.userError error)

open Lean Elab Command in
run_cmd liftTermElabM do
  for dependency in (← collectAxioms ``callerWindow_from_summary) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "callerWindow_from_summary depends on unapproved axiom {dependency}"

#print axioms callerWindow_from_summary

end CalleeSummaryExample

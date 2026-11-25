import CalleeReturn

/-! The emitted stores in the protected callee. -/

namespace CalleeSummaryReflected

open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.TreeBorrows Miri.Verification
open PointerObservation.Fixture GeneratedBodySafety

set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
set_option cbv.maxSteps 160000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert
attribute [local cbv_opaque] RvalueWP.evalPre ValidityVisitor.validatePlace ValidityVisitor.visit
attribute [local cbv_eval] ValidityVisitor.validatePlace_shallow
attribute [local cbv_opaque] writeImmediateAfterAccess
attribute [local cbv_eval] writeImmediateAfterAccess_scalar

/-- The exported callee writes 42 through the protected reference and
assigns literal 7 to its return local. Its exact endpoint supplies the
input to the canonical Return, including the retained bytes and borrow tree. -/
theorem assignmentWindow :
    match writeEntry, returnEntry with
    | .ok (config, before), .ok (_, expected) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun middle => middle.stack.frames.size = 2 ∧
          GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
            (fun after => after = expected) (fun _ _ => False)
            ((window_1_bb0_1 config limits).take 1) middle)
        (fun _ _ => False) ((window_1_bb0_0 config limits).take 1) before
    | _, _ => False := by
  conv => cbv
  refine ⟨rfl, ?_⟩
  intro choice _
  cases choice
  conv => cbv
  conv =>
    pattern ValidityVisitor.visit _ _ 32 _ _ _
    tactic =>
      refine ValidityVisitor.visit_integer_memory (P := Provenance) _ _ 31 _ _ _
        ?value ?layout ?memory ?ranges ?updated ?classified ?read ?clear ?operand
        ?reset ?tracked ?sized ?marked
      case classified => cbv <;> rfl
      case read => cbv <;> rfl
      case clear => cbv <;> rfl
      case operand => cbv <;> rfl
      case reset => cbv <;> rfl
      case tracked => cbv <;> rfl
      case sized => cbv <;> rfl
      case marked => cbv <;> rfl
  conv => cbv
  refine ⟨rfl, ?_⟩
  intro choice _
  cases choice
  conv => cbv
  conv =>
    pattern ValidityVisitor.visit _ _ 32 _ _ _
    tactic =>
      refine ValidityVisitor.visit_integer _ _ 31 _ _ _ ?localValue ?localLayout
        ?localClassified ?localRead ?localClear ?localRanges
      case localClassified => cbv <;> rfl
      case localRead => cbv <;> rfl
      case localClear => cbv <;> rfl
      case localRanges => rfl
  conv => cbv
  rfl

/-- The same emitted transfers determine the two canonical machine steps. -/
theorem assignmentSteps :
    match writeEntry, returnEntry with
    | .ok (config, before), .ok (_, expected) =>
      let first := ExecutionMachine.step config limits () before
      first.2 = .ok true ∧ first.1.stack.frames.size = 2 ∧
        ExecutionMachine.step config limits () first.1 = (expected, .ok true)
    | _, _ => False := by
  have checked := assignmentWindow
  cases entered : writeEntry with
  | error error => simp only [entered] at checked
  | ok input =>
    obtain ⟨config, before⟩ := input
    cases exited : returnEntry with
    | error error => simp only [entered, exited] at checked
    | ok output =>
      obtain ⟨_, expected⟩ := output
      simp only [entered, exited, window_1_bb0_0, window_1_bb0_1,
        List.take_succ_cons, List.take_zero] at checked
      rw [GeneratedBodyVC.windowPrefixPre_step] at checked
      have firstProof := checked.2 () trivial
      rcases ran : ExecutionMachine.step config limits () before with ⟨after, outcome⟩
      cases outcome with
      | error error =>
        simp only [ran, InstructionWP.resultPre] at firstProof
      | ok more =>
        simp only [ran, InstructionWP.resultPre] at firstProof
        change more = true ∧ after.stack.frames.size = 2 ∧ _ at firstProof
        rcases firstProof with ⟨rfl, depth, secondProof⟩
        rw [GeneratedBodyVC.windowPrefixPre_step] at secondProof
        have finalProof := secondProof.2 () trivial
        rcases finished : ExecutionMachine.step config limits () after with ⟨final, result⟩
        cases result with
        | error error =>
          simp only [finished, InstructionWP.resultPre] at finalProof
        | ok continued =>
          simp only [finished, InstructionWP.resultPre, GeneratedBodyVC.windowPrefixPre] at finalProof
          rcases finalProof with ⟨rfl, rfl⟩
          simp only [ran, finished, depth, and_self]

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``assignmentWindow, ``assignmentSteps] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms assignmentWindow
#print axioms assignmentSteps

end CalleeSummaryReflected

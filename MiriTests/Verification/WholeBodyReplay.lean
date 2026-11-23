import Miri.Verification.BodyVCGen

/-! Validate finite deterministic execution certificates against the generated
VC in tests. The replay budget only limits certificate search. -/
namespace MiriTests.Verification.WholeBodyReplay

open Miri.Interpreter Miri.Verification Miri.Verification.WholeBodyWP Std.WP

variable {S C : Type}

/-- The selected callback choice is the only choice at each state. -/
def selected (choose : S → C) (state : S) (choice : C) : Prop := choice = choose state

/-- Try to find a terminal outcome under the chosen schedule. Scope exits
are observed immediately, including after the last permitted replay step. -/
def replay (step : C → S → StepResult S Bool) (choose : S → C)
    (stackDepth : S → Nat) (depth : Nat) : Nat → S → Option (S × Except StepError Exit)
  | budget, state =>
    if depth ≤ stackDepth state then
      match budget with
      | 0 => none
      | fuel + 1 =>
        match step (choose state) state with
        | (after, .ok true) => replay step choose stackDepth depth fuel after
        | (after, .ok false) => some (after, .ok .stopped)
        | (after, .error error) => some (after, .error error)
    else some (state, .ok .scopeExit)

theorem replay_sound (step : C → S → StepResult S Bool) (choose : S → C)
    (stackDepth : S → Nat) (depth budget : Nat) (before after : S) (outcome : Except StepError Exit)
    (checked : replay step choose stackDepth depth budget before = some (after, outcome)) :
    Finishes step stackDepth (selected choose) depth before after outcome := by
  induction budget generalizing before with
  | zero =>
    unfold replay at checked
    split at checked
    · simp at checked
    · rename_i outside
      obtain ⟨rfl, rfl⟩ := Option.some.inj checked
      exact .scopeExit (Nat.lt_of_not_ge outside)
  | succ budget ih =>
    unfold replay at checked
    split at checked
    · rename_i inside
      rcases ran : step (choose before) before with ⟨next, result⟩
      cases result with
      | error error =>
        rw [ran] at checked
        obtain ⟨rfl, rfl⟩ := Option.some.inj checked
        exact .failed inside rfl ran
      | ok more =>
        cases more
        · rw [ran] at checked
          obtain ⟨rfl, rfl⟩ := Option.some.inj checked
          exact .stopped inside rfl ran
        · rw [ran] at checked
          exact .next inside rfl ran (ih next checked)
    · rename_i outside
      obtain ⟨rfl, rfl⟩ := Option.some.inj checked
      exact .scopeExit (Nat.lt_of_not_ge outside)

/-- One replay is a valid counterexample under any policy that permits every
choice selected by the schedule. -/
theorem replay_sound_for (step : C → S → StepResult S Bool) (choose : S → C)
    (stackDepth : S → Nat) (allowed : S → C → Prop) (depth budget : Nat)
    (before after : S) (outcome : Except StepError Exit)
    (permits : ∀ state, allowed state (choose state))
    (checked : replay step choose stackDepth depth budget before = some (after, outcome)) :
    Finishes step stackDepth allowed depth before after outcome := by
  have finished := replay_sound _ _ _ _ _ _ _ _ checked
  clear checked
  induction finished with
  | scopeExit outside => exact .scopeExit outside
  | stopped inside chosen ran => exact .stopped inside (chosen ▸ permits _) ran
  | failed inside chosen ran => exact .failed inside (chosen ▸ permits _) ran
  | next inside chosen ran _ ih => exact .next inside (chosen ▸ permits _) ran ih

theorem finishes_unique (step : C → S → StepResult S Bool) (choose : S → C)
    (stackDepth : S → Nat) (depth : Nat)
    {before after₁ after₂ : S} {outcome₁ outcome₂ : Except StepError Exit}
    (first : Finishes step stackDepth (selected choose) depth before after₁ outcome₁)
    (second : Finishes step stackDepth (selected choose) depth before after₂ outcome₂) :
    after₁ = after₂ ∧ outcome₁ = outcome₂ := by
  induction first generalizing after₂ outcome₂ with
  | scopeExit outside =>
    cases second with
    | scopeExit => exact ⟨rfl, rfl⟩
    | stopped inside => exact (Nat.not_le_of_gt outside inside).elim
    | failed inside => exact (Nat.not_le_of_gt outside inside).elim
    | next inside => exact (Nat.not_le_of_gt outside inside).elim
  | stopped inside allowed firstRun =>
    cases second with
    | scopeExit outside => exact (Nat.not_le_of_gt outside inside).elim
    | stopped _ allowed' secondRun =>
      rw [show _ = choose _ from allowed] at firstRun
      rw [show _ = choose _ from allowed'] at secondRun
      have same := firstRun.symm.trans secondRun
      exact ⟨(Prod.mk.inj same).1, rfl⟩
    | failed _ allowed' secondRun | next _ allowed' secondRun =>
      rw [show _ = choose _ from allowed] at firstRun
      rw [show _ = choose _ from allowed'] at secondRun
      cases firstRun.symm.trans secondRun
  | failed inside allowed firstRun =>
    cases second with
    | scopeExit outside => exact (Nat.not_le_of_gt outside inside).elim
    | failed _ allowed' secondRun =>
      rw [show _ = choose _ from allowed] at firstRun
      rw [show _ = choose _ from allowed'] at secondRun
      obtain ⟨rfl, equal⟩ := Prod.mk.inj (firstRun.symm.trans secondRun)
      cases equal
      exact ⟨rfl, rfl⟩
    | stopped _ allowed' secondRun | next _ allowed' secondRun =>
      rw [show _ = choose _ from allowed] at firstRun
      rw [show _ = choose _ from allowed'] at secondRun
      cases firstRun.symm.trans secondRun
  | next inside allowed firstRun _ ih =>
    cases second with
    | scopeExit outside => exact (Nat.not_le_of_gt outside inside).elim
    | stopped _ allowed' secondRun | failed _ allowed' secondRun =>
      rw [show _ = choose _ from allowed] at firstRun
      rw [show _ = choose _ from allowed'] at secondRun
      cases firstRun.symm.trans secondRun
    | next _ allowed' secondRun tail =>
      rw [show _ = choose _ from allowed] at firstRun
      rw [show _ = choose _ from allowed'] at secondRun
      cases firstRun.symm.trans secondRun
      exact ih tail

section Production

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

/-- A checked replay proves or refutes the actual generated program VC,
depending on the arbitrary success and error postconditions. -/
theorem generatedProgramPre_iff_replay
    (config : Config) (limits : ExecutionMachine.Limits) (program : BodyVCGen.LoadedProgram)
    (choose : State → C) (post : Exit → State → Prop) (failure : StepError → State → Prop)
    (before after : State) (outcome : Except StepError Exit) (budget : Nat)
    (entry : entryMatchesLoaded program.root before)
    (checked : replay (ExecutionMachine.step config limits) choose (fun s => s.stack.frames.size)
      before.stack.frames.size budget before = some (after, outcome)) :
    (BodyVCGen.generateProgram config limits program (selected choose) post failure).pre before ↔
      InstructionWP.resultPre post failure (after, outcome) := by
  rw [BodyVCGen.generatedProgramPre_eq, catalogBodyPre_iff]
  have finished := replay_sound _ _ _ _ _ _ _ _ checked
  constructor
  · intro valid
    exact valid.2 _ _ finished
  · intro accepted
    refine ⟨entry, ?_⟩
    intro actual result run
    obtain ⟨rfl, rfl⟩ := finishes_unique _ _ _ _ finished run
    exact accepted

/-- A checked certificate also discharges the VC pulled through canonical
root preparation, including the production ABI and argument-copy setup. -/
theorem preparedProgramPre_iff_replay
    (config : Config) (limits : ExecutionMachine.Limits) (program : BodyVCGen.LoadedProgram)
    (launchChoice : C) (args : Array (RvalueImmTy Miri.Memory.Provenance))
    (dest : Option (MPlaceTy Miri.Memory.Provenance)) (span : Miri.MIR.SpanRef)
    (choose : State → C) (post : Exit → State → Prop) (failure : StepError → State → Prop)
    (initial before after : State) (outcome : Except StepError Exit) (budget : Nat)
    (launched : BodyVCGen.prepareRoot config limits program launchChoice args dest span initial = .ok () before)
    (entry : entryMatchesLoaded program.root before)
    (checked : replay (ExecutionMachine.step config limits) choose (fun s => s.stack.frames.size)
      before.stack.frames.size budget before = some (after, outcome)) :
    BodyVCGen.preparedProgramPre config limits program launchChoice args dest span (selected choose)
      post failure initial ↔ InstructionWP.resultPre post failure (after, outcome) := by
  simp only [BodyVCGen.preparedProgramPre, wp, WP.wpTrans, launched]
  exact generatedProgramPre_iff_replay _ _ _ _ _ _ _ _ _ _ entry checked

/-- A kernel-checked connection between the evaluator's terminal observation
and the generated VC. The proof is retained in the type and erased in logs. -/
structure Certificate (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (choose : State → C) (before : State) where
  after : State
  outcome : Except StepError Exit
  exact : ∀ post failure,
    (BodyVCGen.generateProgram config limits program (selected choose) post failure).pre before ↔
      InstructionWP.resultPre post failure (after, outcome)

/-- Compute an actual driver replay with a checked root identity, body and
entry location. A missing terminal result yields no certificate. -/
def certify (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (choose : State → C) (before : State) (budget : Nat) :
    Option (Certificate config limits program choose before) :=
  match current : before.stack.currentFrame? with
  | none => none
  | some frame =>
    if entry : frame.bodyIdentity = program.root.identity ∧ frame.body = program.root.body ∧
        frame.location = .mir ⟨0, 0⟩ then
      match checked : replay (ExecutionMachine.step config limits) choose (fun s => s.stack.frames.size)
          before.stack.frames.size budget before with
      | none => none
      | some (after, outcome) => some ⟨after, outcome, fun post failure =>
        generatedProgramPre_iff_replay config limits program choose post failure before after outcome
          budget ⟨frame, current, entry.1, entry.2.1, entry.2.2⟩ checked⟩
    else none

/-- Visible evaluator verdicts with a proof about each exact generated VC. -/
structure Verdict (normal stopped impossible noUB : Prop) where
  acceptsScopeExit : Bool
  acceptsStopped : Bool
  acceptsNoUB : Bool
  exactScopeExit : normal ↔ acceptsScopeExit = true
  exactStopped : stopped ↔ acceptsStopped = true
  rejectsImpossiblePost : ¬ impossible
  exactNoUB : noUB ↔ acceptsNoUB = true

def Certificate.verdict {config : Config} {limits : ExecutionMachine.Limits}
    {program : BodyVCGen.LoadedProgram} {choose : State → C} {before : State}
    (certificate : Certificate config limits program choose before) :
    Verdict
      ((BodyVCGen.generateProgram config limits program (selected choose)
        (fun exit _ => exit = .scopeExit) (fun _ _ => False)).pre before)
      ((BodyVCGen.generateProgram config limits program (selected choose)
        (fun exit _ => exit = .stopped) (fun _ _ => False)).pre before)
      ((BodyVCGen.generateProgram config limits program (selected choose)
        (fun _ _ => False) (fun _ _ => False)).pre before)
      ((BodyVCGen.generateProgram config limits program (selected choose)
        (fun _ _ => True) (fun error _ => RunLoop.reportsUB error = false)).pre before) := by
  refine ⟨(match certificate.outcome with | .ok exit => exit == .scopeExit | .error _ => false),
    (match certificate.outcome with | .ok exit => exit == .stopped | .error _ => false),
    (match certificate.outcome with | .ok _ => true | .error error => !RunLoop.reportsUB error), ?_, ?_, ?_, ?_⟩
  · rw [certificate.exact]
    cases certificate.outcome <;> simp [InstructionWP.resultPre]
  · rw [certificate.exact]
    cases certificate.outcome <;> simp [InstructionWP.resultPre]
  · rw [certificate.exact]
    cases certificate.outcome <;> simp [InstructionWP.resultPre]

  · rw [certificate.exact]
    cases certificate.outcome <;> simp [InstructionWP.resultPre]

end Production
end MiriTests.Verification.WholeBodyReplay

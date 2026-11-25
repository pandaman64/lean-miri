import Generated
import MiriTests.Verification.WholeBodyReplay

namespace BodyVCGenReplayExample

open Miri.Interpreter Miri.Verification Std.WP
open MiriTests.Verification.WholeBodyReplay

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host

/-- In the source runner's initialized core, the typed choice is `Unit`.
The certificate therefore checks every core choice for this initialized state. -/
theorem savedSafetyFromReplay (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (before : State) (certificate : Certificate config limits program (fun _ => ()) before) :
    GeneratedBodySafety.requiredForEveryChoiceAt config limits before ↔
      certificate.verdict.acceptsNoUB = true := by
  have choices : selected (fun _ : State => ()) = fun _ _ => True := by
    funext state choice
    cases choice
    simp [selected]
  simpa only [GeneratedBodySafety.requiredForEveryChoiceAt, GeneratedBodySafety.requiredAt_eq,
    BodyVCGen.noUB, loaded, choices] using certificate.verdict.exactNoUB

set_option experimental.vcgen true in
/-- Direct Lean clients can ask `vcgen` for the specialized precondition with
arbitrary success and failure continuations. -/
theorem generatedTriple (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → Unit → Prop)
    (initial : State → Prop) (post : WholeBodyWP.Exit → State → Prop)
    (failure : StepError → State → Prop)
    (valid : ∀ state, initial state → GeneratedBodyVC.pre config limits program
      (GeneratedBodySafety.transferTable config limits) allowed post failure state) :
    Triple (GeneratedBodyVC.run config limits program (GeneratedBodySafety.transferTable config limits) allowed)
      initial post failure := by
  vcgen
  rename_i state entered
  exact valid state entered

set_option experimental.vcgen true in
/-- For an entry that selects a generated row, `vcgen` reduces the obligation
to that row's predicate. Its successor remains shared on a back edge. -/
theorem generatedTripleRow (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → Unit → Prop)
    (before : State) (post : WholeBodyWP.Exit → State → Prop)
    (failure : StepError → State → Prop)
    (identity : BodyIdentity) (cfg : BodyCFG.Compiled) (equation : BodyCFG.Equation)
    (reduced : GeneratedBodyVC.ReducedNode config limits)
    (entered : WholeBodyWP.entryMatchesLoaded program.root before)
    (active : (BodyCFG.compileProgram program.bodies).graphFor before = some (identity, cfg))
    (selected : cfg.equationFor before = some equation)
    (found : (GeneratedBodySafety.transferTable config limits)[
      (identity.index, equation.pc.block, equation.pc.statementIndex)]? = some reduced)
    (same : reduced.node = equation.node)
    (checked : ∀ choice, allowed before choice →
      let graph := BodyCFG.compileProgram program.bodies
      let table := GeneratedBodySafety.transferTable config limits
      let depth := before.stack.frames.size
      reduced.pre choice (fun more after => if more then
        if 0 < BodyCFG.programRank graph after ∧
            BodyCFG.programRank graph after < BodyCFG.programRank graph before then
          GeneratedBodyVC.controlPre config limits graph table allowed depth post failure after
        else GeneratedBodyVC.sharedPre config limits graph table allowed depth post failure after
      else post .stopped after) failure before) :
    Triple (GeneratedBodyVC.run config limits program (GeneratedBodySafety.transferTable config limits) allowed)
      (fun state => state = before) post failure := by
  vcgen
  rename_i state equal
  subst state
  miri_generated_program
  refine ⟨entered, ?_⟩
  simp only [Nat.le_refl, ↓reduceIte]
  intro choice permitted
  rw [GeneratedBodyVC.rule_pre_of_row (active := active) (selected := selected)
    (found := found) (same := same)]
  exact checked choice permitted

#print axioms savedSafetyFromReplay
#print axioms generatedTriple
#print axioms generatedTripleRow
end BodyVCGenReplayExample

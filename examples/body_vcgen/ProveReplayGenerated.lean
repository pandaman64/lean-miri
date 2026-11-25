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

#print axioms savedSafetyFromReplay
#print axioms generatedTriple
end BodyVCGenReplayExample

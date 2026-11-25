import Generated
import MiriTests.Verification.WholeBodyReplay

namespace BodyVCGenReplayExample

open Miri.Interpreter Miri.Verification
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

#print axioms savedSafetyFromReplay
end BodyVCGenReplayExample

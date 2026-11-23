import Representative
import MiriTests.Verification.WholeBodyReplay

namespace DuplicatePrefix.VerifyGenerated

open Miri.Interpreter Miri.Verification
open MiriTests.Verification.WholeBodyReplay

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

/-- On a successful safety check, return a kernel-checked proof of the
emitted VC at this entry state and selected schedule. -/
def certifyRequiredAt (config : Config) (limits : ExecutionMachine.Limits)
    (choose : State → C) (before : State) (budget : Nat) :
    Option (PLift (GeneratedBodySafety.requiredAt config limits (selected choose) before)) :=
  match loaded : GeneratedBodySafety.loaded with
  | .error _ => none
  | .ok program => do
    let certificate ← certify config limits program choose before budget
    if safe : certificate.verdict.acceptsNoUB = true then
      some ⟨by
        rw [GeneratedBodySafety.requiredAt, loaded]
        exact certificate.verdict.exactNoUB.mpr safe⟩
    else none

/-- A singleton typed choice space admits every choice. The initialized
state still contains the runner's concrete environmental inputs. -/
def certifyRequiredForEveryChoiceAt [Subsingleton C] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (before : State) (budget : Nat) :
    Option (PLift (GeneratedBodySafety.requiredForEveryChoiceAt config limits before)) := by
  have allChoices : selected (fun _ : State => choice) = (fun _ _ => True) := by
    funext state selectedChoice
    exact propext ⟨fun _ => trivial, fun _ => Subsingleton.elim selectedChoice choice⟩
  rw [GeneratedBodySafety.requiredForEveryChoiceAt, ← allChoices]
  exact certifyRequiredAt config limits (fun _ => choice) before budget

end DuplicatePrefix.VerifyGenerated

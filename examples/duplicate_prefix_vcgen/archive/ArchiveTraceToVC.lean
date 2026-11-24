import Miri.Verification.BodyVCGen
import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.SuccessfulTrace

open Miri.Interpreter Miri.Verification
open Miri.Verification.WholeBodyWP

variable {K U O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X H

/-- The exact checked trace excludes stops and errors at every permitted finite
prefix, even if its proof contains instructions after the first scope exit. -/
theorem firstExit_of_returning_trace {config : Config} {limits : ExecutionMachine.Limits}
    {allowed : State → Unit → Prop} {depth : Nat} {initial final after : State}
    {outcome : Except StepError Exit}
    (trace : Trace config limits initial final) (returned : final.stack.frames.size < depth)
    (check : Finishes (ExecutionMachine.step config limits) (fun state => state.stack.frames.size)
      allowed depth initial after outcome) :
    outcome = .ok .scopeExit := by
  induction trace generalizing after outcome with
  | refl current =>
    cases check with
    | scopeExit _ => rfl
    | stopped inside _ _ | failed inside _ _ | next inside _ _ _ => omega
  | @next before middle final expected tail ih =>
    cases check with
    | scopeExit _ => rfl
    | @stopped _ _ choice _ _ actual =>
      cases choice
      rw [expected] at actual
      simp at actual
    | @failed _ _ choice _ _ _ actual =>
      cases choice
      rw [expected] at actual
      simp at actual
    | @next _ _ _ choice _ _ _ actual rest =>
      cases choice
      rw [expected] at actual
      cases actual
      exact ih returned rest

/-- Feed an archival universal trace constructor into the current generated
whole-program precondition for its actual imported root and stock safety post. -/
theorem generated_of_returning_trace (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (allowed : State → Unit → Prop)
    (initial final : State)
    (root : entryMatchesLoaded program.root initial)
    (trace : Trace config limits initial final)
    (returned : final.stack.frames.size < initial.stack.frames.size) :
    (BodyVCGen.generateProgram config limits program allowed
      (fun _ _ => True) BodyVCGen.noUB).pre initial := by
  rw [BodyVCGen.generatedProgramPre_eq, catalogBodyPre_iff]
  refine ⟨root, ?_⟩
  intro after outcome finish
  rw [firstExit_of_returning_trace trace returned finish]
  exact True.intro

#print axioms generated_of_returning_trace
end DuplicatePrefix.SuccessfulTrace

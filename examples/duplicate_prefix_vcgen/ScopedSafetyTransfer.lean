import Representative

/-! Transfer independently proved scoped error safety to the emitted VC.
The scope ends when a successful step leaves the entry stack depth. Resource
limits are the same limits used by the step and root preparation. -/
namespace DuplicatePrefix.ScopedSafetyTransfer

open Miri.Memory Miri.Interpreter Miri.Verification Std.WP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

/-- Apply a separate proof of error safety over the current interpreter
prefixes to the prepared entry in the saved MIR. -/
theorem requiredAt_of_onError
    (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (selected : GeneratedBodySafety.loaded = .ok program)
    (allowed : State → C → Prop) (entry : State)
    (entered : WholeBodyWP.entryMatchesLoaded program.root entry)
    (safe : FunctionBody.OnError (ExecutionMachine.step config limits)
      (fun state => state.stack.frames.size) allowed entry.stack.frames.size entry BodyVCGen.noUB) :
    GeneratedBodySafety.requiredAt config limits allowed entry := by
  apply (GeneratedBodySafety.safetySpec config limits allowed entry program selected).mpr
  refine ⟨entered, ?_⟩
  have onSuffix {before failed : State} {result : Except StepError WholeBodyWP.Exit}
      (finish : WholeBodyWP.Finishes (ExecutionMachine.step config limits)
        (fun state => state.stack.frames.size) allowed entry.stack.frames.size before failed result)
      (reachable : FunctionBody.Reachable (ExecutionMachine.step config limits)
        (fun state => state.stack.frames.size) allowed entry.stack.frames.size entry before) :
      InstructionWP.resultPre (fun _ _ => True) BodyVCGen.noUB (failed, result) := by
    induction finish with
    | scopeExit => trivial
    | stopped => trivial
    | failed inside permitted ran => exact safe _ reachable inside _ permitted _ _ ran
    | next inside permitted ran _ ih => exact ih (.next reachable inside permitted ran)
  intro failed error finish
  exact onSuffix finish .initial

/-- Check canonical root preparation first, including the preparation error
and its actual failed state. A successful preparation establishes the saved
VC at the callee depth, independently of how deep the original caller was. -/
theorem requiredFromRoot_of_onError
    (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (selected : GeneratedBodySafety.loaded = .ok program)
    (launch : C) (arguments : Array (RvalueImmTy Provenance))
    (destination : Option (MPlaceTy Provenance)) (span : Miri.MIR.SpanRef)
    (allowed : State → C → Prop) (before : State)
    (preparationError : ∀ error failed,
      BodyVCGen.prepareRoot config limits program launch arguments destination span before =
        .error error failed → BodyVCGen.noUB error failed)
    (prepared : ∀ entry,
      BodyVCGen.prepareRoot config limits program launch arguments destination span before =
        .ok () entry →
      WholeBodyWP.entryMatchesLoaded program.root entry ∧
      FunctionBody.OnError (ExecutionMachine.step config limits)
        (fun state => state.stack.frames.size) allowed entry.stack.frames.size entry BodyVCGen.noUB) :
    GeneratedBodySafety.requiredFromRoot config limits launch arguments destination span allowed before := by
  simp only [GeneratedBodySafety.requiredFromRoot_eq, selected, BodyVCGen.preparedProgramPre,
    wp, WP.wpTrans]
  cases result : BodyVCGen.prepareRoot config limits program launch arguments destination span before with
  | error error failed => exact preparationError error failed result
  | ok value entry =>
    cases value
    obtain ⟨entered, safe⟩ := prepared entry result
    simpa only [GeneratedBodySafety.requiredAt_eq, selected] using
      requiredAt_of_onError config limits program selected allowed entry entered safe

#print axioms requiredAt_of_onError
#print axioms requiredFromRoot_of_onError

end DuplicatePrefix.ScopedSafetyTransfer

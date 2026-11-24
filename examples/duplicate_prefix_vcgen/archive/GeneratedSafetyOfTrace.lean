import Representative
import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.GeneratedSafetyOfTrace

open Miri.Interpreter Miri.Verification

/-- A terminating proof trace from the prepared root establishes the emitted safety
condition for every choice of the unit-choice interpreter. -/
theorem required [DecidableEq K]
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (config : ExecutionMachine.Config K U Unit Other Extern Host) (limits : ExecutionMachine.Limits)
    (before done : MachineHooks.State K U)
    (entry : WholeBodyWP.entryMatchesLoaded program.root before)
    (trace : SuccessfulTrace.Trace config limits before done)
    (returned : done.stack.frames.size < before.stack.frames.size) :
    GeneratedBodySafety.requiredForEveryChoiceAt config limits before := by
  rw [GeneratedBodySafety.requiredForEveryChoiceAt, GeneratedBodySafety.requiredAt, loaded]
  apply (WholeBodyWP.catalogBodyPre_iff config limits _ _ _ _ _ _).mpr
  refine ⟨entry, ?_⟩
  intro after outcome finished
  generalize depthEq : before.stack.frames.size = depth at returned finished
  clear entry depthEq
  induction finished with
  | scopeExit =>
    trivial
  | stopped inside permitted step =>
    trivial
  | @failed current failedAt choice err inside permitted step =>
    cases choice
    cases trace with
    | refl => exact False.elim (by omega)
    | next first tail =>
      rw [step] at first
      cases first
  | @next current intermediate final choice result inside permitted step suffix ih =>
    cases choice
    cases trace with
    | refl => exact False.elim (by omega)
    | next first tail =>
      rw [step] at first
      have same := congrArg Prod.fst first
      cases same
      exact ih tail

end DuplicatePrefix.GeneratedSafetyOfTrace

#print axioms DuplicatePrefix.GeneratedSafetyOfTrace.required

import empty_function.LocalImmediateNoUB
import empty_function.ProjectedImmediateNoUB
import Miri.Verification.BodyVCGen

namespace EmptyFunction.GeneratedBodySafety

open Miri.Memory Miri.Interpreter Miri.Verification Std.WP
open EmptyFunction.WholeCall EmptyFunction.Specification

set_option maxHeartbeats 3000000
set_option maxRecDepth 65536

/-- The canonical root selected by the caller metadata. -/
def program (s : Static) : BodyVCGen.LoadedProgram :=
  ⟨s.functionInstance, s.loaded, #[s.loaded]⟩

/-- The actual initialization followed by the generated no-UB condition.
The successful state must be the installed callee at entry with call depth. -/
def noUBVC (s : Static) (p : Packet) : Prop :=
  match install s p with
  | .error error _ => RunLoop.reportsUB error = false
  | .ok () entry =>
    (BodyVCGen.generateProgram s.cfg s.limits (program s) (fun _ _ => True)
      (fun _ _ => True) (fun error _ => RunLoop.reportsUB error = false)).pre entry

theorem ofScopedSafety (s : Static) (p : Packet) (safe : CallLevelNoUB.NoUB s p)
    (entryBinding : ∀ entry, install s p = .ok () entry →
      WholeBodyWP.entryMatchesLoaded s.loaded entry ∧ entry.stack.frames.size = depth p) :
    noUBVC s p := by
  obtain ⟨initialization, execution⟩ := (CallLevelNoUB.noUB_iff_initialization_and_scoped s p).mp safe
  unfold noUBVC
  split
  · rename_i error failed actual
    exact initialization error failed actual
  · rename_i entry actual
    obtain ⟨entered, callDepth⟩ := entryBinding entry actual
    rw [BodyVCGen.generatedProgramPre_eq]
    apply (WholeBodyWP.catalogBodyPre_iff _ _ _ _ _ _ _ _).mpr
    refine ⟨entered, ?_⟩
    intro after outcome finished
    rw [callDepth] at finished
    have safe := execution entry actual
    have accumulate {start after : State} {outcome : Except StepError WholeBodyWP.Exit}
        (suffix : WholeBodyWP.Finishes (ExecutionMachine.step s.cfg s.limits)
          (fun state => state.stack.frames.size) (fun _ _ => True) (depth p) start after outcome)
        (reachable : ScopedSafety.Reachable s.cfg s.limits (fun _ _ => True) (depth p) entry start) :
        InstructionWP.resultPre (fun _ _ => True)
          (fun error _ => RunLoop.reportsUB error = false) (after, outcome) := by
      induction suffix with
      | scopeExit => trivial
      | stopped => trivial
      | failed inside allowed run => exact safe _ reachable inside _ allowed _ _ run
      | next inside allowed run _ ih => exact ih (.next reachable inside allowed run)
    exact accumulate finished .initial

/-- Every admitted caller with a local immediate destination satisfies
the generated safety VC. The canonical initializer determines the actual entry. -/
theorem localImmediate (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value) : noUBVC s p := by
  cases offset : destination.offset with
  | none =>
    apply ofScopedSafety s p (LocalImmediateNoUB.noUB s metadata profile p runtime input
      destination offset value immediate)
    intro entry actual
    obtain ⟨older, bound, frame, machine, original, installed, body, identity, _, location, _⟩ :=
      LocalImmediateTotal.init_whole s metadata profile p runtime input destination offset value immediate
    rw [installed] at actual
    cases actual
    refine ⟨⟨frame, ?_, identity, body, location⟩, ?_⟩
    · simp [LocalUnit.current, Stack.currentFrame?]
    · simp [LocalUnit.current, LocalInit.cachedState, depth, original]
  | some amount =>
    apply ofScopedSafety s p (ProjectedImmediateNoUB.noUB s metadata profile p runtime input
      destination amount offset value immediate)
    intro entry actual
    obtain ⟨older, bound, frame, machine, original, installed, body, identity, _, location, _⟩ :=
      LocalImmediateTotal.init_projected s metadata profile p runtime input destination amount offset value immediate
    rw [installed] at actual
    cases actual
    refine ⟨⟨frame, ?_, identity, body, location⟩, ?_⟩
    · simp [LocalUnit.current, Stack.currentFrame?]
    · simp [LocalUnit.current, LocalCachedPush.cachedState, depth, original]

#print axioms ofScopedSafety
#print axioms localImmediate
end EmptyFunction.GeneratedBodySafety

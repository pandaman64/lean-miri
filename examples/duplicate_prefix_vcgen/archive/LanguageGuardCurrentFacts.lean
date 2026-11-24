import duplicate_prefix.PointerAddCurrentFacts
import duplicate_prefix.CompilerFrameLayout

namespace DuplicatePrefix.LanguageGuardCurrentFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def checkedOk {E A : Type} : (result : Except E A) → result.isOk = true → A
  | .ok answer, _ => answer
  | .error _, impossible => False.elim (by cases impossible)

private noncomputable def resolver := PreparedReflection.actual.compiler.lifecycle.calls.calls

noncomputable def parentCallQuery :=
  CallResolution.atSite resolver ⟨PointerAddCurrentFacts.body.identity.index, 0⟩

noncomputable def parentCall := checkedOk parentCallQuery (by decide +kernel)

noncomputable def parentBodyQuery := CallResolution.loadedBodyOfInstance resolver parentCall.callee

noncomputable def parentBody := checkedOk parentBodyQuery (by decide +kernel)

noncomputable def leafCallQuery :=
  CallResolution.atSite resolver ⟨parentBody.identity.index, 0⟩

noncomputable def leafCall := checkedOk leafCallQuery (by decide +kernel)

noncomputable def leafBodyQuery := CallResolution.loadedBodyOfInstance resolver leafCall.callee

noncomputable def leafBody := checkedOk leafBodyQuery (by decide +kernel)

theorem current_source_instances :
    parentCall.sourceInstanceId = 9 ∧ leafCall.sourceInstanceId = 21 := by
  exact ⟨rfl, rfl⟩

theorem parent_local_count : parentBody.body.locals.size = 3 := rfl

theorem leaf_local_count : leafBody.body.locals.size = 1 := rfl

theorem parent_local0 (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = parentBody.body) (identity : frame.bodyIdentity = parentBody.identity)
    (callee : frame.functionInstance = parentCall.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 0 = .ok 0 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem parent_local2 (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = parentBody.body) (identity : frame.bodyIdentity = parentBody.identity)
    (callee : frame.functionInstance = parentCall.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 2 = .ok 5 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

end DuplicatePrefix.LanguageGuardCurrentFacts

#print axioms DuplicatePrefix.LanguageGuardCurrentFacts.current_source_instances
#print axioms DuplicatePrefix.LanguageGuardCurrentFacts.parent_local0
#print axioms DuplicatePrefix.LanguageGuardCurrentFacts.parent_local2

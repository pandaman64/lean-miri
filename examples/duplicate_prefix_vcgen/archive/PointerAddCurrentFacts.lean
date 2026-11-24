import duplicate_prefix.CompilerFrameLayout

namespace DuplicatePrefix.PointerAddCurrentFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def checkedOk {E A : Type} : (result : Except E A) → result.isOk = true → A
  | .ok answer, _ => answer
  | .error _, impossible => False.elim (by cases impossible)

noncomputable def callQuery :=
  CallResolution.atSite PreparedReflection.actual.compiler.lifecycle.calls.calls
    ⟨RootBody.reflected.body.identity.index, 7⟩

noncomputable def call := checkedOk callQuery (by decide +kernel)

noncomputable def bodyQuery :=
  CallResolution.loadedBodyOfInstance PreparedReflection.actual.compiler.lifecycle.calls.calls call.callee

noncomputable def body := checkedOk bodyQuery (by decide +kernel)

theorem source_instance : call.sourceInstanceId = 4 := by rfl

theorem local_count : body.body.locals.size = 12 := by rfl

theorem normalized_local0 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = body.identity)
    (callee : frame.functionInstance = call.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 0 = .ok 8 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local10 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = body.identity)
    (callee : frame.functionInstance = call.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 10 = .ok 8 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local11 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = body.identity)
    (callee : frame.functionInstance = call.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 11 = .ok 4 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl


#print axioms local_count
#print axioms normalized_local0
#print axioms normalized_local10
#print axioms normalized_local11
end DuplicatePrefix.PointerAddCurrentFacts

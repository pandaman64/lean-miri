import duplicate_prefix.AsMutRootRoundtrip
import duplicate_prefix.CopyHelperCleanup

namespace DuplicatePrefix.AsMutPreparedAddFrame
open Miri Miri.ABI Miri.MIR Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def returned (before : CompilerFrameContext.ActualFrame)
    (valid : 15 < before.locals.size) (pointer : Scalar Provenance) :=
  let cached := AsMutCurrentCall.cacheCaller before valid
  let inBounds : 15 < cached.locals.size := by
    simpa [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout] using valid
  {AsMutPtrReturn.writeFrame cached 15 (.scalar pointer) inBounds with location := .mir ⟨7,0⟩}

theorem locals_size (before : CompilerFrameContext.ActualFrame)
    (valid : 15 < before.locals.size) (pointer : Scalar Provenance) :
    (returned before valid pointer).locals.size = before.locals.size := by
  simp [returned,AsMutCurrentCall.cacheCaller,AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout]

theorem slot (before : CompilerFrameContext.ActualFrame)
    (valid : 15 < before.locals.size) (pointer : Scalar Provenance) :
    (returned before valid pointer).locals[15]? =
      some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ := by
  simp [returned,AsMutCurrentCall.cacheCaller,AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout]

theorem unchanged (before : CompilerFrameContext.ActualFrame)
    (valid : 15 < before.locals.size) (pointer : Scalar Provenance)
    (i : Nat) (different : i ≠ 15) :
    (returned before valid pointer).locals[i]? = before.locals[i]? := by
  simp [returned,AsMutCurrentCall.cacheCaller,AsMutPtrReturn.writeFrame,LocalPlaces.cachePlaceLayout,
    Ne.symm different]

theorem direct (before : CompilerFrameContext.ActualFrame)
    (valid : 15 < before.locals.size) (pointer : Scalar Provenance)
    (input : CopyHelperCleanup.AllImmediate before) : CopyHelperCleanup.AllImmediate (returned before valid pointer) := by
  let cached := AsMutCurrentCall.cacheCaller before valid
  have inBounds : 15 < cached.locals.size := by
    simpa [cached,AsMutCurrentCall.cacheCaller,LocalPlaces.cachePlaceLayout] using valid
  have cacheDirect : CopyHelperCleanup.AllImmediate cached :=
    CopyHelperCleanup.all_immediate_cache before 15 CopyCompilerFacts.destPointerLayout valid input
  exact CopyHelperCleanup.all_immediate_set cached 15 _ inBounds cacheDirect (by intro ptr; simp)

end DuplicatePrefix.AsMutPreparedAddFrame

#print axioms DuplicatePrefix.AsMutPreparedAddFrame.locals_size
#print axioms DuplicatePrefix.AsMutPreparedAddFrame.slot
#print axioms DuplicatePrefix.AsMutPreparedAddFrame.unchanged
#print axioms DuplicatePrefix.AsMutPreparedAddFrame.direct

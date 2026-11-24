import duplicate_prefix.RuntimeZeroEntry
import duplicate_prefix.LanguageGuardCurrentFacts

namespace DuplicatePrefix.RuntimeZeroCurrentInstalled
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def frame (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (dest : RuntimeStackPlace Provenance) :=
  RuntimeZeroDone.doneFrame (RuntimeZeroEntry.rawFrame options state dest)

/-- The only runtime guard local is a live, uncached return place. -/
theorem locals (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (dest : RuntimeStackPlace Provenance) :
    (frame options state dest).locals = #[⟨.live (.immediate .uninit),none⟩] := by
  with_unfolding_all rfl

theorem metadata (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (dest : RuntimeStackPlace Provenance) :
    let installed := frame options state dest
    installed.body = LanguageGuardCurrentFacts.leafBody.body ∧
    installed.bodyIdentity = LanguageGuardCurrentFacts.leafBody.identity ∧
    installed.functionInstance = LanguageGuardCurrentFacts.leafCall.callee ∧
    installed.location = .mir ⟨0,0⟩ ∧
    installed.returnPlace = dest ∧ installed.returnContinuation = .goto (some 1) .Unreachable ∧
    installed.vaList = #[] ∧
    installed.extra.dataRace = state.machine.dataRace.map (fun _ => {}) ∧
    installed.extra.borrowTracker = state.machine.borrowTracker.map (fun _ => {}) := by
  with_unfolding_all exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end DuplicatePrefix.RuntimeZeroCurrentInstalled

#print axioms DuplicatePrefix.RuntimeZeroCurrentInstalled.locals
#print axioms DuplicatePrefix.RuntimeZeroCurrentInstalled.metadata

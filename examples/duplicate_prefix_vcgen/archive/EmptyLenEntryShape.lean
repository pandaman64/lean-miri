import duplicate_prefix.LenEntry
import duplicate_prefix.SharedReferenceMetadata
namespace DuplicatePrefix.EmptyLenEntryShape
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def initialized (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
     :=
  let frame := LenEntry.rawFrame options state destination
  let valid : 1 < frame.locals.size := by rw [LenEntry.raw_size];decide
  let initialized := LenInstall.resultFrame frame valid value
  LenDone.doneFrame {initialized with location := .unwinding LenEntryFacts.lenPreamble}

theorem locals (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
     :
    (initialized options state destination value).locals =
      #[⟨.live (.immediate .uninit),none⟩,⟨.live (.immediate value),some SharedReferenceMetadata.sharedLayout⟩,⟨.dead,none⟩] := by
  with_unfolding_all rfl

theorem control (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
     :
    let frame := initialized options state destination value
    frame.body = LenHelper.body.body ∧ frame.bodyIdentity = LenHelper.body.identity ∧
    frame.functionInstance = LenHelper.resolved.callee ∧ frame.location = .mir ⟨0,0⟩ ∧
    frame.returnPlace = destination ∧ frame.returnContinuation = .goto (some 3) .Unreachable ∧ frame.vaList = #[] := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem no_clocks (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)
     (race : state.machine.dataRace = none) :
    (initialized options state destination value).extra.dataRace = none := by
  simp [initialized,LenDone.doneFrame,CallEntryFacts.liveSlot,
      LenInstall.resultFrame,LenArgument.liveFrame,LenInstall.cacheFrame,LenInstall.spanFrame,
      LocalOperands.cachedLayoutFrame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,race]

theorem borrow (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (value : Immediate Provenance)

    (tracker : MachineHooks.BorrowState) (tracked : state.machine.borrowTracker = some tracker) :
    (initialized options state destination value).extra.borrowTracker =
      some ({} : FrameState) := by
  simp [initialized,LenDone.doneFrame,CallEntryFacts.liveSlot,
      LenInstall.resultFrame,LenArgument.liveFrame,LenInstall.cacheFrame,LenInstall.spanFrame,
      LocalOperands.cachedLayoutFrame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,tracked]
end
end DuplicatePrefix.EmptyLenEntryShape
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.EmptyLenEntryShape.locals, ``DuplicatePrefix.EmptyLenEntryShape.control,
      ``DuplicatePrefix.EmptyLenEntryShape.no_clocks, ``DuplicatePrefix.EmptyLenEntryShape.borrow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved len entry shape {dependency}"

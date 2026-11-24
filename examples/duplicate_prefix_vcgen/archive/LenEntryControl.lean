import duplicate_prefix.RootLenCurrentCall
import duplicate_prefix.PushThread

namespace DuplicatePrefix.LenEntryControl

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem preserved (crates : Array Nat) (state : RootState)
    (destination : RuntimeStackPlace Provenance) (current : CompilerFrameContext.ActualFrame)
    (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (exactMachine : after = {(LenPush.completed crates state destination current).machine with
      memory := after.memory, borrowTracker := after.borrowTracker}) :
    after.dataRace = state.machine.dataRace ∧
    after.user.addresses = state.machine.user.addresses ∧
    after.user.payload.ghost = state.machine.user.payload.ghost ∧
    after.user.payload.validation = state.machine.user.payload.validation ∧
    after.user.payload.payload.user = state.machine.user.payload.payload.user ∧
    after.threads.fixedScheduling = state.machine.threads.fixedScheduling := by
  rw [exactMachine]
  dsimp only [LenPush.completed, Storage.withCurrent]
  unfold GenericPushRelevance.afterPush
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem active (crates : Array Nat) (state : RootState)
    (destination : RuntimeStackPlace Provenance) (current : CompilerFrameContext.ActualFrame)
    (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (exactMachine : after = {(LenPush.completed crates state destination current).machine with
      memory := after.memory, borrowTracker := after.borrowTracker})
    (thread : ThreadRecord) (activeThread : state.machine.threads.activeThread? = some thread) :
    let raw := LenFrame.rawFrame crates (LenPush.fresh state.machine).1 destination (LenPush.fresh state.machine).2
    after.threads.activeThread? = some (PushThread.after thread state.stack.frames.size
      raw.extra.userRelevance current.extra.userRelevance) := by
  rw [exactMachine]
  exact PushThread.active_after (LenPush.fresh state.machine).1 thread state.stack.frames.size _ _ activeThread

/-- Updating the relevance cache for the fresh frame preserves index bounds. -/
theorem cacheInBounds (thread : ThreadRecord) (priorSize : Nat) (newRank oldRank : UInt8)
    (valid : ∀ index, thread.topUserRelevantFrame = some index → index < priorSize + 1) :
    ∀ index, (PushThread.after thread priorSize newRank oldRank).topUserRelevantFrame = some index →
      index < priorSize + 1 := by
  unfold PushThread.after
  split
  · intro index equality
    have indexEq : priorSize = index := Option.some.inj equality
    subst index
    omega
  · exact valid

end DuplicatePrefix.LenEntryControl

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.LenEntryControl.preserved, ``DuplicatePrefix.LenEntryControl.active,
      ``DuplicatePrefix.LenEntryControl.cacheInBounds] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved length entry dependency {dependency}"

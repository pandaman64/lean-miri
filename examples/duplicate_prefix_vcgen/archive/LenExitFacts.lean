import duplicate_prefix.MetadataOutputFacts
import duplicate_prefix.FrameRootRelevance

namespace DuplicatePrefix.LenExitFacts
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open MetadataCallSummary MetadataUncachedCall

set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

abbrev MachineState := MachineHooks.MachineState MiriMemoryKind Machine.RootUser
abbrev ActualFrame := CompilerFrameContext.ActualFrame

/-- Observations outside the length computation and its active protector's tree. -/
structure Stable (before after : MachineState) : Prop where
  race : after.dataRace = before.dataRace
  addresses : after.user.addresses = before.user.addresses
  types : after.user.payload.payload.user.types = before.user.payload.payload.user.types
  backend : after.user.payload.payload.user.backend = before.user.payload.payload.user.backend
  extras : after.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras

theorem Stable.trans {first middle last : MachineState}
    (left : Stable first middle) (right : Stable middle last) : Stable first last :=
  ⟨right.race.trans left.race, right.addresses.trans left.addresses, right.types.trans left.types,
    right.backend.trans left.backend, right.extras.trans left.extras⟩

theorem metadata_stable (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (frames : Array ActualFrame) (lenFrame : ActualFrame)
    (before : MachineState) (valid : 0 < lenFrame.locals.size)
    (current done : ActualFrame) (thread : ThreadRecord) :
    Stable before (outputMachine options remaining span frames lenFrame before valid current done thread) := by
  refine ⟨?_, MetadataOutputFacts.addresses_eq options remaining span frames lenFrame before valid current done thread,
    MetadataOutputFacts.types_eq options remaining span frames lenFrame before valid current done thread,
    MetadataOutputFacts.backend_eq options remaining span frames lenFrame before valid current done thread,
    MetadataOutputFacts.extras_eq options remaining span frames lenFrame before valid current done thread⟩
  have preservesRace (machine : MachineState) (position : Nat) (new old : UInt8) :
      (GenericPushRelevance.afterPush machine position new old).dataRace = machine.dataRace := by
    by_cases condition : old ≤ new
    · rw [GenericPushRelevance.afterPush, ite_eq_left condition]
      rfl
    · rw [GenericPushRelevance.afterPush, ite_eq_right condition]
  have raceAtPush : (MetadataPushFacts.posted options remaining span frames (cachedCaller lenFrame valid)
      before current).dataRace = before.dataRace := by
    unfold MetadataPushFacts.posted MetadataPush.completed
    simp only [Storage.withCurrent]
    rw [preservesRace]
    rfl
  simp only [outputMachine, PtrMetadataReturn.poppedMachine, GenericPopFrame.afterRelevanceAt]
  split <;> exact raceAtPush

private theorem after_two (older : Array ActualFrame) (root length metadata : ActualFrame)
    (rank : root.extra.userRelevance = 255) :
    FrameRelevance.computeTop ⟨((older.push root).push length).push metadata⟩ 1 =
      if length.extra.userRelevance = 255 then some (older.push root).size else some older.size := by
  unfold FrameRelevance.computeTop
  simp only [Array.size_push, List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.drop_succ_cons, List.drop_zero, List.forIn_cons]
  have lengthAt : (((older.push root).push length).push metadata)[older.size+1]? = some length := by
    rw [Array.getElem?_push_lt (by simp [Array.size_push])]
    have last := (Array.getElem_push_eq (xs := older.push root) (x := length))
    simpa only [Array.size_push] using congrArg some last
  have rootAt : (((older.push root).push length).push metadata)[older.size]? = some root := by
    rw [Array.getElem?_push_lt (by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (by simp [Array.size_push])]
    rw [Array.getElem_push_eq]
  rw [lengthAt]
  by_cases top : length.extra.userRelevance = 255
  · simp [top, bind, Bind.bind, pure, Pure.pure, Id.run]
  · simp [top, rootAt, rank, bind, Bind.bind, pure, Pure.pure, Id.run, beq_iff_eq]

/-- The metadata call can select its own frame temporarily. Its real pop then
restores either the length frame or the rank-255 root immediately below it. -/
theorem metadata_cache (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (older : Array ActualFrame) (root length : ActualFrame)
    (before : MachineState) (valid : 0 < length.locals.size)
    (current done : ActualFrame) (thread : ThreadRecord)
    (active : before.threads.activeThread? = some thread) (rank : root.extra.userRelevance = 255)
    (cached : thread.topUserRelevantFrame = some older.size ∨
      thread.topUserRelevantFrame = some (older.push root).size) :
    ∃ record, (outputMachine options remaining span (older.push root) length before valid current done thread).threads.activeThread? =
        some record ∧ (record.topUserRelevantFrame = some older.size ∨
          record.topUserRelevantFrame = some (older.push root).size) := by
  let frames := older.push root
  let cachedLength := cachedCaller length valid
  let pushedThread := PushThread.after thread (frames.size+1) (MetadataFrame.rank options.userRelevantCrates) current.extra.userRelevance
  let ticked := PtrMetadataReturn.accountedMachine options remaining span
    (MetadataPushFacts.posted options remaining span frames cachedLength before current)
  have live : ticked.threads.activeThread? = some pushedThread :=
    MetadataPushFacts.active options remaining span frames cachedLength before current thread active
  change ∃ record, (PtrMetadataReturn.poppedMachine frames cachedLength done ticked
    (pushedThread.topUserRelevantFrame.getD (frames.push cachedLength).size)).threads.activeThread? = some record ∧ _
  have metadataIndex : frames.size + 1 = (frames.push cachedLength).size := by simp
  unfold PtrMetadataReturn.poppedMachine GenericPopFrame.afterRelevanceAt
  have indexShape : pushedThread.topUserRelevantFrame = some (frames.push cachedLength).size ∨
      pushedThread.topUserRelevantFrame = thread.topUserRelevantFrame := by
    unfold pushedThread PushThread.after
    split
    · exact Or.inl (congrArg some metadataIndex)
    · exact Or.inr rfl
  rcases indexShape with selected | retained
  · rw [selected]
    simp only [Option.getD_some, ↓reduceIte]
    have final := MetadataOutputFacts.relevance_active (frames.push cachedLength) done ticked pushedThread live
    have chosen := after_two older root cachedLength done rank
    rw [chosen] at final
    refine ⟨_, final, ?_⟩
    dsimp only
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [retained]
    have different : thread.topUserRelevantFrame.getD (frames.push cachedLength).size ≠ (frames.push cachedLength).size := by
      rcases cached with key | key <;>
        simp only [key, Option.getD_some, frames, Array.size_push] <;> omega
    rw [ite_eq_right different]
    exact ⟨pushedThread, live, retained ▸ cached⟩

#print axioms metadata_stable
#print axioms metadata_cache
end DuplicatePrefix.LenExitFacts

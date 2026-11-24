import duplicate_prefix.ActiveStackRelease
import duplicate_prefix.ActiveReleaseExclusive
import duplicate_prefix.ExclusiveTypedRetag

namespace DuplicatePrefix.RetagReleaseRights

open Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.Tree Miri.Verification Miri.Verification.MutableTypedRetag
open ArchiveForestProjection SourceDomain PreparedArguments GeneralRangeMapOrigins GeneralRangeMapState
open MutableSliceRights ActiveRelease

variable {K U : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "GlobalHooks" => GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U)
local notation "BorrowFrame" => Frame Provenance LocalLayout MachineHooks.FrameExtra

private theorem end_add (lower length capacity : UInt64) (fits : lower.toNat + length.toNat ≤ capacity.toNat) :
    (lower + length).toNat = lower.toNat + length.toNat := by
  have safe : lower.toNat + length.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt fits capacity.toNat_lt
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt safe]

omit [DecidableEq K] in
/-- A formed source region grants ownership of each range-map segment
intersecting its byte extent. -/
theorem region_owned (before : State) (length : UInt64)
    (storage : InitializedRegion before length) (tag : BorTag)
    (region : ExclusiveRegion before length storage tag)
    (fits : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat) :
    OwnedOn (fun row => LocationRights storage.entry.allocation.extra row
      region.tracker.global.protectedTags region.source) storage.relativeStart.bytes
      (storage.relativeStart.bytes + length) storage.entry.allocation.extra.locations := by
  intro position present positive begins ends
  let table := storage.entry.allocation.extra.locations
  have hasEntry : table.entries.size ≠ 0 := by
    change position < table.entries.size at present
    omega
  have partition := region.coherent.ranges
  change table.WellFormed at partition
  simp only [DedupRangeMap.WellFormed, hasEntry, ↓reduceDIte] at partition
  let row := table.entries[position]
  have strict : row.range.start.toNat < row.range.stop.toNat :=
    UInt64.lt_iff_toNat_lt.mp (partition.2.1 position present)
  have endpoint := end_add storage.relativeStart.bytes length _ fits
  let point := max storage.relativeStart.bytes.toNat row.range.start.toNat
  have inStorage : point < storage.relativeStart.bytes.toNat + length.toNat := by
    change row.range.start.toNat < (storage.relativeStart.bytes + length).toNat at begins
    omega
  have slotStart : row.range.start.toNat ≤ point := Nat.le_max_right _ _
  have slotStop : point < row.range.stop.toNat := by
    change storage.relativeStart.bytes.toNat < row.range.stop.toNat at ends
    omega
  let distance := point - storage.relativeStart.bytes.toNat
  have base : storage.relativeStart.bytes.toNat ≤ point := Nat.le_max_left _ _
  have exactPoint : storage.relativeStart.bytes.toNat + distance = point := by
    dsimp only [distance]
    omega
  have inExtent : distance < length.toNat := by omega
  exact region.exclusive distance inExtent row (Array.mem_iff_getElem.mpr ⟨position, present, rfl⟩)
    (by simpa only [exactPoint] using slotStart) (by simpa only [exactPoint] using slotStop)

/-- The actual one-entry call ledger releases the selected child, keeps its
raw-byte grants in keyed memory, removes the protector, and returns to the
original caller stack. -/
private theorem releasedImage (old final : BorrowTree) (tag : BorTag) (tags : ProtectedTags)
    (complete : ∀ post failure, ProtectorReleaseWP.releasePre tag tags post failure old ↔ post final) :
    (old.releaseProtector tag tags).tree = final := by
  have exactRun := (ProtectorReleaseWP.releasePre_iff tag tags (· = final) (fun _ _ => False) old).mp
    ((complete _ _).mpr rfl)
  cases observed : old.releaseProtector tag tags with
  | mk tree status =>
    rw [observed] at exactRun
    cases status <;> exact (by first | exact exactRun | exact exactRun.elim)

theorem popExclusive_with_frame (kind : K) (hooks : GlobalHooks) (retag : TypedRetag.Hooks K U)
    (ensure : retag.ensureTreeExtra = GlobalAllocationMachine.ensure kind hooks)
    (older : Array BorrowFrame) (frame : BorrowFrame) (machine : MachineHooks.MachineState K U)
    (length : UInt64) (storage : InitializedRegion (⟨⟨older.push frame⟩, machine⟩ : State) length)
    (tag : BorTag) (region : ExclusiveRegion (⟨⟨older.push frame⟩, machine⟩ : State) length storage tag)
    (synchronize : hooks.synchronizeMemory machine.memory ⟨machine, none⟩ = ⟨machine, none⟩)
    (owned : FrameState) (ledger : frame.extra.borrowTracker = some owned)
    (one : owned.protectedTags = #[(storage.id, tag)])
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (node : TreeNode) (nodeFound : storage.entry.allocation.extra.nodeAt region.source = some node)
    (unexposed : node.isExposed = false)
    (active : Every (ActiveByteRights storage.entry.allocation.extra region.tracker.global.protectedTags
      region.source) storage.entry.allocation.extra.locations)
    (fits : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (thread : ThreadRecord) (relevance : Nat)
    (current : machine.threads.activeThread? = some thread)
    (cached : FrameRelevance.top ⟨older.push frame⟩ thread.topUserRelevantFrame = some relevance) :
    ∃ after : State, after.stack.frames = older ∧ after.machine.user = machine.user ∧
      after.machine.dataRace = machine.dataRace ∧
      after.machine.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      (∃ thread, after.machine.threads.activeThread? = some thread) ∧
      after.machine.threads = (afterRelevance older frame machine relevance).threads ∧
      (∀ key, key ≠ storage.id → after.machine.memory.live[key]? = machine.memory.live[key]?) ∧
      (∃ next : InitializedRegion after length, next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } ∧
        next.entry.allocation.extra.roots = storage.entry.allocation.extra.roots ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        next.entry.allocation.extra = (storage.entry.allocation.extra.releaseProtector tag region.tracker.global.protectedTags).tree ∧
        ∃ rights : ExclusiveRegion after length next tag, rights.tracker.retagMode = region.tracker.retagMode ∧
          rights.tracker.global.protectedTags = region.tracker.global.protectedTags.remove tag) ∧
      ∀ post failure, ProtectorReleaseWP.popRawPre retag post failure ⟨⟨older.push frame⟩, machine⟩ ↔ post frame after := by
  let before : State := ⟨⟨older.push frame⟩, machine⟩
  let old := storage.entry.allocation.extra
  have grants := region_owned before length storage tag region fits
  obtain ⟨tree, treeShape, coherent, sameSize, retained, release⟩ :=
    release_retains_owned old tag region.source root region.tracker.global.protectedTags region.tagKnown
      region.coherent roots node nodeFound unexposed active storage.relativeStart.bytes
      (storage.relativeStart.bytes + length) grants
  let released := releasedMachine before storage.entry storage.id tree region.tracker owned
  let tracker : MachineHooks.BorrowState := {region.tracker with global := region.tracker.global.endCall owned}
  let after : State := ⟨⟨older⟩, afterRelevance older frame released relevance⟩
  refine ⟨after, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases top : relevance = older.size <;> simp [top, after, afterRelevance, released, releasedMachine, before]
  · by_cases top : relevance = older.size <;> simp [top, after, afterRelevance, released, releasedMachine, before]
  · by_cases top : relevance = older.size <;> simp [top, after, afterRelevance, released, releasedMachine, before]
  · by_cases top : relevance = older.size
    · have ready : released.threads.threads[released.threads.activeThread.toNat]? = some thread := current
      let updated := fun position (record : ThreadRecord) =>
        if position == released.threads.activeThread.toNat then
          {record with topUserRelevantFrame := FrameRelevance.computeTop ⟨older.push frame⟩ 1}
        else record
      refine ⟨updated released.threads.activeThread.toNat thread, ?_⟩
      simp only [after, afterRelevance, top, ↓reduceIte]
      change (released.threads.threads.mapIdx updated)[released.threads.activeThread.toNat]? = _
      rw [List.getElem?_mapIdx, ready]
      rfl
    · have ready : released.threads.activeThread? = some thread := current
      exact ⟨thread, by simpa only [after, afterRelevance, ite_eq_right top] using ready⟩
  · by_cases top : relevance = older.size <;> simp [top, after, afterRelevance, released, releasedMachine, before]
  · intro key different
    by_cases top : relevance = older.size <;>
      simp [top,after,afterRelevance,released,releasedMachine,before,Std.ExtTreeMap.getElem?_insert,Ne.symm different]
  · have stored : after.machine.memory.live[storage.id]? =
        some {storage.entry with allocation := storage.entry.allocation.setExtra tree} := by
      by_cases top : relevance = older.size <;> simp [top, after, afterRelevance, released, releasedMachine, before]
    have tracked : after.machine.borrowTracker = some tracker := by
      by_cases top : relevance = older.size <;> simp [top, after, afterRelevance, released, releasedMachine, tracker]
    have newTags : tracker.global.protectedTags = region.tracker.global.protectedTags.remove tag := by
      simp [tracker, GlobalState.endCall, one]
    have known : tree.indexOfTag tag = some region.source := by
      rw [treeShape]
      exact region.tagKnown
    have present : ∃ data, tree.nodeAt region.source = some data ∧ data.tag = tag := by
      rw [treeShape]
      exact region.sourcePresent
    have extent : storage.relativeStart.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat := by
      rw [sameSize]
      exact fits
    have owns : ∀ point : UInt64, storage.relativeStart.bytes.toNat ≤ point.toNat →
        point.toNat < (storage.relativeStart.bytes + length).toNat →
        ∀ row, ValueAt tree.locations point row → OwnsByte tree row tracker.global.protectedTags region.source := by
      intro point lower upper row slot
      obtain ⟨index, inside, starts, ends, same⟩ := slot
      have right := retained index inside (by omega) (by omega) (by omega)
      rw [same] at right
      rw [newTags]
      intro query data found
      obtain ⟨state, queried, localRight, foreignRight⟩ := right query data found
      exact ⟨state, queried, fun path => (localOwns_iff _ _).mp (localRight path),
        fun away => (foreignCompatible_iff _ _).mp (foreignRight away)⟩
    obtain ⟨next, idEq, offsetEq, entryEq, exclusive⟩ :=
      ExclusiveTypedRetag.region_from_cached_reborrow before after length storage tree tag region.source tracker
        stored tracked coherent known present extent owns
    obtain ⟨rights⟩ := exclusive
    have sameTracker : rights.tracker = tracker := Option.some.inj (rights.tracked.symm.trans tracked)
    refine ⟨next, idEq, offsetEq, ?_, ?_, ?_, ?_, rights, by rw [sameTracker], by rw [sameTracker,newTags]⟩
    · rw [entryEq]
      rfl
    · rw [entryEq,treeShape]
      rfl
    · rw [entryEq]
      exact sameSize
    · rw [entryEq]
      exact (releasedImage old tree tag _ release).symm
  · have currentFrame : before.stack.currentFrame? = some frame := by simp [before, Stack.currentFrame?]
    have stackRelease : ∀ post failure, ProtectorReleaseWP.beforeStackPopPre retag.ensureTreeExtra post failure before ↔
        post {before with machine := released} := by
      intro post failure
      rw [ensure]
      exact beforeStackPopOfTree kind hooks storage.id tag before storage.entry storage.live synchronize
        region.tracker region.tracked frame currentFrame owned ledger one tree release post failure
    have stillCurrent : released.threads.activeThread? = some thread := current
    intro post failure
    exact popOfRelease retag older frame machine released stackRelease thread relevance stillCurrent cached post failure

/-- Release the active child and return to the caller with its raw rights. -/
theorem popExclusive (kind : K) (hooks : GlobalHooks) (retag : TypedRetag.Hooks K U)
    (ensure : retag.ensureTreeExtra = GlobalAllocationMachine.ensure kind hooks)
    (older : Array BorrowFrame) (frame : BorrowFrame) (machine : MachineHooks.MachineState K U)
    (length : UInt64) (storage : InitializedRegion (⟨⟨older.push frame⟩, machine⟩ : State) length)
    (tag : BorTag) (region : ExclusiveRegion (⟨⟨older.push frame⟩, machine⟩ : State) length storage tag)
    (synchronize : hooks.synchronizeMemory machine.memory ⟨machine, none⟩ = ⟨machine, none⟩)
    (owned : FrameState) (ledger : frame.extra.borrowTracker = some owned)
    (one : owned.protectedTags = #[(storage.id, tag)])
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (node : TreeNode) (nodeFound : storage.entry.allocation.extra.nodeAt region.source = some node)
    (unexposed : node.isExposed = false)
    (active : Every (ActiveByteRights storage.entry.allocation.extra region.tracker.global.protectedTags
      region.source) storage.entry.allocation.extra.locations)
    (fits : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (thread : ThreadRecord) (relevance : Nat)
    (current : machine.threads.activeThread? = some thread)
    (cached : FrameRelevance.top ⟨older.push frame⟩ thread.topUserRelevantFrame = some relevance) :
    ∃ after : State, after.stack.frames = older ∧ after.machine.user = machine.user ∧
      after.machine.dataRace = machine.dataRace ∧
      (∃ next : InitializedRegion after length, next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        Nonempty (ExclusiveRegion after length next tag)) ∧
      ∀ post failure, ProtectorReleaseWP.popRawPre retag post failure ⟨⟨older.push frame⟩, machine⟩ ↔ post frame after := by
  obtain ⟨after, stack, user, race, _, _, _, _, ⟨next, id, offset, _, _, _, _, rights, _, _⟩, exactPop⟩ :=
    popExclusive_with_frame kind hooks retag ensure older frame machine length storage tag region
      synchronize owned ledger one root roots node nodeFound unexposed active fits thread relevance current cached
  exact ⟨after, stack, user, race, ⟨next, id, offset, ⟨rights⟩⟩, exactPop⟩

#print axioms popExclusive

end DuplicatePrefix.RetagReleaseRights

import Miri.Verification.MemoryWP
import Miri.Verification.TreeRangeAccess

/-! Connect the current copy access to a permission proof and the clock,
policy, and keyed cache transitions for that access. -/
namespace DuplicatePrefix.SymbolicCopyAccess

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification Std.WP

variable {K U : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Machine" => PlaceMachine.Machine K U

/-- A permission proof for the ranged Tree Borrows operation feeds the
symbolic rule with the actual updated permission tree. -/
theorem permission_of_completed (tree : BorrowTree) (provenance : ProvenanceExtra)
    (range : AllocRange) (kind : AccessKind) (tags : ProtectedTags)
    (complete : (tree.performBorrowAccessRange provenance range.start range.size kind tags
      .VisitChildrenOfAccessed).status = .Completed) :
    let result := tree.performBorrowAccessRange provenance range.start range.size kind tags
      .VisitChildrenOfAccessed
    TreeBorrowsWP.accessPre tree provenance range.start range.size kind tags .VisitChildrenOfAccessed
      (fun updated _ => updated = result.tree) (fun _ _ _ => False) := by
  dsimp only
  simp only [TreeBorrowsWP.accessPre_iff, complete, eq_self]

private theorem permission_result (tree updated : BorrowTree) (provenance : ProvenanceExtra)
    (range : AllocRange) (kind : AccessKind) (tags : ProtectedTags)
    (permission : TreeBorrowsWP.accessPre tree provenance range.start range.size
      kind tags .VisitChildrenOfAccessed (fun actual _ => actual = updated) (fun _ _ _ => False)) :
    let result := tree.performBorrowAccessRange provenance range.start range.size kind tags
      .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = updated := by
  rw [TreeBorrowsWP.accessPre_iff] at permission
  dsimp only at permission ⊢
  generalize tree.performBorrowAccessRange provenance range.start range.size kind tags
    .VisitChildrenOfAccessed = result at permission ⊢
  rcases result with ⟨tree, visits, status⟩
  cases status <;> simp_all

private theorem cache_live (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (allocation : Allocation Provenance BorrowTree) (live : memory.live[id]? = some entry) :
    (if memory.live.contains id then memory.setLiveAllocation id allocation else .ok memory) =
      .ok {memory with live := memory.live.insert id {entry with allocation}} := by
  rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, live]
  exact memory.setLiveAllocation_of_find id entry allocation live

/-- Discharge a source read or destination write through the canonical copy
access, retaining the updated tree and the machine after synchronization. -/
theorem access_of_permission
    (config : PlaceMachine.AccessConfig K U) (write : Bool)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) (before : State)
    (diagnosed raced ready synced : Machine) (tracker : MachineHooks.BorrowState)
    (updated : BorrowTree) (liveEntry : LocalAllocation Provenance BorrowTree K)
    (diagnostic : config.diagnostic write id range before.machine = .ok () diagnosed)
    (race : MachineHooks.memoryRaceAccess diagnosed id range (if write then some .Write else none) .Read =
      (raced, .ok ()))
    (weak : if write then config.weakMemoryWrite id range raced = .ok () ready else ready = raced)
    (tracked : ready.borrowTracker = some tracker)
    (permission : TreeBorrowsWP.accessPre allocation.extra provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
      (fun actual _ => actual = updated) (fun _ _ _ => False))
    (synchronized : config.syncAccess write id range ready = .ok () synced)
    (live : synced.memory.live[id]? = some liveEntry) :
    let memory := {synced.memory with live := (synced.memory.live.insert id
      {liveEntry with allocation := allocation.setExtra updated})}
    wp (GlobalMemoryCopyMachine.access config write allocation id provenance range)
      (fun value after => value = allocation.setExtra updated ∧
        after = { before with machine := (config.retainTouched {synced with memory}
          (some ⟨id, range, allocation.setExtra updated⟩)) }) (fun _ _ => False) before := by
  have cached := cache_live synced.memory id liveEntry (allocation.setExtra updated) live
  dsimp only
  rw [MemoryWP.copyAccess_iff]
  simp only [MemoryWP.memoryAccessPre, MemoryWP.policyPre, wp, WP.wpTrans, diagnostic, race]
  cases write <;> simp only [Bool.false_eq_true, ↓reduceIte] at weak permission synchronized ⊢
  · subst ready
    rw [tracked]
    have checked := permission_result _ _ _ _ _ _ permission
    simp only [TreeBorrowsWP.accessPre_iff, checked.1, checked.2, synchronized,
      MemoryWP.copyAccessCommitPre, cached, and_self]
  · simp only [weak, tracked]
    have checked := permission_result _ _ _ _ _ _ permission
    simp only [TreeBorrowsWP.accessPre_iff, checked.1, checked.2, synchronized,
      MemoryWP.copyAccessCommitPre, cached, and_self]

/-- Apply the actual copy access using permission facts for each prepared
iterator position. Both the ranged traversal and cache commit are verified. -/
theorem access_of_slots
    (config : PlaceMachine.AccessConfig K U) (write : Bool)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) (before : State)
    (diagnosed raced ready synced : Machine) (tracker : MachineHooks.BorrowState)
    (liveEntry : LocalAllocation Provenance BorrowTree K)
    (prepared : IterMutResult LocationTree) (source : Option UniIndex)
    (diagnostic : config.diagnostic write id range before.machine = .ok () diagnosed)
    (race : MachineHooks.memoryRaceAccess diagnosed id range (if write then some .Write else none) .Read =
      (raced, .ok ()))
    (weak : if write then config.weakMemoryWrite id range raced = .ok () ready else ready = raced)
    (tracked : ready.borrowTracker = some tracker)
    (selected : match provenance with
      | .concrete tag => ∃ index, source = some index ∧ allocation.extra.indexOfTag tag = some index
      | .wildcard => source = none)
    (prepare : allocation.extra.locations.iterMut range.start range.size = prepared)
    (okay : prepared.outcome = .ok ())
    (owned : TreeRangeAccess.SlotsAuthorized allocation.extra prepared source
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed)
    (synchronized : config.syncAccess write id range ready = .ok () synced)
    (live : synced.memory.live[id]? = some liveEntry) :
    let result := allocation.extra.performBorrowAccessRange provenance range.start range.size
      (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
    let updated := allocation.setExtra result.tree
    let memory := {synced.memory with live := (synced.memory.live.insert id
      {liveEntry with allocation := updated})}
    wp (GlobalMemoryCopyMachine.access config write allocation id provenance range)
      (fun value after => value = updated ∧
        after = {before with machine := (config.retainTouched {synced with memory}
          (some ⟨id, range, updated⟩))}) (fun _ _ => False) before := by
  have complete := TreeRangeAccess.rangeComplete allocation.extra provenance range.start range.size
    _ tracker.global.protectedTags .VisitChildrenOfAccessed prepared source selected prepare okay owned
  exact access_of_permission config write allocation id provenance range before diagnosed raced ready
    synced tracker _ liveEntry diagnostic race weak tracked
    (permission_of_completed allocation.extra provenance range _ _ complete) synchronized live

/-- The destination copy hook propagates an actual Tree Borrows failure
with its partially updated tree, without calling synchronization. -/
theorem write_of_tree_failure
    (config : PlaceMachine.AccessConfig K U)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) (before : State)
    (diagnosed raced ready : Machine) (tracker : MachineHooks.BorrowState)
    (updated : BorrowTree) (status : BorrowTree.BorrowTreeAccessStatus)
    (liveEntry : LocalAllocation Provenance BorrowTree K)
    (diagnostic : config.diagnostic true id range before.machine = .ok () diagnosed)
    (race : MachineHooks.memoryRaceAccess diagnosed id range (some .Write) .Read = (raced, .ok ()))
    (weak : config.weakMemoryWrite id range raced = .ok () ready)
    (tracked : ready.borrowTracker = some tracker)
    (permission : TreeBorrowsWP.accessPre allocation.extra provenance range.start range.size
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed (fun _ _ => False)
      (fun reason actual _ => reason = status ∧ actual = updated))
    (live : ready.memory.live[id]? = some liveEntry) :
    let memory := {ready.memory with live := (ready.memory.live.insert id
      {liveEntry with allocation := allocation.setExtra updated})}
    wp (GlobalMemoryCopyMachine.access config true allocation id provenance range)
      (fun _ _ => False)
      (fun error after => error = PlaceMachine.treeError true status ∧
        after = { before with machine := (config.retainTouched {ready with memory}
          (some ⟨id, range, allocation.setExtra updated⟩)) }) before := by
  have cached := cache_live ready.memory id liveEntry (allocation.setExtra updated) live
  dsimp only
  rw [MemoryWP.copyAccess_iff]
  simp only [MemoryWP.memoryAccessPre, MemoryWP.policyPre, wp, WP.wpTrans, diagnostic,
    ↓reduceIte, race, weak, tracked, TreeBorrowsWP.accessPre_iff] at permission ⊢
  generalize allocation.extra.performBorrowAccessRange provenance range.start range.size
    .Write tracker.global.protectedTags .VisitChildrenOfAccessed = result at permission ⊢
  rcases result with ⟨tree, visits, reason⟩
  cases reason <;> simp at permission
  all_goals
    obtain ⟨rfl, rfl⟩ := permission
    simp only [MemoryWP.failurePre, MemoryWP.copyAccessCommitPre, cached,
      Option.getD_some, tracked, eq_self, and_self]

/-- A denied write to a protected frozen node reaches the diagnostic UB
class in the ordinary no-UB postcondition. -/
theorem protected_frozen_is_ub (range : ByteRange) (node : Nat) :
    RunLoop.reportsUB (PlaceMachine.treeError true
      (.AccessFailure range (.TransitionError node (.ProtectedDisabled .Frozen)))) = true := rfl

#print axioms permission_of_completed
#print axioms access_of_permission
#print axioms access_of_slots
#print axioms write_of_tree_failure
#print axioms protected_frozen_is_ub
end DuplicatePrefix.SymbolicCopyAccess

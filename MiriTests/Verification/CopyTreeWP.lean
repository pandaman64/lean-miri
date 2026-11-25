import Miri.Verification.CopyTreeWP
import Init.Internal.Order.While

namespace MiriTests.Verification.CopyTreeWP

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification Std.WP

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def byte := Size.ofBytes 1
private def twoBytes := Size.ofBytes 2
private def root (size : Size) := BorrowTree.new BorTag.one size
private def tag : ProvenanceExtra := .concrete BorTag.one

/-- The write shares the second byte of the read and also reaches a byte
outside it. This checks only the tree hooks. The nonoverlap flag is checked
by the subsequent physical copy. -/
example : TreeRangePointwiseWP.readWritePre (root (Size.ofBytes 3)) tag tag
    Size.ZERO twoBytes byte twoBytes {} {} .VisitChildrenOfAccessed .VisitChildrenOfAccessed := by
  apply (CopyTreeWP.permissions_pointwise_iff _ _ _ (allocRange Size.ZERO twoBytes)
    (allocRange byte twoBytes) {} {}).mp
  simp only [TreeBorrowsWP.accessPre_iff]
  cbv

/-- On each outcome the cache exposes the updated tree at the accessed ID
and preserves the other allocation. A borrow failure preserves its typed
error and still passes the partial tree to the cache. -/
example {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (before : MachineHooks.State K U)
    (state : PlaceMachine.AccessState K U) (source other : AllocId)
    (allocation : Allocation Provenance BorrowTree) (range : AllocRange)
    (entry : LocalAllocation Provenance BorrowTree K) (updated : BorrowTree) (error : StepError)
    (typed : state.pendingError = some error)
    (live : state.machine.memory.live[source]? = some entry) (distinct : source ≠ other)
    (retain : ∀ machine touched, (config.retainTouched machine touched).memory = machine.memory) :
    let seeTrees := fun (after : MachineHooks.State K U) =>
      after.machine.memory.live[source]?.map (·.allocation.extra) = some updated ∧
      after.machine.memory.live[other]?.map (·.allocation.extra) =
        state.machine.memory.live[other]?.map (·.allocation.extra)
    MemoryWP.copyAccessCommitPre config before allocation source range state updated (.ok ())
      (fun result after => result.extra = updated ∧ seeTrees after) (fun _ _ => False) ∧
    MemoryWP.copyAccessCommitPre config before allocation source range state updated (.error (reprStr error))
      (fun _ _ => False) (fun actual after => actual = error ∧ seeTrees after) := by
  dsimp only
  have see :
      ((state.machine.memory.live.insert source {entry with allocation := allocation.setExtra updated})[source]?).map
        (·.allocation.extra) = some updated ∧
      ((state.machine.memory.live.insert source {entry with allocation := allocation.setExtra updated})[other]?).map
        (·.allocation.extra) = state.machine.memory.live[other]?.map (·.allocation.extra) := by
    rw [(CopyTreeWP.committedLookup _ source source entry _ live).2,
      (CopyTreeWP.committedLookup _ source other entry _ live).2]
    simp only [distinct, ↓reduceIte, Option.map_some]
    exact ⟨rfl, trivial⟩
  constructor <;> rw [CopyTreeWP.commitLocal_iff config before allocation source range state updated entry live]
  · exact ⟨rfl, by simpa only [retain] using see⟩
  · refine ⟨by simp only [typed, Option.getD_some], ?_⟩
    simpa only [retain] using see

/-- A resolved destination can fail its actual tracked write. The error
continuation observes the pre-synchronization machine and its cache commit. -/
example {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (before : MachineHooks.State K U)
    (destination : AllocId) (allocation : Allocation Provenance BorrowTree)
    (range : AllocRange) (tag : BorTag)
    (ready : CopyTreeWP.Ready config true destination range before)
    (missing : allocation.extra.indexOfTag tag = none)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : ready.machine.memory.live[destination]? = some entry) :
    wp (GlobalMemoryCopyMachine.access config true allocation destination (.concrete tag) range)
      (fun _ _ => False)
      (fun error after =>
        let touched := allocation.setExtra allocation.extra
        let memory := {ready.machine.memory with live :=
          (ready.machine.memory.live.insert destination {entry with allocation := touched})}
        error = PlaceMachine.treeError true (.MissingTag tag) ∧
          after = {before with machine :=
            config.retainTouched {ready.machine with memory} (some ⟨destination, range, touched⟩)})
      before := by
  rw [CopyTreeWP.access_iff config true allocation destination (.concrete tag) range before ready]
  rw [TreeBorrowsWP.accessPre_missingTag _ _ _ _ _ _ _ _ _ missing]
  rw [CopyTreeWP.commitLocal_iff _ _ _ _ _ _ _ _ live]
  exact ⟨rfl, rfl⟩

private def childTag : BorTag := ⟨2, by decide⟩
private def destinationRange := allocRange byte byte
private def sourceTree := (root twoBytes).newChild byte tag childTag
  (DedupRangeMap.new byte ⟨.Unique, true, .None⟩) (.ReservedFrz false) false
private def readTree := (sourceTree.tree.performBorrowAccessRange tag Size.ZERO byte .Read {}
  .VisitChildrenOfAccessed).tree

private theorem source_read :
    (sourceTree.tree.performBorrowAccessRange tag Size.ZERO byte .Read {} .VisitChildrenOfAccessed).status =
      .Completed := by cbv

private def firstLocation : LocationTree := (readTree.locations.entries[0]?.map (·.data)).getD {}
private def secondLocation : LocationTree := (readTree.locations.entries[1]?.map (·.data)).getD {}
private theorem readEntries : readTree.locations.entries =
    #[⟨⟨0, 1⟩, firstLocation⟩, ⟨⟨1, 2⟩, secondLocation⟩] := by cbv

private theorem readFormed : readTree.locations.WellFormed := by
  unfold DedupRangeMap.WellFormed
  have count : readTree.locations.entries.size = 2 := by rw [readEntries]; rfl
  rw [dite_eq_right (by omega : readTree.locations.entries.size ≠ 0)]
  refine ⟨by cbv, ?_, ?_⟩
  · intro n inside
    have possible : n = 0 ∨ n = 1 := by omega
    rcases possible with rfl | rfl <;> cbv
  · intro n inside
    have only : n = 0 := by omega
    subst n
    cbv

private theorem destinationAt {position : UInt64} {location : LocationTree}
    (found : readTree.locations.MapAt position location)
    (covered : ByteRange.Contains ⟨1, 2⟩ position) : location = secondLocation := by
  obtain ⟨index, segment, entry, contains, value⟩ := found
  rw [readEntries] at entry
  have inside := (Array.getElem?_eq_some_iff.mp entry).choose
  have possible : index = 0 ∨ index = 1 := by simp at inside; omega
  rcases possible with rfl | rfl
  · simp at entry
    subst segment
    exact False.elim (UInt64.not_lt.mpr covered.1 contains.2)
  · simp at entry
    subst segment
    exact value.symm

set_option maxHeartbeats 1200000 in
/-- At the destination of a tracked copy, after an accepted source read,
the root can read the newly written location. The third access through the
stale child fails, and the failure state retains the new permission. -/
theorem tracked_copy_observes_write {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K U) (before : MachineHooks.State K U)
    (id : AllocId) (backing : Allocation Provenance BorrowTree)
    (ready : CopyTreeWP.Ready config true id destinationRange before)
    (unprotected : ready.tracker.global.protectedTags = {})
    (synced : PlaceMachine.Machine K U) (sync : config.syncAccess true id destinationRange ready.machine = .ok () synced)
    (entry : LocalAllocation Provenance BorrowTree K) (live : synced.memory.live[id]? = some entry) :
    CopyTreeWP.accessPre config true (backing.setExtra readTree) id tag destinationRange
      (fun written _ =>
        (∃ observed, written.extra.locations.MapAt 1 observed ∧
          (observed.perms.get ⟨1⟩).map (·.permission) = some .Disabled) ∧
        TreeBorrowsWP.accessPre written.extra tag byte byte .Read {} .VisitChildrenOfAccessed
          (fun _ _ => True) (fun _ _ _ => False) ∧
        TreeBorrowsWP.accessPre written.extra (.concrete childTag) byte byte .Read {} .VisitChildrenOfAccessed
          (fun _ _ => False) (fun status retained trace =>
            status = .AccessFailure ⟨1, 2⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)) ∧
            trace.map (·.range) = #[⟨1, 2⟩] ∧
            ((retained.locations.entries[1]?.bind fun segment => segment.data.perms.get ⟨1⟩).map
              (·.permission)) = some .Disabled)) (fun _ _ => False) before := by
  have endpoint : destinationRange.start.add destinationRange.size = .ok twoBytes := by cbv
  have bound : twoBytes.bytes ≤ readTree.locations.size.bytes := by cbv
  miri_copy_tree_wp observe using ready, readFormed, endpoint, bound
  dsimp only [Allocation.setExtra]
  simp only [↓reduceIte]
  simp only [unprotected, TreeOverlapWP.accessBytePre, TreeOverlapWP.byteChecks]
  refine ⟨⟨by cbv, ?_⟩, ?_⟩
  · intro position location found covered
    rw [destinationAt found covered]
    cbv
  · intro _ _ _ observation
    dsimp only [MemoryWP.policyPre, wp, WP.wpTrans]
    rw [sync]
    dsimp only
    rw [CopyTreeWP.commitLocal_iff _ _ _ _ _ _ _ _ live]
    simp only [Allocation.setExtra]
    refine ⟨?_, by cbv; exact ⟨trivial, trivial⟩⟩
    have initialAt : readTree.locations.MapAt 1 secondLocation :=
      ⟨1, ⟨⟨1, 2⟩, secondLocation⟩, by rw [readEntries]; rfl, by cbv, rfl⟩
    have inside : ByteRange.Contains ⟨1, 2⟩ 1 := by cbv
    refine ⟨_, (observation 1 _).mpr ⟨secondLocation, initialAt, fun _ => rfl,
      fun h => (h inside).elim⟩, by cbv⟩

#print axioms source_read
#print axioms tracked_copy_observes_write

end MiriTests.Verification.CopyTreeWP

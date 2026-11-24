import Miri.Verification.CopyTreeWP
import Init.Internal.Order.While

namespace MiriTests.Verification.CopyTreeWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification Std.WP

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

end MiriTests.Verification.CopyTreeWP

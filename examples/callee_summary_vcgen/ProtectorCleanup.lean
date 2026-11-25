import Miri.Verification.ProtectorReleaseWP

/-! The writeback on release updates the live allocation's Tree Borrows
extra and removes the callee's protector from the global index. -/
namespace CalleeSummaryExample

open Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification

variable {K U : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U

/-- At the protector-release part of normal return, a single live protector
can be discharged symbolically. The post records the resulting tree and
shows that the actual release keeps the caller allocation's bytes and
removes the protected tag. -/
theorem release_singleton
    (ensureTreeExtra : AllocId → MachineHooks.M K U Unit)
    (before : State) (allocation : AllocId) (tag : BorTag)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (tracker : MachineHooks.BorrowState) (entry : LocalAllocation Provenance BorrowTree K)
    (current : before.stack.currentFrame? = some frame)
    (owned : frame.extra.borrowTracker = some ⟨#[(allocation, tag)]⟩)
    (tracking : before.machine.borrowTracker = some tracker)
    (live : before.machine.memory.live[allocation]? = some entry)
    (extraReady : ensureTreeExtra allocation before = .ok () before)
    (release : ProtectorReleaseWP.releasePre tag tracker.global.protectedTags
      (fun _ => True) (fun _ _ => False) entry.allocation.extra) :
    ∃ after updated updatedTracker,
      MachineHooks.beforeStackPopWithEnsure ensureTreeExtra before = .ok () after ∧
      after.stack = before.stack ∧
      after.machine.memory.live[allocation]? = some updated ∧
      (∀ range, updated.allocation.getBytesUnchecked range = entry.allocation.getBytesUnchecked range) ∧
      after.machine.borrowTracker = some updatedTracker ∧
      updatedTracker.global.protectedTags.get tag = none := by
  let post (after : State) :=
    ∃ updated updatedTracker, after.stack = before.stack ∧
      after.machine.memory.live[allocation]? = some updated ∧
      (∀ range, updated.allocation.getBytesUnchecked range = entry.allocation.getBytesUnchecked range) ∧
      after.machine.borrowTracker = some updatedTracker ∧
      updatedTracker.global.protectedTags.get tag = none
  have ready : ProtectorReleaseWP.beforeStackPopPre ensureTreeExtra post
      (fun _ _ => False) before := by
    have info : before.machine.memory.getAllocInfo allocation =
        .ok ⟨entry.allocation.byteSize, entry.allocation.align, .liveData,
          entry.allocation.mutability⟩ := by
      simp [MemoryState.getAllocInfo, live]
      rfl
    simp only [ProtectorReleaseWP.beforeStackPopPre, tracking, Option.isSome_some,
      ↓reduceIte, current, owned, ProtectorReleaseWP.stackEntriesPre,
      ProtectorReleaseWP.stackEntryPre, info, beq_self_eq_true, RvalueWP.actionPre,
      extraReady, live, MemoryState.setLiveAllocation_of_find _ _ _ _ live]
    rw [ProtectorReleaseWP.releasePre_iff] at release ⊢
    cases run : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags with
    | mk tree status =>
      rw [run] at release
      cases status <;> try exact False.elim release
      refine ⟨{entry with allocation := entry.allocation.setExtra tree}, _, rfl, ?_, ?_, rfl, ?_⟩
      · simp
      · intro range
        rfl
      · simp [GlobalState.endCall]
  have checked := (ProtectorReleaseWP.beforeStackPopPre_iff ensureTreeExtra post
    (fun _ _ => False) before).mp ready
  unfold RvalueWP.actionPre at checked
  cases run : MachineHooks.beforeStackPopWithEnsure ensureTreeExtra before with
  | error error failed =>
    rw [run] at checked
    exact False.elim checked
  | ok success after =>
    rw [run] at checked
    obtain ⟨updated, updatedTracker, stack, read, bytes, enabled, gone⟩ := checked
    cases success
    exact ⟨after, updated, updatedTracker, rfl, stack, read, bytes, enabled, gone⟩

#print axioms release_singleton

end CalleeSummaryExample

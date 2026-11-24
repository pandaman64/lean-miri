import Miri.Verification.ProtectorReleaseWP
import Miri.Interpreter.GlobalAllocationMachine

namespace DuplicatePrefix.ZeroTail
open Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification

/-- No location has recorded an access through the newly installed tag.
Entries for other tags and their history need not have any particular shape. -/
def protectorUnused (tree : BorrowTree) (source : UniIndex) (position : Nat) : Prop :=
  ∃ segment, tree.locations.index position = .ok segment ∧
    ∀ state, segment.data.perms.get source = some state → state.accessed = false

private theorem segments_unused (tag : BorTag) (tags : ProtectedTags) (source : UniIndex)
    (post : BorrowTree → Prop) (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop)
    (tree : BorrowTree) (positions : List Nat)
    (unused : ∀ position ∈ positions, protectorUnused tree source position)
    (index : tree.indexOfTag tag = some source)
    (node : TreeNode) (found : tree.nodeAt source = some node) (unexposed : node.isExposed = false) :
    ProtectorReleaseWP.segmentsPre tag tags source post failure positions tree ↔ post tree := by
  induction positions with
  | nil =>
    simp [ProtectorReleaseWP.segmentsPre, BorrowTree.MutationVerification.releaseExposurePre, index, found, unexposed]
  | cons position rest ih =>
    obtain ⟨segment, indexed, untouched⟩ := unused position (by simp)
    have smaller : ∀ position ∈ rest, protectorUnused tree source position := by
      intro position member
      exact unused position (by simp [member])
    simp only [ProtectorReleaseWP.segmentsPre, ProtectorReleaseWP.segmentPre, indexed]
    cases entry : segment.data.perms.get source with
    | none => simpa only [entry] using ih smaller
    | some state =>
      cases kind : state.permission.associatedAccess <;>
        simpa only [entry, kind, untouched state entry, Bool.false_eq_true, ↓reduceIte] using ih smaller

/-- Releasing an unused, unexposed protected tag preserves the complete live
tree and cannot invoke a release access. This applies to arbitrary histories
of all other tags in the same allocation. -/
theorem release_unused (tree : BorrowTree) (tag : BorTag) (tags : ProtectedTags)
    (source : UniIndex) (index : tree.indexOfTag tag = some source)
    (node : TreeNode) (found : tree.nodeAt source = some node) (unexposed : node.isExposed = false)
    (unused : ∀ position < tree.locations.entries.size, protectorUnused tree source position)
    (post : BorrowTree → Prop) (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) :
    ProtectorReleaseWP.releasePre tag tags post failure tree ↔ post tree := by
  unfold ProtectorReleaseWP.releasePre
  rw [index]
  apply segments_unused tag tags source post failure tree _ _ index node found unexposed
  intro position member
  exact unused position (by simpa using member)

variable {K U : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "GlobalHooks" => GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U)

private theorem ensureLive (kind : K) (hooks : GlobalHooks) (id : AllocId) (before : State)
    (entry : LocalAllocation Provenance BorrowTree K)
    (present : before.machine.memory.live[id]? = some entry)
    (synchronize : hooks.synchronizeMemory before.machine.memory ⟨before.machine, none⟩ =
      ⟨before.machine, none⟩) :
    GlobalAllocationMachine.ensure kind hooks id before = .ok () before := by
  cases before with
  | mk stack machine =>
    simp [GlobalAllocationMachine.ensure, MemoryLifecycle.getAllocRaw, present, synchronize, Id.run,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
      EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet] <;> rfl

/-- The actual release action on a live allocation with a dormant protector
writes back the same Tree Borrows state. Arbitrary unrelated tags, bytes and
permissions are retained. -/
theorem stackEntry_unused (kind : K) (hooks : GlobalHooks) (id : AllocId) (tag : BorTag)
    (before : State) (entry : LocalAllocation Provenance BorrowTree K)
    (present : before.machine.memory.live[id]? = some entry)
    (synchronize : hooks.synchronizeMemory before.machine.memory ⟨before.machine, none⟩ =
      ⟨before.machine, none⟩)
    (tracker : MachineHooks.BorrowState) (tracked : before.machine.borrowTracker = some tracker)
    (source : UniIndex) (index : entry.allocation.extra.indexOfTag tag = some source)
    (node : TreeNode) (found : entry.allocation.extra.nodeAt source = some node)
    (unexposed : node.isExposed = false)
    (unused : ∀ position < entry.allocation.extra.locations.entries.size,
      protectorUnused entry.allocation.extra source position)
    (next : State → Prop) (failure : StepError → State → Prop) :
    let memory := { before.machine.memory with
      live := before.machine.memory.live.insert id { entry with
        allocation := entry.allocation.setExtra entry.allocation.extra } }
    ProtectorReleaseWP.stackEntryPre (GlobalAllocationMachine.ensure kind hooks) id tag next failure before ↔
      next { before with machine := { before.machine with memory } } := by
  have info : before.machine.memory.getAllocInfo id = .ok
      ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo, present] <;> rfl
  simp only [ProtectorReleaseWP.stackEntryPre, info, beq_self_eq_true, ↓reduceIte,
    RvalueWP.actionPre, ensureLive kind hooks id before entry present synchronize, present, tracked]
  rw [release_unused entry.allocation.extra tag tracker.global.protectedTags
    source index node found unexposed unused]
  rw [MemoryState.setLiveAllocation_of_find _ _ _ _ present]

/-- End the call's protector ownership after the live release. The release
traversal and the ledger update retain their source order. -/
theorem stackPop_unused (kind : K) (hooks : GlobalHooks) (id : AllocId) (tag : BorTag)
    (before : State) (entry : LocalAllocation Provenance BorrowTree K)
    (present : before.machine.memory.live[id]? = some entry)
    (synchronize : hooks.synchronizeMemory before.machine.memory ⟨before.machine, none⟩ =
      ⟨before.machine, none⟩)
    (tracker : MachineHooks.BorrowState) (tracked : before.machine.borrowTracker = some tracker)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (current : before.stack.currentFrame? = some frame)
    (owned : FrameState) (ownership : frame.extra.borrowTracker = some owned)
    (ownedTags : owned.protectedTags = #[(id, tag)])
    (source : UniIndex) (index : entry.allocation.extra.indexOfTag tag = some source)
    (node : TreeNode) (found : entry.allocation.extra.nodeAt source = some node)
    (unexposed : node.isExposed = false)
    (unused : ∀ position < entry.allocation.extra.locations.entries.size,
      protectorUnused entry.allocation.extra source position)
    (post : State → Prop) (failure : StepError → State → Prop) :
    let memory := { before.machine.memory with
      live := before.machine.memory.live.insert id { entry with
        allocation := entry.allocation.setExtra entry.allocation.extra } }
    let afterTracker := { tracker with global := tracker.global.endCall owned }
    ProtectorReleaseWP.beforeStackPopPre (GlobalAllocationMachine.ensure kind hooks) post failure before ↔
      post { before with machine := { before.machine with memory, borrowTracker := some afterTracker } } := by
  let finish : State → Prop := fun after =>
    match after.machine.borrowTracker with
    | none => failure (.invalidProgram "borrow tracker removed during stack pop") after
    | some current =>
      post { after with machine := { after.machine with
        borrowTracker := some { current with global := current.global.endCall owned } } }
  have h := stackEntry_unused kind hooks id tag before entry present synchronize tracker tracked
    source index node found unexposed unused finish failure
  dsimp only at h
  simp [ProtectorReleaseWP.beforeStackPopPre, tracked, current, ownership, ownedTags,
    ProtectorReleaseWP.stackEntriesPre, finish] at h ⊢
  with_unfolding_all exact h

#print axioms release_unused
#print axioms stackEntry_unused
#print axioms stackPop_unused
end DuplicatePrefix.ZeroTail

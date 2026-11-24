import duplicate_prefix.ActiveReleaseRange
import Miri.Interpreter.GlobalAllocationMachine
import duplicate_prefix.AllocationCopy

namespace DuplicatePrefix.ActiveRelease
open Miri.Concurrency Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification

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

/-- Release one structurally authorized active protector in the live allocation
map and then update ownership. The source data determine the complete saved
tree, keyed allocation update, and final protector ledger. -/
theorem beforeStackPop (kind : K) (hooks : GlobalHooks) (id : AllocId) (tag : BorTag)
    (before : State) (entry : LocalAllocation Provenance BorrowTree K)
    (present : before.machine.memory.live[id]? = some entry)
    (synchronize : hooks.synchronizeMemory before.machine.memory ⟨before.machine, none⟩ =
      ⟨before.machine, none⟩)
    (tracker : MachineHooks.BorrowState) (tracked : before.machine.borrowTracker = some tracker)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (current : before.stack.currentFrame? = some frame)
    (owned : FrameState) (ownership : frame.extra.borrowTracker = some owned)
    (ownedTags : owned.protectedTags = #[(id, tag)])
    (source root : UniIndex) (index : entry.allocation.extra.indexOfTag tag = some source)
    (roots : entry.allocation.extra.roots = #[root])
    (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (node : TreeNode) (found : entry.allocation.extra.nodeAt source = some node)
    (unexposed : node.isExposed = false)
    (authorized : ∀ position < entry.allocation.extra.locations.entries.size, ∃ slot,
      entry.allocation.extra.locations.index position = .ok slot ∧
        ReleaseOwnership entry.allocation.extra source root tracker.global.protectedTags slot) :
    ∃ after, after.stack = before.stack ∧ after.machine.threads = before.machine.threads ∧
      after.machine.user = before.machine.user ∧
      ∀ post failure, ProtectorReleaseWP.beforeStackPopPre (GlobalAllocationMachine.ensure kind hooks) post failure before ↔
        post after := by
  obtain ⟨tree, released⟩ := releaseAll entry.allocation.extra tag source root
    tracker.global.protectedTags index roots depth children node found unexposed authorized
  let memory := { before.machine.memory with
    live := before.machine.memory.live.insert id { entry with allocation := entry.allocation.setExtra tree } }
  let afterTracker := { tracker with global := tracker.global.endCall owned }
  refine ⟨{ before with machine := { before.machine with memory, borrowTracker := some afterTracker } }, rfl, rfl, rfl, ?_⟩
  intro post failure
  have info : before.machine.memory.getAllocInfo id = .ok
      ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo, present] <;> rfl
  simp only [ProtectorReleaseWP.beforeStackPopPre, tracked, Option.isSome_some, ↓reduceIte,
    current, ownership, ownedTags]
  change ProtectorReleaseWP.stackEntryPre (GlobalAllocationMachine.ensure kind hooks) id tag
    (fun after =>
      match after.machine.borrowTracker with
      | none => failure (.invalidProgram "borrow tracker removed during stack pop") after
      | some current => post { after with machine := { after.machine with
          borrowTracker := some { current with global := current.global.endCall owned } } })
    failure before ↔ _
  simp only [ProtectorReleaseWP.stackEntryPre, info, beq_self_eq_true, ↓reduceIte, RvalueWP.actionPre,
    ensureLive kind hooks id before entry present synchronize, present, tracked]
  rw [released]
  rw [MemoryState.setLiveAllocation_of_find _ _ _ _ present]

private def atFrame (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (machine : MachineHooks.MachineState K U) : State :=
  ⟨⟨older.push frame⟩, machine⟩

def afterRelevance (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (index : Nat) : MachineHooks.MachineState K U :=
  if index = older.size then
    let cached := FrameRelevance.computeTop ⟨older.push frame⟩ 1
    {machine with threads := {machine.threads with threads := machine.threads.threads.mapIdx fun position thread =>
      if position == machine.threads.activeThread.toNat then
        {thread with topUserRelevantFrame := cached} else thread}}
  else machine

private theorem relevance (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord) (index : Nat)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨older.push frame⟩ thread.topUserRelevantFrame = some index) :
    FrameRelevance.beforeStackPop (atFrame older frame machine) =
      .ok () (atFrame older frame (afterRelevance older frame machine index)) := by
  unfold FrameRelevance.beforeStackPop
  unfold_internal ".FrameRelevance.active"
  simp only [atFrame, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    active, pure, EStateM.pure, top, Array.size_push, Nat.add_sub_cancel]
  by_cases topFrame : index = older.size
  · simp only [topFrame, beq_self_eq_true, ↓reduceIte]
    unfold_internal ".FrameRelevance.setCache"
    unfold_internal ".FrameRelevance.active"
    simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, active, afterRelevance,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure, atFrame]
  · simp [afterRelevance, topFrame] <;> rfl

/-- Continue an exact release proof through source frame relevance and the
actual raw frame removal, returning the exact detached frame and caller stack. -/
theorem popOfRelease (retag : TypedRetag.Hooks K U)
    (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (initial released : MachineHooks.MachineState K U)
    (release : ∀ post failure, ProtectorReleaseWP.beforeStackPopPre retag.ensureTreeExtra post failure
      (atFrame older frame initial) ↔ post (atFrame older frame released))
    (thread : ThreadRecord) (index : Nat)
    (active : released.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨older.push frame⟩ thread.topUserRelevantFrame = some index)
    (post : Frame Provenance LocalLayout MachineHooks.FrameExtra → State → Prop)
    (failure : StepError → State → Prop) :
    ProtectorReleaseWP.popRawPre retag post failure (atFrame older frame initial) ↔
      post frame ⟨⟨older⟩, afterRelevance older frame released index⟩ := by
  rw [ProtectorReleaseWP.popRawPre, release]
  unfold RvalueWP.actionPre
  rw [relevance older frame released thread index active top]
  simp [
    atFrame, Stack.popFrame, Array.back?_push, Array.pop_push, Except.pure, Pure.pure]

/-- Structurally owned active bytes suffice to pop the current frame.
The result carries the actual keyed allocation and protector-ledger update
followed by the frame-relevance update. -/
theorem popOfOwnership (kind : K) (hooks : GlobalHooks) (retag : TypedRetag.Hooks K U)
    (ensure : retag.ensureTreeExtra = GlobalAllocationMachine.ensure kind hooks)
    (id : AllocId) (tag : BorTag)
    (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (entry : LocalAllocation Provenance BorrowTree K)
    (present : machine.memory.live[id]? = some entry)
    (synchronize : hooks.synchronizeMemory machine.memory ⟨machine, none⟩ = ⟨machine, none⟩)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (owned : FrameState) (ownership : frame.extra.borrowTracker = some owned)
    (ownedTags : owned.protectedTags = #[(id, tag)])
    (source root : UniIndex) (index : entry.allocation.extra.indexOfTag tag = some source)
    (roots : entry.allocation.extra.roots = #[root])
    (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (node : TreeNode) (found : entry.allocation.extra.nodeAt source = some node)
    (unexposed : node.isExposed = false)
    (authorized : ∀ position < entry.allocation.extra.locations.entries.size, ∃ slot,
      entry.allocation.extra.locations.index position = .ok slot ∧
        ReleaseOwnership entry.allocation.extra source root tracker.global.protectedTags slot)
    (thread : ThreadRecord) (relevant : Nat)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨older.push frame⟩ thread.topUserRelevantFrame = some relevant) :
    ∃ popped, popped.user = machine.user ∧
      ∀ post failure, ProtectorReleaseWP.popRawPre retag post failure (atFrame older frame machine) ↔
        post frame ⟨⟨older⟩, popped⟩ := by
  have current : (atFrame older frame machine).stack.currentFrame? = some frame := by
    simp [atFrame, Stack.currentFrame?]
  obtain ⟨released, stack, threads, user, checked⟩ := beforeStackPop kind hooks id tag
    (atFrame older frame machine) entry present synchronize tracker tracked frame current
    owned ownership ownedTags source root index roots depth children node found unexposed authorized
  have sameFrame : atFrame older frame released.machine = released := by
    cases released
    simp only [atFrame] at stack ⊢
    simp only [stack]
  have release : ∀ post failure, ProtectorReleaseWP.beforeStackPopPre retag.ensureTreeExtra post failure
      (atFrame older frame machine) ↔ post (atFrame older frame released.machine) := by
    intro post failure
    rw [ensure, sameFrame]
    exact checked post failure
  refine ⟨afterRelevance older frame released.machine relevant, ?_, ?_⟩
  · unfold afterRelevance
    split <;> exact user
  intro post failure
  apply popOfRelease retag older frame machine released.machine release thread relevant
  · exact threads ▸ active
  · exact top

#print axioms popOfOwnership
#print axioms popOfRelease
#print axioms beforeStackPop
end DuplicatePrefix.ActiveRelease

import duplicate_prefix.SharedReborrowContinuity
import Miri.Verification.MutableTypedRetag

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.Tree
open SourceDomain GeneralRangeMapOrigins RetagLocationFrame RetagSharedChild
open RetagPolicy Miri.Verification.MutableTypedRetag
open Miri.Verification

variable {K U : Type}
local notation "State" => MachineHooks.State K U

set_option maxRecDepth 65536
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

private theorem uniform_shared_segments (offset length capacity : Size)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ capacity.bytes.toNat) :
    ∀ segment ∈ (DedupRangeMap.new length sharedState).iterAll.toList,
      (segment.range.start ≤ segment.range.stop ∧
        offset.bytes.toNat + segment.range.stop.toNat ≤ capacity.bytes.toNat) ∧
      segment.data = sharedState := by
  intro segment member
  by_cases empty : length.bytes = 0
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, empty] at member
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, beq_iff_eq, empty] at member
    subst segment
    exact ⟨⟨by simp, bounds⟩, rfl⟩

def protectedShared : NewPermission := ⟨.Frozen, .Cell, .Frozen, some .StrongProtector⟩

/-- The actual FnEntry shared retag records the strong protector in the
callee and derives the fresh readable child from structural read rights. -/
theorem typed_shared_fn_entry [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (length : Size) (tag parentTag : BorTag)
    (parent root : UniIndex) (location : RetagPipeline.ResolvedLocation)
    (before pointed resolved logged : State)
    (chosenFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (ledger : FrameState)
    (current : logged.stack.currentFrame? = some chosenFrame)
    (frameLedger : chosenFrame.extra.borrowTracker = some ledger)
    (entry : LocalAllocation Provenance BorrowTree K) (borrow : MachineHooks.BorrowState)
    (check : hooks.checkPtrAccess place.mplace.ptr length before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place length protectedShared tag (some location) resolved = .ok () logged)
    (source : location.parentProvenance = .concrete parentTag)
    (tracked : logged.machine.borrowTracker = some borrow)
    (live : logged.machine.memory.live[location.allocId]? = some entry)
    (mutable : entry.allocation.mutability = .Mut)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (positive : length.bytes ≠ 0)
    (ensure : let entered := withStrongProtector logged location tag chosenFrame ledger borrow
      hooks.ensureTreeExtra location.allocId entered = .ok () entered)
    (raceOff : logged.machine.dataRace = none)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (freshTag : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ tag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : location.baseOffset.bytes.toNat + length.bytes.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row borrow.global.protectedTags parent .Read)
      location.baseOffset.bytes (location.baseOffset.bytes + length.bytes) entry.allocation.extra.locations) :
    let active := registeredTracker borrow tag
    let entered := withStrongProtector logged location tag chosenFrame ledger borrow
    let read := entry.allocation.extra.performBorrowAccessRange location.parentProvenance location.baseOffset
      length .Read active.global.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild location.baseOffset location.parentProvenance tag
      (DedupRangeMap.new length sharedState) .Frozen true
    let staged := withTree entered location.allocId entry read.tree
    let updated := {entry with allocation := entry.allocation.setExtra read.tree}
    let after := withTree staged location.allocId updated child.tree
    TypedRetag.reborrow hooks budget place length protectedShared tag before =
      .ok (some (.concrete location.allocId tag)) after ∧
    child.tree.locations.size = entry.allocation.extra.locations.size ∧
      CoherentForest child.tree ∧ child.tree.roots = #[root] ∧
      ∃ index, child.tree.indexOfTag tag = some index ∧
        (∃ node, child.tree.nodeAt index = some node ∧
          node.tag = tag ∧ node.parent = some parent ∧ node.defaultInitialPermission = .Frozen) ∧
        ∀ point : UInt64, location.baseOffset.bytes.toNat ≤ point.toNat →
          point.toNat < (location.baseOffset.bytes + length.bytes).toNat →
          ∀ row, ValueAt child.tree.locations point row →
            LocationAccessRights child.tree row active.global.protectedTags index .Read := by
  let active := registeredTracker borrow tag
  let entered := withStrongProtector logged location tag chosenFrame ledger borrow
  let inside := DedupRangeMap.new length sharedState
  have uniform := uniform_shared_segments location.baseOffset length _ bounds
  have rights : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row
      active.global.protectedTags parent .Read)
      location.baseOffset.bytes (location.baseOffset.bytes + length.bytes) entry.allocation.extra.locations := by
    intro position valid positive start stop index node present
    obtain ⟨state, witness, localRight, alien⟩ := owners position valid positive start stop index node present
    have held : active.global.protectedTags.contains node.tag = borrow.global.protectedTags.contains node.tag :=
      MutableReferenceRights.contains_insert_other _ _ _ _ (freshTag index node present)
    exact ⟨state, witness, by rw [held]; exact localRight, by rw [held]; exact alien⟩
  obtain ⟨readDone, childDone, sizeEq, nextCoherent, nextRoots, index, tagFound, stored, rest⟩ :=
    concrete_shared_readable_reborrow entry.allocation.extra active.global.protectedTags parentTag tag
      parent root location.baseOffset length inside true coherent parentNode parentStored roots
      parentFound depth rank tagFresh room aligned reuse clean
      (fun segment member => (uniform segment member).1)
      (fun segment member => (uniform segment member).2) bounds rights
  have normalized : entry.allocation.extra.performBorrowAccessRange location.parentProvenance
      location.baseOffset length .Read active.global.protectedTags .VisitChildrenOfAccessed =
      entry.allocation.extra.performNormalAccessRange parentTag location.baseOffset length .Read
        active.global.protectedTags .VisitChildrenOfAccessed := by
    rw [source]
    rfl
  have completed : (entry.allocation.extra.performBorrowAccessRange location.parentProvenance
      location.baseOffset length .Read active.global.protectedTags .VisitChildrenOfAccessed).status = .Completed :=
    normalized.symm ▸ readDone
  have childComplete :
      let read := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
        location.baseOffset length .Read active.global.protectedTags .VisitChildrenOfAccessed
      (read.tree.newChild location.baseOffset location.parentProvenance tag inside .Frozen true).outcome = .ok () := by
    simpa only [source, BorrowTree.performNormalAccessRange] using childDone
  have race := retagRace_disabled location.allocId .Read location.baseOffset length
    (withTree entered location.allocId entry
      (entry.allocation.extra.performBorrowAccessRange location.parentProvenance location.baseOffset
        length .Read active.global.protectedTags .VisitChildrenOfAccessed).tree) raceOff
  have operation := uniform_live_reborrow hooks budget place length protectedShared tag location
    before pointed resolved logged _ chosenFrame ledger borrow sharedState entry .Read
    check resolve log rfl current frameLedger tracked live mutable imprecise freeze rfl rfl positive ensure
    completed race childComplete
  refine ⟨operation, ?_⟩
  simp only [source]
  exact ⟨sizeEq, nextCoherent, nextRoots, index, tagFound, stored, rest⟩

#print axioms typed_shared_fn_entry
end DuplicatePrefix.ArchiveForestProjection

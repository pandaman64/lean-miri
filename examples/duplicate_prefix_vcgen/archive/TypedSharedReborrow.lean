import duplicate_prefix.ConcreteSharedReborrow
import duplicate_prefix.ExclusiveTwoPhaseRetag

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.Tree
open SourceDomain GeneralRangeMapOrigins RetagLocationFrame RetagSharedChild
open RetagPolicy Miri.Verification.MutableTypedRetag

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

def unprotectedShared : NewPermission := ⟨.Frozen, .Cell, .Frozen, none⟩

/-- A concrete shared retag checks the actual parent Read, installs its
fresh read-only child, and writes both trees back by the actual allocation
key. The permission conclusions are derived from the prepared byte grants. -/
theorem typed_shared_reborrow [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (length : Size) (tag parentTag : BorTag)
    (parent root : UniIndex) (location : RetagPipeline.ResolvedLocation)
    (before pointed resolved logged : State)
    (entry : LocalAllocation Provenance BorrowTree K) (borrow : MachineHooks.BorrowState)
    (check : hooks.checkPtrAccess place.mplace.ptr length before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place length unprotectedShared tag (some location) resolved = .ok () logged)
    (source : location.parentProvenance = .concrete parentTag)
    (tracked : logged.machine.borrowTracker = some borrow)
    (live : logged.machine.memory.live[location.allocId]? = some entry)
    (mutable : entry.allocation.mutability = .Mut)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (positive : length.bytes ≠ 0)
    (ensure : hooks.ensureTreeExtra location.allocId logged = .ok () logged)
    (raceOff : logged.machine.dataRace = none)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : location.baseOffset.bytes.toNat + length.bytes.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row borrow.global.protectedTags parent)
      location.baseOffset.bytes (location.baseOffset.bytes + length.bytes) entry.allocation.extra.locations) :
    let read := entry.allocation.extra.performBorrowAccessRange location.parentProvenance location.baseOffset
      length .Read borrow.global.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild location.baseOffset location.parentProvenance tag
      (DedupRangeMap.new length sharedState) .Frozen false
    let staged := withTree logged location.allocId entry read.tree
    let updated := {entry with allocation := entry.allocation.setExtra read.tree}
    let after := withTree staged location.allocId updated child.tree
    TypedRetag.reborrow hooks budget place length unprotectedShared tag before =
      .ok (some (.concrete location.allocId tag)) after ∧
    child.tree.locations.size = entry.allocation.extra.locations.size ∧
      ∃ index, child.tree.indexOfTag tag = some index ∧
        (∃ node, child.tree.nodeAt index = some node ∧
          node.tag = tag ∧ node.parent = some parent ∧ node.defaultInitialPermission = .Frozen) ∧
        FramedWith (fun state => state.permission = .Frozen ∧ state.accessed = true)
          read.tree.locations index child.tree := by
  let inside := DedupRangeMap.new length sharedState
  have uniform := uniform_shared_segments location.baseOffset length _ bounds
  obtain ⟨readDone, childDone, sizeEq, index, tagFound, stored, frame⟩ :=
    concrete_shared_reborrow entry.allocation.extra borrow.global.protectedTags parentTag tag
      parent root location.baseOffset length inside false coherent parentNode parentStored roots
      parentFound depth rank tagFresh room aligned reuse clean
      (fun segment member => (uniform segment member).1)
      (fun segment member => (uniform segment member).2) bounds owners
  have operation := DuplicatePrefix.ExclusiveTwoPhaseRetag.uniform_live_reborrow_unprotected
    hooks budget place length unprotectedShared tag location before pointed resolved logged
    sharedState entry borrow .Read check resolve log rfl tracked live mutable imprecise freeze rfl rfl
    positive ensure raceOff
  have normalized : entry.allocation.extra.performBorrowAccessRange location.parentProvenance
      location.baseOffset length .Read borrow.global.protectedTags .VisitChildrenOfAccessed =
      entry.allocation.extra.performNormalAccessRange parentTag location.baseOffset length .Read
        borrow.global.protectedTags .VisitChildrenOfAccessed := by
    rw [source]
    rfl
  specialize operation (by rw [normalized]; exact readDone)
    (by simp only [normalized, source, unprotectedShared]; exact childDone)
  refine ⟨operation, ?_⟩
  simp only [normalized, source]
  exact ⟨sizeEq, index, tagFound, stored, frame⟩

#print axioms typed_shared_reborrow
end DuplicatePrefix.ArchiveForestProjection

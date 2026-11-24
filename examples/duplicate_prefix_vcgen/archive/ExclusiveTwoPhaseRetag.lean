import duplicate_prefix.ConcreteFrozenReborrow
import Miri.Verification.MutableTypedRetag

namespace DuplicatePrefix.ExclusiveTwoPhaseRetag
open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.RetagPolicy Miri.Verification Miri.Verification.MutableTypedRetag
open DuplicatePrefix.SourceDomain DuplicatePrefix.ArchiveForestProjection DuplicatePrefix.MutableSliceRights
open DuplicatePrefix.RetagFrozenChild GeneralRangeMapOrigins

variable {K U : Type}
local notation "State" => MachineHooks.State K U

def policy : NewPermission := ⟨.ReservedFrz false, .ReservedIM, .ReservedFrz false, none⟩
def initial : Tree.LocationState := ⟨.ReservedFrz false, true, .Read⟩

private theorem segmentProperties (offset size capacity : Size)
    (bounds : offset.bytes.toNat + size.bytes.toNat ≤ capacity.bytes.toNat) :
    ∀ segment ∈ (DedupRangeMap.new size initial).iterAll.toList,
      (segment.range.start ≤ segment.range.stop ∧
        offset.bytes.toNat + segment.range.stop.toNat ≤ capacity.bytes.toNat) ∧
      FrozenChildState false segment.data := by
  intro segment member
  by_cases empty : size.bytes = 0
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, empty] at member
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, beq_iff_eq, empty] at member
    subst segment
    exact ⟨⟨by simp, bounds⟩, .inl rfl⟩

/-- Execute the unprotected, uniform frozen reborrow after proving the
parent access and child edit. Both mutable two-phase and ordinary shared
references use this machine path. -/
theorem uniform_live_reborrow_unprotected [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag)
    (location : RetagPipeline.ResolvedLocation) (before pointed resolved logged : State)
    (initial : Tree.LocationState) (entry : LocalAllocation Provenance BorrowTree K)
    (borrow : MachineHooks.BorrowState) (kind : AccessKind)
    (check : hooks.checkPtrAccess place.mplace.ptr size before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place size policy tag (some location) resolved = .ok () logged)
    (unprotected : policy.protector = none)
    (tracked : logged.machine.borrowTracker = some borrow)
    (live : logged.machine.memory.live[location.allocId]? = some entry)
    (mutable : entry.allocation.mutability = .Mut)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (initialized : initialLocationState policy true = .ok initial)
    (associated : initial.permission.associatedAccess = some kind)
    (nonempty : size.bytes ≠ 0)
    (ensure : hooks.ensureTreeExtra location.allocId logged = .ok () logged)
    (raceOff : logged.machine.dataRace = none)
    (parentAccess : (entry.allocation.extra.performBorrowAccessRange location.parentProvenance
      location.baseOffset size kind borrow.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childComplete :
      let read := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
        location.baseOffset size kind borrow.global.protectedTags .VisitChildrenOfAccessed
      (read.tree.newChild location.baseOffset location.parentProvenance tag (DedupRangeMap.new size initial)
        policy.outsidePermission policy.protector.isSome).outcome = .ok ()) :
    let read := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
      location.baseOffset size kind borrow.global.protectedTags .VisitChildrenOfAccessed
    let raced := withTree logged location.allocId entry read.tree
    let child := read.tree.newChild location.baseOffset location.parentProvenance tag (DedupRangeMap.new size initial)
      policy.outsidePermission policy.protector.isSome
    let updated := {entry with allocation := entry.allocation.setExtra read.tree}
    TypedRetag.reborrow hooks budget place size policy tag before =
      .ok (some (.concrete location.allocId tag)) (withTree raced location.allocId updated child.tree) := by
  intro read raced child updated
  let inside := DedupRangeMap.new size initial
  let after := withTree raced location.allocId updated child.tree
  have register : TypedRetagWP.registerProtector location policy tag logged = .ok () logged := by
    simp [TypedRetagWP.registerProtector, unprotected, pure, Pure.pure, EStateM.pure]
  have permissions : TypedRetag.insidePermissions hooks budget place size policy logged = .ok inside logged := by
    rw [MutableRetagRights.frozen_insidePermissions hooks budget place size policy initial imprecise freeze initialized]
    rfl
  have race : retagRace location.allocId kind location.baseOffset size raced = .ok () raced :=
    retagRace_disabled location.allocId kind location.baseOffset size raced raceOff
  have racedLive : raced.machine.memory.live[location.allocId]? = some updated :=
    withTree_live logged location.allocId entry read.tree
  have childReady : TypedRetagWP.insertChildPre location policy tag inside
      (fun state => state = after) (fun _ _ => False) raced :=
    MutableRetagRights.insertChild_of_complete location policy tag inside raced updated racedLive childComplete
  apply run_eq_of_wp
  apply live_reborrow hooks budget place size policy tag location before pointed resolved logged logged inside
    entry _ check resolve log register live permissions ensure
  let segment : RangeMapSegment Tree.LocationState := ⟨⟨0,size.bytes⟩,initial⟩
  have partition : inside.iterAll.toList = [segment] := by
    simp [inside, DedupRangeMap.new, DedupRangeMap.iterAll, nonempty, segment]
  rw [partition]
  simp only [TypedRetagWP.segmentsPre, eq_self, true_and]
  have offset : Size.add location.baseOffset (Size.ofBytes segment.range.start) = .ok location.baseOffset := by
    cases location.baseOffset
    simp [Size.add, Size.ofBytes, segment]
  have length : Size.ofBytes (segment.range.stop - segment.range.start) = size := by
    cases size
    simp [Size.ofBytes, segment]
  exact segment_of_parent_access location segment location.baseOffset kind logged raced entry borrow _
    live tracked mutable associated offset (by simpa only [length] using parentAccess)
    (by simpa only [length] using race) childReady

/-- The pure tree transition of the emitted unprotected frozen reservation.
Only the logical tree is retained here. The execution theorem below also
proves the parent access and the child installation both complete. -/
def reservationTree (tree : BorrowTree) (parentTag tag : BorTag) (offset size : Size)
    (tags : ProtectedTags) : BorrowTree :=
  let read := tree.performBorrowAccessRange (.concrete parentTag) offset size .Read tags .VisitChildrenOfAccessed
  (read.tree.newChild offset (.concrete parentTag) tag (DedupRangeMap.new size initial) (.ReservedFrz false) false).tree

/-- The concrete two-phase borrow executes the actual parent read and
installs the new reservation. The existing caller protector ledger and
all existing source grants used by the reborrow are retained. -/
theorem reborrow_exclusive [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (tag parentTag : BorTag)
    (location : RetagPipeline.ResolvedLocation) (before pointed resolved logged : State)
    (borrow : MachineHooks.BorrowState)
    (entry : LocalAllocation Provenance BorrowTree K) (parent root : UniIndex)
    (parentNode : TreeNode)
    (check : hooks.checkPtrAccess place.mplace.ptr size before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place size policy tag (some location) resolved = .ok () logged)
    (parentProvenance : location.parentProvenance = .concrete parentTag)
    (tracked : logged.machine.borrowTracker = some borrow)
    (live : logged.machine.memory.live[location.allocId]? = some entry)
    (mutable : entry.allocation.mutability = .Mut)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (nonempty : size.bytes ≠ 0)
    (ensure : hooks.ensureTreeExtra location.allocId logged = .ok () logged)
    (raceOff : logged.machine.dataRace = none)
    (coherent : CoherentForest entry.allocation.extra)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root])
    (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes)
    (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (fresh : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ tag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none →
      entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none →
      entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : location.baseOffset.bytes.toNat + size.bytes.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationRights entry.allocation.extra location
      borrow.global.protectedTags parent) location.baseOffset.bytes (location.baseOffset.bytes + size.bytes)
      entry.allocation.extra.locations) :
    ∃ (after : State) (tree : BorrowTree) (child : UniIndex),
      TypedRetag.reborrow hooks budget place size policy tag before =
        .ok (some (.concrete location.allocId tag)) after ∧
      after.machine.memory.live[location.allocId]? =
        some {entry with allocation := entry.allocation.setExtra tree} ∧
      after.machine.borrowTracker = some borrow ∧ after.stack = logged.stack ∧
      after.machine.user = logged.machine.user ∧ after.machine.dataRace = logged.machine.dataRace ∧
      after.machine.threads = logged.machine.threads ∧
      tree = reservationTree entry.allocation.extra parentTag tag location.baseOffset size borrow.global.protectedTags ∧
      tree.locations.size = entry.allocation.extra.locations.size ∧ CoherentForest tree ∧ tree.roots = #[root] ∧
      tree.indexOfTag tag = some child ∧
      (∃ node, tree.nodeAt child = some node ∧ node.tag = tag) ∧
      ∀ point : UInt64, location.baseOffset.bytes.toNat ≤ point.toNat →
        point.toNat < (location.baseOffset.bytes + size.bytes).toNat →
        ∀ row, ValueAt tree.locations point row →
          OwnsByte tree row borrow.global.protectedTags child := by
  let tree := entry.allocation.extra
  let inside := DedupRangeMap.new size initial
  let tags := borrow.global.protectedTags
  let read := tree.performBorrowAccessRange location.parentProvenance location.baseOffset size .Read
    tags .VisitChildrenOfAccessed
  let raced := withTree logged location.allocId entry read.tree
  let child := read.tree.newChild location.baseOffset location.parentProvenance tag inside (.ReservedFrz false) false
  let updated := {entry with allocation := entry.allocation.setExtra read.tree}
  let after := withTree raced location.allocId updated child.tree
  have laws := segmentProperties location.baseOffset size tree.locations.size bounds
  have effects := coherent_frozen_reborrow_with_mode tree tags parentTag tag parent root
    location.baseOffset size inside false coherent parentNode parentStored roots parentFound depth rank
    tagFresh fresh room aligned reuse clean (fun segment mem => (laws segment mem).1)
    (fun segment mem => (laws segment mem).2) bounds owners
  have effects' : read.status = .Completed ∧ child.outcome = .ok () ∧
      child.tree.locations.size = tree.locations.size ∧ CoherentForest child.tree ∧ child.tree.roots = #[root] ∧
      ∃ index, child.tree.indexOfTag tag = some index ∧
        (∃ node, child.tree.nodeAt index = some node ∧ node.tag = tag) ∧
        ∀ point : UInt64, location.baseOffset.bytes.toNat ≤ point.toNat →
          point.toNat < (location.baseOffset.bytes + size.bytes).toNat →
          ∀ row, ValueAt child.tree.locations point row → OwnsByte child.tree row tags index := by
    simpa only [read, child, parentProvenance, BorrowTree.performNormalAccessRange, childProtections, Bool.false_eq_true,
      ↓reduceIte] using effects
  obtain ⟨readOk, childOk, capacity, well, stillRoot, index, key, node, owned⟩ := effects'
  have actual := uniform_live_reborrow_unprotected hooks budget place size policy tag location
    before pointed resolved logged initial entry borrow .Read check resolve log rfl tracked live mutable
    imprecise freeze rfl rfl nonempty ensure raceOff readOk childOk
  have exactTree : child.tree = reservationTree tree parentTag tag location.baseOffset size borrow.global.protectedTags := by
    simp only [child, read, reservationTree, parentProvenance, tags, inside]
  exact ⟨after, child.tree, index, actual, withTree_live raced location.allocId updated child.tree,
    tracked, rfl, rfl, rfl, rfl, exactTree, capacity, well, stillRoot, key, node, owned⟩

end DuplicatePrefix.ExclusiveTwoPhaseRetag

#print axioms DuplicatePrefix.ExclusiveTwoPhaseRetag.reborrow_exclusive

#print axioms DuplicatePrefix.ExclusiveTwoPhaseRetag.uniform_live_reborrow_unprotected

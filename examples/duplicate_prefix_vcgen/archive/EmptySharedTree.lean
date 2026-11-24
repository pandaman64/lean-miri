import duplicate_prefix.RetagSharedChild
import duplicate_prefix.RetagFrozenChild
import duplicate_prefix.RetagGraphFrame
import Miri.Verification.MutableTypedRetag

namespace DuplicatePrefix.EmptySharedTree
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows
open Miri.Verification.MutableTypedRetag
open BorrowTree BorrowTree.MutationVerification BorrowTree.ZeroProtection
open Miri.Verification Miri.Verification.MutableRetagFootprint Miri.Interpreter.TypedRetag
open ArchiveForestProjection DuplicatePrefix.SourceDomain
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

private theorem noSegments (initial : Tree.LocationState) :
    (DedupRangeMap.new Size.ZERO initial).iterAll.toList = [] := rfl

/-- Empty shared retags allocate a tag and attach a child, without any
inside-byte permissions or associated parent access. -/
theorem attach (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentFound : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index → index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (coherent : CoherentForest tree)
    (graph : ParentDepth tree.nodes) (rank : graph.depth parent < tree.nodes.size)
    (vacantRange : ∀ index, tree.nodeAt index = none → ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none)
    (held : Bool) :
    let inside := DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState
    let result := tree.newChild offset (.concrete parentTag) tag inside .Frozen held
    ∃ mapping child, tree.tagMapping.insert tag = .Inserted mapping child ∧
      result.outcome = .ok () ∧ result.tree.indexOfTag tag = some child ∧
      result.tree.roots = tree.roots ∧ CoherentForest result.tree ∧
      (∃ data, result.tree.nodeAt child = some data ∧ data.isExposed = false) ∧
      RetagLocationFrame.FramedAt (fun _ _ => False) tree.locations child result.tree := by
  obtain ⟨mapping, child, selected, childBound, vacant⟩ := RetagFrozenChild.select_slot tree tag fresh room aligned reuse
  let inside := DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState
  have empty : inside.iterAll.toList = [] := noSegments _
  have well := coherent.ranges
  have complete := RetagSharedChild.newChild_shared_completes tree offset parentTag tag parent child mapping
    inside held selected parentFound parentNode present vacant childBound well graph rank
    (by simp [empty]) (by simp [empty])
  have key := newChild_selected_key tree offset (.concrete parentTag) tag inside .Frozen held
    mapping child selected
  have framed := RetagLocationFrame.newChild_framed_at (grant := fun _ _ => False)
    (fun _ _ _ _ _ impossible => impossible) tree offset parentTag tag parent child mapping inside .Frozen held
    selected parentFound parentNode present vacant well (vacantRange child vacant) (by simp [empty]) (by simp [empty]) complete
  have graphAfter := initial_child_coherent tree offset parentTag tag parent child mapping inside
    .Frozen held .Read rfl rfl rfl selected parentFound parentNode present vacant childBound coherent graph rank
    complete framed.2.1
  let after := (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree
  have metadata := newChild_nodeMetadata tree offset parentTag tag parent child mapping inside .Frozen held
    selected parentFound parentNode present vacant complete
  have installed : nodeMetadata after child = some (tag,some parent,.Frozen) := by
    simpa only [ite_true] using metadata child
  have found : ∃ data, after.nodeAt child = some data := by
    unfold nodeMetadata at installed
    cases lookup : after.nodeAt child with
    | none => rw [lookup] at installed; cases installed
    | some data => exact ⟨data,rfl⟩
  obtain ⟨data, dataAt⟩ := found
  have exposure := newChild_initial_unexposed tree offset parentTag tag parent child mapping inside .Frozen held .Read
    rfl rfl rfl selected parentFound parentNode present vacant complete data dataAt
  exact ⟨mapping, child, selected, complete, key, graphAfter.2, graphAfter.1, ⟨data,dataAt,exposure⟩, framed⟩

/-- Every stored range lacks materialized state for the zero-width child. -/
theorem childUnmaterialized (initial : DedupRangeMap LocationTree) (child : UniIndex)
    (after : BorrowTree) (framed : RetagLocationFrame.FramedAt (fun _ _ => False) initial child after)
    (position : Nat) (inside : position < after.locations.entries.size) :
    after.locations.entries[position].data.perms.get child = none := by
  have formed := framed.2.1
  have nonempty : after.locations.entries.size ≠ 0 := by omega
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at formed
  let segment := after.locations.entries[position]
  have authorized := framed.2.2 segment.range.start position inside (UInt64.le_refl _) (formed.2.1 position inside)
  cases found : segment.data.perms.get child with
  | none => rfl
  | some state => exact (authorized.2 state found).elim

/-- Actual live backed-empty reborrows commit the exact child tree through
keyed allocation replacement, after canonical pointer checks and registration. -/
theorem reborrow {K U : Type} [DecidableEq K]
    (hooks : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (location : RetagPipeline.ResolvedLocation)
    (before pointed resolved logged registered : MachineHooks.State K U)
    (entry : LocalAllocation Provenance BorrowTree K) (initial : Tree.LocationState)
    (check : hooks.checkPtrAccess place.mplace.ptr Size.ZERO before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place Size.ZERO policy tag (some location) resolved = .ok () logged)
    (register : TypedRetagWP.registerProtector location policy tag logged = .ok () registered)
    (live : registered.machine.memory.live[location.allocId]? = some entry)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (initialized : RetagPolicy.initialLocationState policy true = .ok initial)
    (ensure : hooks.ensureTreeExtra location.allocId registered = .ok () registered)
    (complete : (entry.allocation.extra.newChild location.baseOffset location.parentProvenance tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome).outcome = .ok ()) :
    TypedRetag.reborrow hooks budget place Size.ZERO policy tag before =
      .ok (some (.concrete location.allocId tag))
        (withTree registered location.allocId entry
          (entry.allocation.extra.newChild location.baseOffset location.parentProvenance tag
            (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome).tree) := by
  let inside := DedupRangeMap.new Size.ZERO initial
  let child := entry.allocation.extra.newChild location.baseOffset location.parentProvenance tag inside
    policy.outsidePermission policy.protector.isSome
  let after := withTree registered location.allocId entry child.tree
  have permissions : TypedRetag.insidePermissions hooks budget place Size.ZERO policy registered = .ok inside registered := by
    simp [TypedRetag.insidePermissions, imprecise, freeze, initialized, inside, bind, EStateM.bind,
      pure, EStateM.pure, checked]
  apply run_eq_of_wp
  apply live_reborrow hooks budget place Size.ZERO policy tag location before pointed resolved logged registered inside entry
    (fun value state => value = some (.concrete location.allocId tag) ∧ state = after)
    check resolve log register live permissions ensure
  rw [noSegments initial]
  simp only [TypedRetagWP.segmentsPre, TypedRetagWP.insertChildPre, TypedRetagWP.effectPre,
    getTree_apply, live, insertChildPre_iff,
    childResultPre, updateTree_apply, MemoryState.setLiveAllocation_of_find _ _ _ _ live, after, withTree]
  rw [show child.outcome = .ok () from complete]
  exact ⟨True.intro,rfl⟩

#print axioms attach
#print axioms childUnmaterialized
#print axioms reborrow
end DuplicatePrefix.EmptySharedTree

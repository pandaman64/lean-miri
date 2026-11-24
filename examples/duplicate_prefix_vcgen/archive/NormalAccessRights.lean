import duplicate_prefix.ExclusiveConcreteRange
import duplicate_prefix.GeneralBorrowFreshReuseProtection

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposure GeneralBorrowProjection GeneralBorrowPresence BorrowRangeAccess SourceDomain

set_option backward.isDefEq.respectTransparency false

private theorem same_index {first second : UniIndex} (equal : first.toNat = second.toNat) : first = second :=
  Option.some.inj ((index_self first).symm.trans ((congrArg UniIndex.ofNat? equal).trans (index_self second)))

private theorem held_at (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    (source_normal_projection tree location protections).protectedNodes.contains index.toNat =
      protections.contains node.tag := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, GeneralBorrowFreshReuseProtection.protected_iff]
  constructor
  · rintro ⟨found, lookup, held⟩
    cases Option.some.inj (lookup.symm.trans present)
    exact held
  · intro held
    exact ⟨node, present, held⟩

private theorem vacancy (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (index : UniIndex) (valid : index.toNat < tree.nodes.data.size)
    (empty : tree.nodeAt index = none) (noStale : location.perms.get index = none) :
    (source_normal_projection tree location protectors).stateAt index.toNat = some ⟨.Disabled, false, .None⟩ := by
  have atSlot : tree.nodes.data[index.toNat] = none := by
    simpa only [BorrowTree.nodeAt, UniValMap.get, Array.getElem?_eq_getElem valid, Option.join_some] using empty
  unfold_general_projection
  simp [NormalTreeState.stateAt, index_self, atSlot, noStale, valid]

/-- Structural access rights on a concrete tree. A read grant also admits a
Frozen local node, while both kinds share the same foreign protection rule. -/
def LocationAccessRights (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (source : UniIndex) (kind : AccessKind) : Prop :=
  ∀ index node, tree.nodeAt index = some node →
    ∃ state, tree.locationStateAt location index = some state ∧
      (Ancestor tree index source → GeneralBorrowPermissions.AccessOwned state kind .LocalAccess (protectors.contains node.tag)) ∧
      (¬ Ancestor tree index source → GeneralBorrowPermissions.AccessOwned state kind .ForeignAccess (protectors.contains node.tag))

theorem LocationRights.readRights {tree : BorrowTree} {location : LocationTree}
    {protectors : ProtectedTags} {source : UniIndex}
    (rights : LocationRights tree location protectors source) :
    LocationAccessRights tree location protectors source .Read := by
  intro index node found
  obtain ⟨state, lookup, localPermission, foreignPermission⟩ := rights index node found
  refine ⟨state, lookup, ?_, foreignPermission⟩
  intro related
  have localRight := localPermission related
  refine ⟨localRight.1, ?_⟩
  intro disabled
  simp [SourceDomain.localOwns, disabled] at localRight

/-- At the checked normal view, absent slots have no old materialized
permissions. Structural rights on the actual graph extend to defaulted slots. -/
theorem normal_access_owned (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (source : UniIndex) (kind : AccessKind) (depth : ParentDepth tree.nodes)
    (sourceNode : TreeNode) (present : tree.nodeAt source = some sourceNode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (clean : ∀ index, tree.nodeAt index = none → location.perms.get index = none)
    (rights : LocationAccessRights tree location protections source kind) :
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) source.toNat kind := by
  let normal := source_normal_projection tree location protections
  have lengthEq := projection_size tree location protections
  have sizes := projection_sizes tree location protections
  refine ⟨(projected_node tree location protections source sourceNode present).1,
    sizes.1.trans lengthEq.symm, sizes.2.trans lengthEq.symm, ?_⟩
  intro position valid
  have posBound : position < tree.nodes.data.size := by rwa [← lengthEq]
  obtain ⟨index, _, convert⟩ := index_nat position (by omega)
  subst position
  cases found : tree.nodeAt index with
  | none =>
    have away : index.toNat ∉ normal.topology.ancestorPath source.toNat := by
      intro member
      obtain ⟨actual, node, convert, lookup⟩ := ancestors_present normal.topology (GeneralBorrowGraph.Present tree)
        (GeneralBorrowGraph.parents_closed tree location protections depth)
        normal.topology.nodes.size source.toNat ⟨source, sourceNode, rfl, present⟩ index.toNat member
      have equal := same_index convert
      subst actual
      rw [found] at lookup
      contradiction
    refine ⟨⟨.Disabled, false, .None⟩, vacancy tree location protections index posBound found (clean index found), ?_⟩
    rw [GeneralBorrowAnchor.relation, ite_eq_right away]
    cases kind <;> exact ⟨rfl, Or.inr (Or.inr ⟨rfl, by decide⟩)⟩
  | some node =>
    obtain ⟨state, stored, own, allow⟩ := rights index node found
    refine ⟨state, ?_, ?_⟩
    · rwa [projection_location_state tree location protections index node found]
    · rw [held_at tree location protections index node found, GeneralBorrowAnchor.relation]
      have related := ancestor_iff tree location protections depth index source sourceNode present
      by_cases lineage : Ancestor tree index source
      · rw [ite_eq_left (related.mpr lineage)]
        exact own lineage
      · rw [ite_eq_right (fun member => lineage (related.mp member))]
        exact allow lineage

theorem normal_access_owned_to_location (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (source : UniIndex) (kind : AccessKind) (depth : ParentDepth tree.nodes)
    (sourceNode : TreeNode) (sourcePresent : tree.nodeAt source = some sourceNode)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) source.toNat kind) :
    LocationAccessRights tree location protections source kind := by
  intro index node present
  obtain ⟨state, stored, rule⟩ := owned.permissions index.toNat (projected_node tree location protections index node present).1
  refine ⟨state, ?_, ?_, ?_⟩
  · rwa [projection_location_state tree location protections index node present] at stored
  · intro lineage
    have found := (ancestor_iff tree location protections depth index source sourceNode sourcePresent).mpr lineage
    rw [held_at tree location protections index node present, GeneralBorrowAnchor.relation, ite_eq_left found] at rule
    exact rule
  · intro unrelated
    have away := fun member => unrelated ((ancestor_iff tree location protections depth index source sourceNode sourcePresent).mp member)
    rw [held_at tree location protections index node present, GeneralBorrowAnchor.relation, ite_eq_right away] at rule
    exact rule

#print axioms normal_access_owned
#print axioms normal_access_owned_to_location
end DuplicatePrefix.ArchiveForestProjection

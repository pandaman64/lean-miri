import duplicate_prefix.NormalAccessRights

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification
open GeneralBorrowExposure GeneralBorrowProjection GeneralBorrowPresence BorrowRangeAccess SourceDomain
open GeneralRangeMapOrigins GeneralBorrowEvents

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

private theorem projected_held (tree : BorrowTree) (location : LocationTree)
    (protectors : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) :
    (source_normal_projection tree location protectors).protectedNodes.contains index.toNat =
      protectors.contains node.tag := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, GeneralBorrowFreshReuseProtection.protected_iff]
  constructor
  · rintro ⟨found, lookup, held⟩
    cases Option.some.inj (lookup.symm.trans present)
    exact held
  · intro held
    exact ⟨node, present, held⟩

/-- A coherent current caller forest and per-location ownership imply completion
of the canonical normal visitor, including its actual writeback and SIFA cache. -/
theorem normal_access_from_rights (tree : BorrowTree) (location : LocationTree)
    (protectors : ProtectedTags) (source : UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode) (coherent : CoherentForest tree) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode)
    (rights : LocationAccessRights tree location protectors source kind) :
    (tree.performNormalAccessAt location source kind protectors mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location source kind protectors mode).outcome = .ok () := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index node present parent edge
    obtain ⟨parentNode, found⟩ := coherent.parentPresent index node parent present edge
    exact ⟨parentNode, found, decreases index node parent present edge⟩⟩
  have childData : ∀ index node, tree.nodeAt index = some node →
      node.children.toList.Nodup ∧
        (∀ child ∈ node.children.toList, ∃ childNode,
          tree.nodeAt child = some childNode ∧ childNode.parent = some index) ∧
        (∀ child childNode, tree.nodeAt child = some childNode →
          childNode.parent = some index → child ∈ node.children.toList) := by
    intro index node present
    simpa using coherent.childEdges index node present
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro index node present child member
    obtain ⟨childNode, found, _⟩ := (childData index node present).2.1 child member
    exact ⟨childNode, found⟩
  let projection := source_normal_projection tree location protectors
  let component : GeneralBorrowExposedScopedNormal.Component projection.topology source.toNat :=
    ⟨GeneralBorrowGraph.Present tree, ⟨source, sourceNode, rfl, sourcePresent⟩,
      GeneralBorrowGraph.parents_closed tree location protectors depth,
      GeneralBorrowGraph.children_closed tree location protectors childNodes⟩
  apply GeneralBorrowExposedScopedNormal.access tree location protectors source kind mode
    (forest tree location protectors coherent.indexFits depth childData) component
    _ depth childNodes sourceNode sourcePresent
  intro position member _
  change GeneralBorrowGraph.Present tree position at member
  obtain ⟨index, node, rfl, lookup⟩ := member
  obtain ⟨state, stateKnown, localOwn, foreignOwn⟩ := rights index node lookup
  refine ⟨state, ?_, ?_⟩
  · simpa only [projection, projection_location_state tree location protectors index node lookup] using stateKnown
  · change GeneralBorrowPermissions.AccessOwned state kind
      (GeneralBorrowAnchor.relation projection source.toNat index.toNat)
      (projection.protectedNodes.contains index.toNat)
    rw [projected_held tree location protectors index node lookup]
    unfold GeneralBorrowAnchor.relation
    have related := ancestor_iff tree location protectors depth index source sourceNode sourcePresent
    by_cases lineage : Ancestor tree index source
    · rw [ite_eq_left (related.mpr lineage)]
      exact localOwn lineage
    · rw [ite_eq_right (fun member => lineage (related.mp member))]
      exact foreignOwn lineage

private theorem access_root (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (source root : UniIndex) (kind : AccessKind)
    (coherent : CoherentForest tree) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode) (roots : tree.roots = #[root]) :
    UniIndex.ofNat? (tree.performNormalAccessAt location source kind protections .VisitChildrenOfAccessed).access.root =
      some root := by
  let projection := source_normal_projection tree location protections
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index node present parent edge
    obtain ⟨parentNode, found⟩ := coherent.parentPresent index node parent present edge
    exact ⟨parentNode, found, decreases index node parent present edge⟩⟩
  have childData : ∀ index node, tree.nodeAt index = some node →
      node.children.toList.Nodup ∧
        (∀ child ∈ node.children.toList, ∃ childNode,
          tree.nodeAt child = some childNode ∧ childNode.parent = some index) ∧
        (∀ child childNode, tree.nodeAt child = some childNode →
          childNode.parent = some index → child ∈ node.children.toList) := by
    intro index node present
    simpa using coherent.childEdges index node present
  have coverage : GeneralBorrowGraph.RootsCover tree := by
    intro index node present noParent
    simpa using (coherent.rootEdges index node present).mp noParent
  have projectedRoot := GeneralBorrowTerminal.ancestor_root_present projection.topology
    (forest tree location protections coherent.indexFits depth childData)
    (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree location protections depth)
    source.toNat root.toNat (projected_node tree location protections source sourceNode sourcePresent).1
    ⟨source, sourceNode, rfl, sourcePresent⟩ (fun index _ => GeneralBorrowGraph.unique_root tree location protections root roots coverage index)
  change UniIndex.ofNat? (projection.performAccess source.toNat kind .VisitChildrenOfAccessed).root = some root
  rw [performAccess_as_schedule]
  change UniIndex.ofNat? (sourceNormalEvents projection _ kind _).root = some root
  rw [GeneralBorrowStorage.events_root]
  rw [projectedRoot]
  exact index_self root

/-- The actual split-led iterator selects authorized slots in a bounded
interval of a coherent single-root allocation. -/
theorem bounded_slots_from_rights (tree : BorrowTree) (protections : ProtectedTags)
    (source root : UniIndex) (kind : AccessKind) (offset length : Size)
    (coherent : CoherentForest tree) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode) (roots : tree.roots = #[root])
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (ownership : OwnedOn (fun location => LocationAccessRights tree location protections source kind)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    TreeRangeAccess.SlotsAuthorized tree (tree.locations.iterMut offset length)
      (some source) kind protections .VisitChildrenOfAccessed := by
  let prepared := tree.locations.iterMut offset length
  have info := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset length coherent.ranges bounds
  have owned := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset length coherent.ranges bounds
    _ offset.bytes (offset.bytes + length.bytes) ownership (Nat.le_refl _) (Nat.le_refl _)
  apply TreeRangeAccess.SlotsAuthorized.ofSingleRoot tree prepared source root kind protections roots
  intro cursor within
  have segmentExists : cursor < prepared.segments.size := by rwa [← info.1.lengths]
  let position := prepared.positions[cursor]
  let segment := prepared.segments[cursor]
  have permission := owned.2.2 cursor segmentExists
  have completed := normal_access_from_rights tree segment.data protections source kind .VisitChildrenOfAccessed
    coherent sourceNode sourcePresent permission
  exact ⟨position, segment, Array.getElem?_eq_getElem within, Array.getElem?_eq_getElem segmentExists,
    (info.1.selected cursor within).1, completed.2, completed.1,
    access_root tree segment.data protections source root kind coherent sourceNode sourcePresent roots⟩

/-- The actual interpreter grants either access across every selected slot
of a bounded interval in a coherent single-root allocation. Preparation,
splitting and range write-back are all discharged by the runtime proofs. -/
theorem bounded_range_from_rights (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (source root : UniIndex) (kind : AccessKind) (offset length : Size)
    (coherent : CoherentForest tree) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode) (roots : tree.roots = #[root])
    (index : tree.indexOfTag tag = some source)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (ownership : OwnedOn (fun location => LocationAccessRights tree location protections source kind)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    (tree.performBorrowAccessRange (.concrete tag) offset length kind protections .VisitChildrenOfAccessed).status =
      .Completed := by
  let prepared := tree.locations.iterMut offset length
  have info := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset length coherent.ranges bounds
  exact TreeRangeAccess.rangeComplete tree (.concrete tag) offset length kind protections .VisitChildrenOfAccessed
    prepared (some source) ⟨source, rfl, index⟩ rfl info.1.outcome
    (bounded_slots_from_rights tree protections source root kind offset length coherent sourceNode sourcePresent roots bounds ownership)

#print axioms bounded_range_from_rights
end DuplicatePrefix.ArchiveForestProjection

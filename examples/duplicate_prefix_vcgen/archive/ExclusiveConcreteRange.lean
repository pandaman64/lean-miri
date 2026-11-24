import duplicate_prefix.ArchiveForestProjection
import Miri.Verification.TreeRangeAccess
import duplicate_prefix.GeneralBorrowTerminal
import duplicate_prefix.GeneralRangeMapOriginPrepare

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification
open GeneralBorrowProjection GeneralBorrowExposure BorrowRangeAccess SourceDomain
open GeneralBorrowEvents
open GeneralRangeMapOrigins PreparedArguments

set_option backward.isDefEq.respectTransparency false

def LocationRights (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (source : UniIndex) : Prop :=
  ∀ index node, tree.nodeAt index = some node →
    ∃ state, tree.locationStateAt location index = some state ∧
      (Ancestor tree index source → localOwns state (protectors.contains node.tag)) ∧
      (¬ Ancestor tree index source → foreignCompatible state (protectors.contains node.tag))

private theorem normal_root (tree : BorrowTree) (location : LocationTree)
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
theorem bounded_slots (tree : BorrowTree) (protections : ProtectedTags)
    (source root : UniIndex) (kind : AccessKind) (offset length : Size)
    (coherent : CoherentForest tree) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode) (roots : tree.roots = #[root])
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (ownership : OwnedOn (fun location => LocationRights tree location protections source)
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
  have completed := normal_access tree segment.data protections source kind .VisitChildrenOfAccessed
    coherent sourceNode sourcePresent permission
  exact ⟨position, segment, Array.getElem?_eq_getElem within, Array.getElem?_eq_getElem segmentExists,
    (info.1.selected cursor within).1, completed.2, completed.1,
    normal_root tree segment.data protections source root kind coherent sourceNode sourcePresent roots⟩

/-- The actual interpreter grants either access across every selected slot
of a bounded interval in a coherent single-root allocation. Preparation,
splitting and range write-back are all discharged by the runtime proofs. -/
theorem bounded_range (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (source root : UniIndex) (kind : AccessKind) (offset length : Size)
    (coherent : CoherentForest tree) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode) (roots : tree.roots = #[root])
    (index : tree.indexOfTag tag = some source)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (ownership : OwnedOn (fun location => LocationRights tree location protections source)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    (tree.performBorrowAccessRange (.concrete tag) offset length kind protections .VisitChildrenOfAccessed).status =
      .Completed := by
  let prepared := tree.locations.iterMut offset length
  have info := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset length coherent.ranges bounds
  exact TreeRangeAccess.rangeComplete tree (.concrete tag) offset length kind protections .VisitChildrenOfAccessed
    prepared (some source) ⟨source, rfl, index⟩ rfl info.1.outcome
    (bounded_slots tree protections source root kind offset length coherent sourceNode sourcePresent roots bounds ownership)

/-- Any bounded subinterval of a prepared concrete slice inherits bytewise
write ownership from its existing provenance tag. -/
theorem exclusive_subrange {K U : Type} {before : MachineHooks.State K U}
    {sliceLength : UInt64} (storage : InitializedRegion before sliceLength)
    {tag : BorTag} (exclusive : ExclusiveRegion before sliceLength storage tag)
    (lower upper : UInt64)
    (startsInside : storage.relativeStart.bytes.toNat ≤ lower.toNat)
    (endsInside : upper.toNat ≤ storage.relativeStart.bytes.toNat + sliceLength.toNat) :
    OwnedOn (fun location => LocationRights storage.entry.allocation.extra location
      exclusive.tracker.global.protectedTags exclusive.source) lower upper storage.entry.allocation.extra.locations := by
  intro position valid positive segmentStarts segmentEnds
  let segment := storage.entry.allocation.extra.locations.entries[position]
  have inTable : segment ∈ storage.entry.allocation.extra.locations.entries :=
    Array.getElem_mem valid
  have populated := (GeneralRangeMapGeometry.facts storage.entry.allocation.extra.locations
    exclusive.coherent.ranges (by omega)).2.1 position valid
  let point := max lower.toNat segment.range.start.toNat
  have pointUpper : point < upper.toNat := Nat.max_lt.mpr ⟨positive, segmentStarts⟩
  have pointEnd : point < segment.range.stop.toNat := Nat.max_lt.mpr ⟨segmentEnds, populated⟩
  have pointLower := Nat.le_max_left lower.toNat segment.range.start.toNat
  have pointStart := Nat.le_max_right lower.toNat segment.range.start.toNat
  let distance := point - storage.relativeStart.bytes.toNat
  have absolute : storage.relativeStart.bytes.toNat + distance = point := by
    dsimp [distance]
    omega
  have distanceIn : distance < sliceLength.toNat := by omega
  exact exclusive.exclusive distance distanceIn segment inTable
    (by rw [absolute]; exact pointStart) (by rw [absolute]; exact pointEnd)

/-- A prepared single-root concrete slice grants the actual current ranged
access. This reuses the caller record and needs no intermediate WP hypothesis. -/
theorem exclusive_access {K U : Type} {before : MachineHooks.State K U}
    {sliceLength : UInt64} (storage : InitializedRegion before sliceLength)
    {tag : BorTag} (exclusive : ExclusiveRegion before sliceLength storage tag)
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (kind : AccessKind) (offset length : Size)
    (startsInside : storage.relativeStart.bytes.toNat ≤ offset.bytes.toNat)
    (endsInside : offset.bytes.toNat + length.bytes.toNat ≤
      storage.relativeStart.bytes.toNat + sliceLength.toNat)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat) :
    (storage.entry.allocation.extra.performBorrowAccessRange (.concrete tag) offset length kind
      exclusive.tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
  obtain ⟨node, present, _⟩ := exclusive.sourcePresent
  apply bounded_range _ _ tag exclusive.source root kind offset length exclusive.coherent node
    present roots exclusive.tagKnown bounds
  apply exclusive_subrange storage exclusive _ _ startsInside
  have sumFits := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
  simpa only [UInt64.toNat_add, Nat.mod_eq_of_lt sumFits] using endsInside

#print axioms bounded_range
#print axioms exclusive_access
end DuplicatePrefix.ArchiveForestProjection

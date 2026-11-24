import duplicate_prefix.ActiveReleaseExclusive
import duplicate_prefix.NormalAccessRights
import duplicate_prefix.GeneralBorrowRangePreserves
import duplicate_prefix.ReadAccessRange
import duplicate_prefix.ExclusiveCopyRanges

namespace DuplicatePrefix.SharedRelease

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection RetagReleaseRights
open GeneralBorrowExposure GeneralBorrowProjection GeneralBorrowPresence BorrowRangeAccess GeneralRangeMapOrigins
open GeneralBorrowPermissions GeneralBorrowOwnership GeneralBorrowRangePreserves

set_option maxRecDepth 65536
set_option maxHeartbeats 1800000

private theorem path_rank (tree : BorrowTree) (depth : ParentDepth tree.nodes)
    {up down : UniIndex} (path : Ancestor tree up down) : depth.depth up ≤ depth.depth down := by
  induction path with
  | self => exact Nat.le_refl _
  | parent above node stored edge ih =>
    obtain ⟨_, _, lower⟩ := depth.parent _ node stored _ edge
    omega

theorem ancestry_antisymm (tree : BorrowTree) (depth : ParentDepth tree.nodes)
    (first second : UniIndex) (forward : Ancestor tree first second) (back : Ancestor tree second first) :
    first = second := by
  have reverse := path_rank tree depth back
  induction forward with
  | self => rfl
  | parent above node stored edge ih =>
    obtain ⟨_, _, lower⟩ := depth.parent _ node stored _ edge
    have below := path_rank tree depth above
    omega

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

private theorem same_local (state : LocationState) (held : Bool) :
    LocalOwned state held ↔ localOwns state held := by
  cases permission : state.permission <;> simp [LocalOwned, localOwns, permission]
  case ReservedFrz conflicted => cases conflicted <;> intro _ <;> rfl

/-- A shared child's final read retains its mutable ancestor's local
permissions. The intervening shared read chain needs only readable grants,
and its released protectors restore compatibility with future writes. -/
theorem parent_after_read (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (tag : BorTag) (child parent root : UniIndex)
    (node : TreeNode) (found : tree.nodeAt child = some node)
    (holder : TreeNode) (holderPresent : tree.nodeAt parent = some holder)
    (chain : Ancestor tree parent child) (separate : parent ≠ child)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index child → ¬ Ancestor tree index parent → (tags.remove tag).contains data.tag = false)
    (unique : ∀ index data, tree.nodeAt index = some data → data.tag = tag → index = child)
    (depth : ParentDepth tree.nodes) (topologyFits : tree.nodes.data.size ≤ 2 ^ 32)
    (children : GeneralBorrowGraph.ChildNodes tree)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location tags).topology)
    (reader : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location tags) child.toNat .Read)
    (parentRights : LocationRights tree location (tags.remove tag) parent)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let visited := tree.performTreeAccessAt location (some child) .Read tags mode range
    LocationRights tree visited.location (tags.remove tag) parent := by
  let normal := source_normal_projection tree location tags
  let writable (index : Nat) := decide (index ∈ normal.topology.ancestorPath parent.toNat)
  have combined : Pointwise normal writable (GeneralBorrowAnchor.relation normal child.toNat) := by
    intro index inside
    have topo : index < normal.topology.nodes.size := by rwa [← reader.locationsAligned]
    obtain ⟨state, stored, readable⟩ := reader.permissions index topo
    refine ⟨state, stored, ?_⟩
    by_cases onHolder : index ∈ normal.topology.ancestorPath parent.toNat
    · obtain ⟨lookedUp, data, number, present⟩ := ancestors_present normal.topology
        (GeneralBorrowGraph.Present tree) (GeneralBorrowGraph.parents_closed tree location tags depth)
        normal.topology.nodes.size parent.toNat ⟨parent, holder, rfl, holderPresent⟩ index onHolder
      have actualPath : Ancestor tree lookedUp parent :=
        (ancestor_iff tree location tags depth lookedUp parent holder holderPresent).mp (by rwa [number])
      have different : lookedUp ≠ child := by
        intro equal
        have back : Ancestor tree child parent := equal ▸ actualPath
        exact separate (ancestry_antisymm tree depth parent child chain back)
      have selectedPath : index ∈ normal.topology.ancestorPath child.toNat := by
        rw [← number]
        exact (ancestor_iff tree location tags depth lookedUp child node found).mpr (ancestor_trans actualPath chain)
      obtain ⟨before, lookup, localRight, _⟩ := parentRights lookedUp data present
      have projected : normal.stateAt lookedUp.toNat = some before :=
        (projection_location_state tree location tags lookedUp data present).trans lookup
      rw [number] at projected
      have exactState := Option.some.inj (projected.symm.trans stored)
      subst before
      have otherTag : data.tag ≠ tag := fun collision => different (unique lookedUp data present collision)
      have protector : normal.protectedNodes.contains index = (tags.remove tag).contains data.tag := by
        rw [← number, held_at tree location tags lookedUp data present, contains_remove_other _ _ _ otherTag]
      rw [protector]
      simpa [Required, writable, onHolder, GeneralBorrowAnchor.relation, selectedPath, Owned] using
        (same_local _ _).mpr (localRight actualPath)
    · simpa [Required, writable, onHolder] using readable
  have preserved := GeneralBorrowOwnership.normal_preserves normal forest child.toNat reader.anchorValid
    .Read mode writable reader.locationsAligned combined (fun _ _ _ _ => rfl)
  let updated := (tree.performTreeAccessAt location (some child) .Read tags mode range).location
  have asNormal : updated = (tree.performNormalAccessAt location child .Read tags mode).location :=
    single_root_location tree location tags child root .Read mode range forest reader
      depth children node found roots covered
  have projection : source_normal_projection tree updated tags =
      (normal.performAccess child.toNat .Read mode).tree := by
    rw [asNormal]
    exact normal_projection tree location tags child .Read mode topologyFits
  change LocationRights tree updated (tags.remove tag) parent
  intro index data present
  have valid := (projected_node tree updated tags index data present).1
  have aligned := (projection_sizes tree updated tags).1
  have sizeEq := projection_size tree updated tags
  have position : index.toNat < (source_normal_projection tree updated tags).locationStates.size := by
    rw [aligned]
    rwa [← sizeEq]
  have output : Pointwise (source_normal_projection tree updated tags) writable
      (GeneralBorrowAnchor.relation normal child.toNat) := projection.symm ▸ preserved.2
  obtain ⟨state, stored, right⟩ := output index.toNat position
  have actual : tree.locationStateAt updated index = some state :=
    (projection_location_state tree updated tags index data present).symm.trans stored
  have held := held_at tree updated tags index data present
  rw [held] at right
  refine ⟨state, actual, ?_, ?_⟩
  · intro onParent
    have notChild : index ≠ child := by
      intro same
      subst index
      exact separate (ancestry_antisymm tree depth parent child chain onParent)
    have onChild := ancestor_trans onParent chain
    have holderMember : index.toNat ∈ normal.topology.ancestorPath parent.toNat := (ancestor_iff tree location tags depth index parent holder holderPresent).mpr onParent
    have childMember : index.toNat ∈ normal.topology.ancestorPath child.toNat := (ancestor_iff tree location tags depth index child node found).mpr onChild
    have otherTag : data.tag ≠ tag := fun collision => notChild (unique index data present collision)
    rw [contains_remove_other _ _ _ otherTag]
    apply (same_local _ _).mp
    simpa [Required, writable, holderMember, GeneralBorrowAnchor.relation, childMember, Owned] using right
  · intro foreign
    have outsideParent : index.toNat ∉ normal.topology.ancestorPath parent.toNat := fun member =>
      foreign ((ancestor_iff tree location tags depth index parent holder holderPresent).mp member)
    by_cases onChild : Ancestor tree index child
    · have member : index.toNat ∈ normal.topology.ancestorPath child.toNat :=
        (ancestor_iff tree location tags depth index child node found).mpr onChild
      have readable : LocalReadable state := by
        simpa [Required, writable, outsideParent, GeneralBorrowAnchor.relation, member, AccessOwned] using right
      exact ⟨readable.1, Or.inl (unheld index data present onChild foreign)⟩
    · have notMember : index.toNat ∉ normal.topology.ancestorPath child.toNat := fun member => onChild ((ancestor_iff tree location tags depth index child node found).mp member)
      have notChild : index ≠ child := by intro same; subst index; exact onChild (Ancestor.self child)
      have otherTag : data.tag ≠ tag := fun collision => notChild (unique index data present collision)
      simpa [contains_remove_other _ _ _ otherTag, Required, writable, outsideParent, GeneralBorrowAnchor.relation,
        notMember, AccessOwned, Owned, ForeignOwned, foreignCompatible] using right

/-- The actual associated read of a shared reborrow retains the earlier
mutable holder's exclusive grant. Reader authority and the holder's
post-release authority are independent input rights. -/
theorem ranged_read_retains_holder
    (tree : BorrowTree) (tags : ProtectedTags) (accessTag releasedTag : BorTag)
    (child parent root : UniIndex) (node holder : TreeNode)
    (found : tree.nodeAt child = some node) (holderFound : tree.nodeAt parent = some holder)
    (tagFound : tree.indexOfTag accessTag = some child)
    (chain : Ancestor tree parent child) (separate : parent ≠ child)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index child → ¬ Ancestor tree index parent →
        (tags.remove releasedTag).contains data.tag = false)
    (unique : ∀ index data, tree.nodeAt index = some data → data.tag = releasedTag → index = child)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (offset length : Size)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (readerRights : OwnedOn (fun row => LocationAccessRights tree row tags child .Read)
      offset.bytes (offset.bytes + length.bytes) tree.locations)
    (holderRights : OwnedOn (fun row => LocationRights tree row (tags.remove releasedTag) parent)
      offset.bytes (offset.bytes + length.bytes) tree.locations)
    (vacant : OwnedOn (fun row => ∀ index, tree.nodeAt index = none → row.perms.get index = none)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    let run := tree.performNormalAccessRange accessTag offset length .Read tags .VisitChildrenOfAccessed
    run.status = .Completed ∧ run.tree = {tree with locations := run.tree.locations} ∧
      CoherentForest run.tree ∧ run.tree.locations.size = tree.locations.size ∧
      OwnedOn (fun row => LocationRights run.tree row (tags.remove releasedTag) parent)
        offset.bytes (offset.bytes + length.bytes) run.tree.locations := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index data present parent edge
    obtain ⟨up, held⟩ := coherent.parentPresent index data parent present edge
    exact ⟨up, held, decreases index data parent present edge⟩⟩
  have childData := forest_children tree coherent
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro index data present child member
    obtain ⟨off, childPresent, _⟩ := (childData index data present).2.1 child member
    exact ⟨off, childPresent⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data present rootEdge
    simpa using (coherent.rootEdges index data present).mp rootEdge
  let retains (row : LocationTree) : Prop :=
    GeneralBorrowRange.LocationOwned tree tags child .Read row ∧
      LocationRights tree row (tags.remove releasedTag) parent
  have ready : OwnedOn retains offset.bytes (offset.bytes + length.bytes) tree.locations := by
    intro position inside positive lower upper
    let row := tree.locations.entries[position].data
    have graph := forest tree row tags coherent.indexFits depth childData
    have reader := normal_access_owned tree row tags child .Read depth node found coherent.indexFits
      (vacant position inside positive lower upper) (readerRights position inside positive lower upper)
    exact ⟨⟨⟨graph⟩, reader⟩, holderRights position inside positive lower upper⟩
  have auth := bounded_slots_from_rights tree tags child root .Read offset length
    coherent node found roots bounds readerRights
  have preserves : ∀ segment : RangeMapSegment LocationTree,
      segment.range.stop.toNat ≤ (offset.bytes + length.bytes).toNat →
      offset.bytes.toNat < (offset.bytes + length.bytes).toNat →
      segment.range.start.toNat < (offset.bytes + length.bytes).toNat →
      offset.bytes.toNat < segment.range.stop.toNat → retains segment.data →
      retains (tree.performTreeAccessAt segment.data (some child) .Read tags
        .VisitChildrenOfAccessed segment.range).location := by
    intro segment _ _ _ _ initial
    obtain ⟨⟨⟨graph⟩, reader⟩, writer⟩ := initial
    have kept := parent_after_read tree segment.data tags releasedTag child parent root node found holder holderFound
      chain separate unheld unique depth coherent.indexFits childNodes roots covered graph reader writer
      .VisitChildrenOfAccessed segment.range
    have readerKept := location_owned tree segment.data tags child root .Read .Read .VisitChildrenOfAccessed
      segment.range (fun _ => rfl) coherent.indexFits ⟨⟨graph⟩, reader⟩ depth childNodes node found roots covered
    exact ⟨readerKept, kept⟩
  have run := preserve_range_property tree accessTag child tags .Read .VisitChildrenOfAccessed
    offset length offset.bytes (offset.bytes + length.bytes) retains tagFound coherent.ranges
    bounds ready preserves auth
  let after := tree.performNormalAccessRange accessTag offset length .Read tags .VisitChildrenOfAccessed
  have shape : after.tree = {tree with locations := after.tree.locations} := run.2.2.2.2
  refine ⟨run.1, shape, ?_, run.2.2.2.1, ?_⟩
  · rw [shape]
    exact {coherent with ranges := run.2.2.1}
  · change OwnedOn (fun row => LocationRights after.tree row (tags.remove releasedTag) parent)
      offset.bytes (offset.bytes + length.bytes) after.tree.locations
    intro position inside positive lo hi
    let row := after.tree.locations.entries[position].data
    change LocationRights after.tree row (tags.remove releasedTag) parent
    have grant := (run.2.1 position inside positive lo hi).2
    rw [shape]
    exact rights_table tree after.tree.locations row (tags.remove releasedTag) parent grant

#print axioms parent_after_read
end DuplicatePrefix.SharedRelease

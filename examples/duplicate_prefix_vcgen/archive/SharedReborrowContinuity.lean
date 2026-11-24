import duplicate_prefix.SharedHolderAttach
import duplicate_prefix.RetagReleaseFootprint
import duplicate_prefix.SharedReleaseRange
import duplicate_prefix.SharedReadOwnership
import duplicate_prefix.InheritedSharedRights
import duplicate_prefix.RetagGraphFrame
import MutableSliceRetag
import duplicate_prefix.RetagFrozenChild
import duplicate_prefix.RetagSharedChild
import duplicate_prefix.RetagKeyFrame
import Miri.Verification.MutableRetagFootprint

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain GeneralRangeMapOrigins MutableSliceRights
open RetagFrozenChild RetagSharedChild RetagLocationFrame
open Miri.Verification.MutableRetagFootprint

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

private theorem all_entries_of_owned {A : Type} (table : DedupRangeMap A)
    (well : table.WellFormed) (predicate : A → Prop)
    (owned : OwnedOn predicate 0 table.size.bytes table) :
    ∀ position (valid : position < table.entries.size), predicate table.entries[position].data := by
  intro position valid
  have notEmpty : 0 < table.entries.size := by omega
  let last := table.entries.size - 1
  have lastValid : last < table.entries.size := by dsimp [last]; omega
  have final := congrArg UInt64.toNat (GeneralRangeMapGeometry.size_last table notEmpty)
  change table.size.bytes.toNat = (table.entries[last]'lastValid).range.stop.toNat at final
  have positive := (GeneralRangeMapGeometry.facts table well (by omega)).2.1
  refine owned position valid ?_ ?_ ?_
  · change 0 < table.size.bytes.toNat
    have lastNonempty := positive last lastValid
    omega
  · by_cases isLast : position = last
    · subst position
      have lastNonempty := positive last lastValid
      omega
    · have before : position < last := by dsimp [last] at *; omega
      have ordered := GeneralRangeMapGeometry.stop_le_start table well position last before lastValid
      have rowNonempty := positive position valid
      have lastNonempty := positive last lastValid
      omega
  · change 0 < table.entries[position].range.stop.toNat
    have rowNonempty := positive position valid
    omega

private theorem read_owned_byte {tree : BorrowTree} {protectors : ProtectedTags} {source : UniIndex}
    {lower upper point : UInt64} {location : LocationTree}
    (ownership : OwnedOn (fun row => LocationAccessRights tree row protectors source .Read) lower upper tree.locations)
    (start : lower.toNat ≤ point.toNat) (stop : point.toNat < upper.toNat)
    (contains : ValueAt tree.locations point location) :
    LocationAccessRights tree location protectors source .Read := by
  obtain ⟨position, valid, before, after, exact⟩ := contains
  have rights := ownership position valid (by omega) (by omega) (by omega)
  rw [exact] at rights
  exact rights

/-- Frame facts from a successful shared child creation. The holder grant is
transported through actual installation using the rights at its post-read
rows, under the chosen current or prospective protector map. -/
structure SharedChildFrame (original read after : BorrowTree) (parent child : UniIndex)
    (tag : BorTag) (offset length : Size) (inside : DedupRangeMap LocationState) : Prop where
  readMetadata : read = {original with locations := read.locations}
  attached : MutableSliceRights.Attachment read after parent child
  olderNodes : ∀ index node, index ≠ child → after.nodeAt index = some node →
    ∃ prior, original.nodeAt index = some prior ∧ prior.tag = node.tag ∧
      node.defaultInitialPermission = prior.defaultInitialPermission
  unexposed : ∀ node, after.nodeAt child = some node → node.isExposed = false
  frozen : GeneralRangeMapState.Every
    (fun row => ∀ state, row.perms.get child = some state → state.permission = .Frozen) after.locations
  extent : (∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat) →
    RetagReleaseFootprint.MaterializedWithin after child offset.bytes (offset.bytes + length.bytes) ∧
      RetagReleaseFootprint.VacantRows after
  unique : (∀ index node, original.nodeAt index = some node → node.tag ≠ tag) →
    ∀ index node, after.nodeAt index = some node → node.tag = tag → index = child
  holder : ∀ (source : UniIndex) (oldTags newTags : ProtectedTags),
    (∃ node, read.nodeAt source = some node) → newTags.contains tag = false →
    (∀ index node, read.nodeAt index = some node → newTags.contains node.tag = oldTags.contains node.tag) →
    OwnedOn (fun row => LocationRights read row oldTags source) offset.bytes (offset.bytes + length.bytes) read.locations →
      OwnedOn (fun row => LocationRights after row newTags source) offset.bytes (offset.bytes + length.bytes) after.locations

  holderMaterialization : ∀ watch, watch ≠ child → ∀ lower upper,
    RetagReleaseFootprint.MaterializedWithin read watch lower upper →
      RetagReleaseFootprint.MaterializedWithin after watch lower upper

  olderExposure : ∀ query, query ≠ child →
    (after.nodeAt query).map TreeNode.isExposed = (original.nodeAt query).map TreeNode.isExposed
  olderTags : ∀ query, query ≠ tag → after.indexOfTag query = original.indexOfTag query

private theorem under_read (original read : BorrowTree) (source index : UniIndex)
    (same : read = {original with locations := read.locations}) :
    Ancestor read index source ↔ Ancestor original index source := by
  rw [same]
  constructor
  · intro path
    induction path with
    | self => exact .self _
    | parent _ data found edge ih => exact .parent ih data found edge
  · intro path
    induction path with
    | self => exact .self _
    | parent _ data found edge ih => exact .parent ih data found edge

/-- Shared construction extends the old ancestor chain and leaves prior
unprotected intermediates unprotected under the eventual release map. -/
theorem SharedChildFrame.releaseLineage {original read after : BorrowTree}
    {parent child holder : UniIndex} {tag : BorTag} {offset length : Size} {inside : DedupRangeMap LocationState}
    (frame : SharedChildFrame original read after parent child tag offset length inside)
    (holderPresent : ∃ node, original.nodeAt holder = some node)
    (chain : Ancestor original holder parent)
    (newTag : ∀ node, after.nodeAt child = some node → node.tag = tag)
    (tags : ProtectedTags)
    (unheld : ∀ index node, original.nodeAt index = some node →
      Ancestor original index parent → ¬ Ancestor original index holder →
        (tags.remove tag).contains node.tag = false) :
    Ancestor after holder child ∧ holder ≠ child ∧
      ∀ index node, after.nodeAt index = some node →
        Ancestor after index child → ¬ Ancestor after index holder →
          (tags.remove tag).contains node.tag = false := by
  have holderOld : ∃ node, read.nodeAt holder = some node := by
    rw [frame.readMetadata]
    exact holderPresent
  have distinct : holder ≠ child := by
    intro same
    obtain ⟨node, found⟩ := holderOld
    rw [same, frame.attached.fresh] at found
    contradiction
  have linked : Ancestor read holder parent := (under_read original read parent holder frame.readMetadata).mpr chain
  refine ⟨frame.attached.ancestry.mpr (.inr linked), distinct, ?_⟩
  intro index node found lineage foreign
  rcases frame.attached.ancestry.mp lineage with fresh | previous
  · subst index
    simp [newTag node found, ProtectedTags.contains]
  · by_cases same : index = child
    · subst index
      simp [newTag node found, ProtectedTags.contains]
    obtain ⟨data, present, sameTag, _⟩ := frame.olderNodes index node same found
    have oldParent := (under_read original read parent index frame.readMetadata).mp previous
    have oldForeign : ¬ Ancestor original index holder := by
      intro old
      have readPath := (under_read original read holder index frame.readMetadata).mpr old
      have retained := (SharedRelease.holder_ancestry frame.attached distinct).2 readPath
      exact foreign retained
    rw [← sameTag]
    exact unheld index data present oldParent oldForeign

private theorem ownership_from_bytes (table : DedupRangeMap LocationTree)
    (lower upper : UInt64) (well : table.WellFormed) (property : LocationTree → Prop)
    (owned : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      ∀ row, ValueAt table point row → property row) :
    OwnedOn property lower upper table := by
  intro position inside positive start stop
  let entry := table.entries[position]
  have nonempty : table.entries.size ≠ 0 := by omega
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at well
  have nonsingle : entry.range.start.toNat < entry.range.stop.toNat :=
    UInt64.lt_iff_toNat_lt.mp (well.2.1 position inside)
  let point := if lower.toNat ≤ entry.range.start.toNat then entry.range.start else lower
  change entry.range.start.toNat < upper.toNat at start
  change lower.toNat < entry.range.stop.toNat at stop
  have left : lower.toNat ≤ point.toNat := by unfold point; split <;> omega
  have right : point.toNat < upper.toNat := by unfold point; split <;> omega
  have inRow : ValueAt table point entry.data := by
    refine ⟨position, inside, ?_, ?_, rfl⟩
    · change entry.range.start.toNat ≤ point.toNat
      unfold point
      split <;> omega
    · change point.toNat < entry.range.stop.toNat
      unfold point
      split <;> omega
  exact owned point left right entry.data inRow

/-- Use the exact installed shared child and its footprint to release protection
and restore the earlier holder's write grants over the same initialized region. -/
theorem SharedChildFrame.releaseHolderWithFrame {original read after : BorrowTree}
    {parent child holder root : UniIndex} {tag : BorTag} {offset length : Size}
    {inside : DedupRangeMap LocationState}
    (frame : SharedChildFrame original read after parent child tag offset length inside)
    (tags : ProtectedTags) (coherent : CoherentForest after) (roots : after.roots = #[root])
    (selected : after.indexOfTag tag = some child)
    (node : TreeNode) (stored : after.nodeAt child = some node) (tagged : node.tag = tag)
    (holderPresent : ∃ data, original.nodeAt holder = some data)
    (chain : Ancestor original holder parent)
    (unheld : ∀ index data, original.nodeAt index = some data →
      Ancestor original index parent → ¬ Ancestor original index holder →
        (tags.remove tag).contains data.tag = false)
    (fresh : ∀ index data, original.nodeAt index = some data → data.tag ≠ tag)
    (extent : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat)
    (readRights : ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
      point.toNat < (offset.bytes + length.bytes).toNat →
      ∀ row, ValueAt after.locations point row → LocationAccessRights after row tags child .Read)
    (holderRights : OwnedOn (fun row => LocationRights read row (tags.remove tag) holder) offset.bytes
      (offset.bytes + length.bytes) read.locations) :
    ∃ finished, finished = {after with locations := finished.locations} ∧ CoherentForest finished ∧
      finished.locations.size = after.locations.size ∧
      OwnedOn (fun row => LocationRights finished row (tags.remove tag) holder)
        offset.bytes (offset.bytes + length.bytes) finished.locations ∧
      RetagReleaseFootprint.VacantRows finished ∧
      (∀ watch, RetagReleaseFootprint.MaterializedWithin after watch offset.bytes (offset.bytes + length.bytes) →
        RetagReleaseFootprint.MaterializedWithin finished watch offset.bytes (offset.bytes + length.bytes)) ∧
      ∀ post failure, Miri.Verification.ProtectorReleaseWP.releasePre tag tags post failure after ↔ post finished := by
  have oldHolder : ∃ data, read.nodeAt holder = some data := by
    rw [frame.readMetadata]
    exact holderPresent
  obtain ⟨parentNode, parentMem⟩ := oldHolder
  obtain ⟨holderNode, holderKnown, _⟩ := frame.attached.oldEdges holder parentNode parentMem
  have installedTag : ∀ data, after.nodeAt child = some data → data.tag = tag := by
    intro data found
    have same := Option.some.inj (found.symm.trans stored)
    simpa only [same] using tagged
  obtain ⟨path, distinct, intermediate⟩ := frame.releaseLineage holderPresent chain installedTag tags unheld
  obtain ⟨rangeFrame, vacancy⟩ := frame.extent extent
  have writable := frame.holder holder (tags.remove tag) (tags.remove tag) ⟨parentNode, parentMem⟩
    (by simp [ProtectedTags.contains]) (fun _ _ _ => rfl) holderRights
  have readable := ownership_from_bytes after.locations offset.bytes (offset.bytes + length.bytes)
    coherent.ranges _ readRights
  exact SharedRelease.release_retains_holder_with_frame after tags tag child holder root node holderNode
    stored (frame.unexposed node stored) holderKnown selected path distinct intermediate (frame.unique fresh)
    coherent roots offset.bytes (offset.bytes + length.bytes) rangeFrame vacancy frame.frozen readable writable

/-- Restore the earlier holder's writable region at the exact release result. -/
theorem SharedChildFrame.releaseHolder {original read after : BorrowTree}
    {parent child holder root : UniIndex} {tag : BorTag} {offset length : Size}
    {inside : DedupRangeMap LocationState}
    (frame : SharedChildFrame original read after parent child tag offset length inside)
    (tags : ProtectedTags) (coherent : CoherentForest after) (roots : after.roots = #[root])
    (selected : after.indexOfTag tag = some child)
    (node : TreeNode) (stored : after.nodeAt child = some node) (tagged : node.tag = tag)
    (holderPresent : ∃ data, original.nodeAt holder = some data)
    (chain : Ancestor original holder parent)
    (unheld : ∀ index data, original.nodeAt index = some data →
      Ancestor original index parent → ¬ Ancestor original index holder →
        (tags.remove tag).contains data.tag = false)
    (fresh : ∀ index data, original.nodeAt index = some data → data.tag ≠ tag)
    (extent : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat)
    (readRights : ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
      point.toNat < (offset.bytes + length.bytes).toNat →
      ∀ row, ValueAt after.locations point row → LocationAccessRights after row tags child .Read)
    (holderRights : OwnedOn (fun row => LocationRights read row (tags.remove tag) holder) offset.bytes
      (offset.bytes + length.bytes) read.locations) :
    ∃ finished, finished = {after with locations := finished.locations} ∧ CoherentForest finished ∧
      finished.locations.size = after.locations.size ∧
      OwnedOn (fun row => LocationRights finished row (tags.remove tag) holder)
        offset.bytes (offset.bytes + length.bytes) finished.locations ∧
      ∀ post failure, Miri.Verification.ProtectorReleaseWP.releasePre tag tags post failure after ↔ post finished := by
  obtain ⟨finished, shape, valid, size, rights, _, _, exactRelease⟩ :=
    frame.releaseHolderWithFrame tags coherent roots selected node stored tagged holderPresent
      chain unheld fresh extent readRights holderRights
  exact ⟨finished, shape, valid, size, rights, exactRelease⟩

theorem concrete_shared_readable_reborrow_with_frame
    (tree : BorrowTree) (protectors : ProtectedTags)
    (parentTag tag : BorTag) (parent root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (coherent : CoherentForest tree) (parentNode : TreeNode)
    (parentStored : tree.nodeAt parent = some parentNode)
    (roots : tree.roots = #[root]) (parentFound : tree.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes) (rank : depth.depth parent < tree.nodes.size)
    (tagFresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (clean : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, segment.data = sharedState)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationAccessRights tree location protectors parent .Read)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) tag inside .Frozen held
    read.status = .Completed ∧ result.outcome = .ok () ∧
      result.tree.locations.size = tree.locations.size ∧
      CoherentForest result.tree ∧ result.tree.roots = #[root] ∧
      ∃ child, result.tree.indexOfTag tag = some child ∧
        (∃ node, result.tree.nodeAt child = some node ∧
          node.tag = tag ∧ node.parent = some parent ∧ node.defaultInitialPermission = .Frozen) ∧
        SharedChildFrame tree read.tree result.tree parent child tag offset length inside ∧
        ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
          point.toNat < (offset.bytes + length.bytes).toNat →
          ∀ location, ValueAt result.tree.locations point location →
            LocationAccessRights result.tree location protectors child .Read := by
  let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
  let archivedDepth : GeneralBorrowExposure.ParentDepth tree.nodes :=
    ⟨depth.depth, depth.bounded, depth.parent⟩
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index node known child member
    have fromChild : child ∈ node.children := by simpa using member
    obtain ⟨node, found, _⟩ := (coherent.childEdges index node known).2.1 child fromChild
    exact ⟨node, found⟩
  have scopedClean : OwnedOn
      (fun row => ∀ index, tree.nodeAt index = none → row.perms.get index = none)
      offset.bytes (offset.bytes + length.bytes) tree.locations := by
    intro pos valid _ _ _ index vacant
    exact clean index vacant pos valid
  have fullClean : OwnedOn
      (fun row => ∀ index, tree.nodeAt index = none → row.perms.get index = none)
      0 tree.locations.size.bytes tree.locations := by
    intro pos valid _ _ _ index vacant
    exact clean index vacant pos valid
  obtain ⟨readOk, readCoherent, readHead, readFound, _, readSize, readOwners⟩ :=
    retag_readable_ownership tree protectors parentTag parent root offset length offset.bytes
      (offset.bytes + length.bytes) coherent parentNode parentStored roots parentFound owners scopedClean
      bounds (Nat.le_refl _) (Nat.le_refl _)
  have readClean := readable_preserves_vacant tree protectors parentTag parent root offset length coherent
    parentNode parentStored roots parentFound archivedDepth children bounds owners 0 tree.locations.size.bytes fullClean
  rw [← readSize] at readClean
  have cleanAll := all_entries_of_owned read.tree.locations readCoherent.ranges _ readClean
  have frame : read.tree = {tree with locations := read.tree.locations} :=
    GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) offset length .Read protectors .VisitChildrenOfAccessed
  have sameNodes : read.tree.nodes = tree.nodes := by
    have equality := congrArg BorrowTree.nodes frame
    exact equality
  have sameMap : read.tree.tagMapping = tree.tagMapping := by
    have equality := congrArg BorrowTree.tagMapping frame
    exact equality
  let readDepth : BorrowTree.ZeroProtection.ParentDepth read.tree.nodes := {
    depth := depth.depth
    bounded := by
      intro index node found
      rw [sameNodes] at found ⊢
      exact depth.bounded index node found
    parent := by
      intro index node found parent edge
      rw [sameNodes] at found ⊢
      exact depth.parent index node found parent edge }
  have readRank : readDepth.depth parent < read.tree.nodes.size := by
    change depth.depth parent < read.tree.nodes.size
    rwa [sameNodes]
  have readTagFresh : read.tree.indexOfTag tag = none := by
    unfold BorrowTree.indexOfTag
    rwa [sameMap]
  have reuseRead : ∀ index, read.tree.tagMapping.deassigned.back? = some index →
      index.toNat < read.tree.nodes.size ∧ read.tree.nodeAt index = none := by
    intro index selected
    rw [sameMap] at selected
    simpa only [sameNodes, BorrowTree.nodeAt] using reuse index selected
  obtain ⟨mapping, child, selected, slot, vacant⟩ :=
    select_slot read.tree tag readTagFresh (by simpa only [sameMap] using room)
      (by simpa only [sameMap, sameNodes] using aligned) reuseRead
  have readSpan : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ read.tree.locations.size.bytes.toNat := by
    rw [readSize]
    exact span
  have complete := newChild_shared_completes read.tree offset parentTag tag parent child mapping
    inside held selected readFound parentNode readHead vacant slot readCoherent.ranges readDepth
    readRank readSpan frozen
  let result := read.tree.newChild offset (.concrete parentTag) tag inside .Frozen held
  have key : result.tree.indexOfTag tag = some child :=
    newChild_selected_key read.tree offset (.concrete parentTag) tag inside .Frozen held mapping child selected
  have metadata := newChild_nodeMetadata read.tree offset parentTag tag parent child mapping inside
    .Frozen held selected readFound parentNode readHead vacant complete child
  have childStored : ∃ node, result.tree.nodeAt child = some node ∧
      node.tag = tag ∧ node.parent = some parent ∧ node.defaultInitialPermission = .Frozen := by
    rw [ite_eq_left (Eq.refl child)] at metadata
    change nodeMetadata result.tree child = some (tag, some parent, .Frozen) at metadata
    unfold nodeMetadata at metadata
    cases found : result.tree.nodeAt child with
    | none => simp [found] at metadata
    | some node =>
      simp only [found, Option.map_some] at metadata
      exact ⟨node, rfl, congrArg Prod.fst (Option.some.inj metadata),
        congrArg (fun x => x.2.1) (Option.some.inj metadata),
        congrArg (fun x => x.2.2) (Option.some.inj metadata)⟩
  have frameWith : FramedWith (fun state => state.permission = .Frozen ∧ state.accessed = true)
        read.tree.locations child result.tree := by
    refine newChild_framed_with ?_ read.tree offset parentTag tag parent child mapping inside .Frozen
      held selected readFound parentNode readHead vacant readCoherent.ranges
      (fun position valid => cleanAll position valid child vacant) ?_ ?_ complete
    · intro old new permission accessed h
      exact ⟨permission.symm.trans h.1, accessed.symm.trans h.2⟩
    · intro segment member start checked
      obtain ⟨ordered, bounded⟩ := readSpan segment member
      obtain ⟨other, found, exactBounds⟩ := selected_size offset segment.range _ ordered bounded
      have same := Except.ok.inj (found.symm.trans checked)
      subst start
      exact exactBounds
    · intro segment member
      rw [frozen segment member]
      exact ⟨rfl, rfl⟩
  obtain ⟨coherentAfter, sameRoots⟩ := initial_child_coherent read.tree offset parentTag tag parent
    child mapping inside .Frozen held .Read rfl rfl rfl selected readFound parentNode readHead vacant slot
    readCoherent readDepth readRank complete frameWith.2.1
  obtain ⟨attachment, _⟩ := MutableSliceRetag.attachment read.tree offset parentTag tag parent child mapping
    inside .Frozen held readCoherent selected readFound parentNode readHead vacant complete
  have metadataBefore := newChild_nodeMetadata read.tree offset parentTag tag parent child mapping inside
    .Frozen held selected readFound parentNode readHead vacant complete
  have oldNodes : ∀ index node, index ≠ child → result.tree.nodeAt index = some node →
      ∃ prior, read.tree.nodeAt index = some prior ∧ prior.tag = node.tag ∧
        node.defaultInitialPermission = prior.defaultInitialPermission := by
    intro index node other found
    have same := metadataBefore index
    change nodeMetadata result.tree index = _ at same
    simp only [ite_eq_right other] at same
    unfold nodeMetadata at same
    simp only [found, Option.map_some] at same
    cases prior : read.tree.nodeAt index with
    | none => simp [prior] at same
    | some previous =>
      simp only [prior, Option.map_some] at same
      have values := Option.some.inj same
      exact ⟨previous, rfl, (congrArg Prod.fst values).symm, congrArg (fun v => v.2.2) values⟩
  have footprint : SharedChildFrame tree read.tree result.tree parent child tag offset length inside := by
    refine ⟨frame, attachment, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro index data distinct found
      obtain ⟨previous, existsBefore, tag, permission⟩ := oldNodes index data distinct found
      exact ⟨previous, by
        unfold BorrowTree.nodeAt at existsBefore
        rwa [sameNodes] at existsBefore, tag, permission⟩
    · exact newChild_initial_unexposed read.tree offset parentTag tag parent child mapping inside .Frozen held .Read
        rfl rfl rfl selected readFound parentNode readHead vacant complete
    · intro position bounded state stored
      have hasRows : result.tree.locations.entries.size ≠ 0 := by omega
      have geometry := frameWith.2.1
      change result.tree.locations.WellFormed at geometry
      simp only [DedupRangeMap.WellFormed, hasRows, ↓reduceDIte] at geometry
      let point := result.tree.locations.entries[position].range.start
      exact ((frameWith.2.2 point position bounded (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _))
        (geometry.2.1 position bounded)).2 state stored).1
    · intro extent
      exact RetagReleaseFootprint.materialized_and_vacant read.tree offset length parentTag tag parent child
        parentNode mapping inside .Frozen held readCoherent selected readFound readHead vacant
        (fun index empty position valid => cleanAll position valid index empty) (by rw [readSize]; exact bounds)
        (fun segment member => ⟨(span segment member).1, extent segment member⟩) complete
    · intro fresh index node stored hasTag
      by_cases equal : index = child
      · exact equal
      exfalso
      have different := equal
      obtain ⟨prior, priorFound, sameTag, _⟩ := oldNodes index node different stored
      have originalFound : tree.nodeAt index = some prior := by
        unfold BorrowTree.nodeAt at priorFound
        rwa [sameNodes] at priorFound
      exact fresh index prior originalFound (sameTag.trans hasTag)
    · intro source oldTags newTags holderPresent freshUnheld retained owns
      exact SharedRelease.retained_holder_after_shared_child read.tree offset parentTag tag parent child source
        parentNode mapping inside held readCoherent selected readFound readHead vacant holderPresent complete frameWith
        oldTags newTags freshUnheld retained offset.bytes (offset.bytes + length.bytes) owns
    · intro watch different lower upper materialized
      exact SharedRelease.retained_materialization_after_attach frameWith different lower upper materialized
    · intro query different
      have ran := newChild_older_exposure read.tree offset parentTag tag parent child query mapping inside
        .Frozen held .Read rfl rfl rfl selected readFound parentNode readHead vacant different complete
      unfold BorrowTree.nodeAt at ran ⊢
      rw [sameNodes] at ran
      exact ran
    · intro query different
      have ran := newChild_old_key read.tree offset (.concrete parentTag) tag query inside .Frozen held
        mapping child different selected
      change result.tree.indexOfTag query = read.tree.indexOfTag query at ran
      simpa only [BorrowTree.indexOfTag, sameMap] using ran
  refine ⟨readOk, complete, frameWith.1.trans readSize, coherentAfter, sameRoots.trans
    ((congrArg BorrowTree.roots frame).trans roots), child, key, childStored, footprint, ?_⟩
  intro point lower upper location indexed
  obtain ⟨pos, valid, start, stop, selectedLocation⟩ := indexed
  have pointFrame := frameWith.2.2 point pos valid
    (UInt64.le_iff_toNat_le.mpr start) (UInt64.lt_iff_toNat_lt.mpr stop)
  rw [selectedLocation] at pointFrame
  apply inherit_shared_read attachment protectors tag point location pointFrame
  · intro prior covers
    exact read_owned_byte (tree := read.tree) readOwners lower upper covers
  · intro node found
    obtain ⟨fixed, lookup, tagged, _, defPermission⟩ := childStored
    have eq := Option.some.inj (lookup.symm.trans found)
    subst node
    exact ⟨tagged, defPermission⟩
  · exact oldNodes

theorem concrete_shared_readable_reborrow
    (tree : BorrowTree) (protectors : ProtectedTags)
    (parentTag tag : BorTag) (parent root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (coherent : CoherentForest tree) (parentNode : TreeNode)
    (parentStored : tree.nodeAt parent = some parentNode)
    (roots : tree.roots = #[root]) (parentFound : tree.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes) (rank : depth.depth parent < tree.nodes.size)
    (tagFresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (clean : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, segment.data = sharedState)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationAccessRights tree location protectors parent .Read)
      offset.bytes (offset.bytes + length.bytes) tree.locations) :
    let read := tree.performNormalAccessRange parentTag offset length .Read protectors .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) tag inside .Frozen held
    read.status = .Completed ∧ result.outcome = .ok () ∧
      result.tree.locations.size = tree.locations.size ∧
      CoherentForest result.tree ∧ result.tree.roots = #[root] ∧
      ∃ child, result.tree.indexOfTag tag = some child ∧
        (∃ node, result.tree.nodeAt child = some node ∧
          node.tag = tag ∧ node.parent = some parent ∧ node.defaultInitialPermission = .Frozen) ∧
        ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
          point.toNat < (offset.bytes + length.bytes).toNat →
          ∀ location, ValueAt result.tree.locations point location →
            LocationAccessRights result.tree location protectors child .Read := by
  obtain ⟨readOk, done, capacity, forest, rootsAfter, child, key, stored, _, rights⟩ :=
    concrete_shared_readable_reborrow_with_frame tree protectors parentTag tag parent root offset length
      inside held coherent parentNode parentStored roots parentFound depth rank tagFresh room aligned reuse clean
      span frozen bounds owners
  exact ⟨readOk, done, capacity, forest, rootsAfter, child, key, stored, rights⟩

#print axioms concrete_shared_readable_reborrow
end DuplicatePrefix.ArchiveForestProjection

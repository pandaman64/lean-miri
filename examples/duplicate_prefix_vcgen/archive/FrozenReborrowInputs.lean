import duplicate_prefix.AsMutHolderScope
import duplicate_prefix.TightParentDepth

namespace DuplicatePrefix.FrozenReborrowInputs

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint RetagFrozenChild

set_option maxRecDepth 65536
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false

/-- Independent structural evidence for a concrete reborrow's input. -/
structure Stage (tree : BorrowTree) (tags : ProtectedTags) (parentTag newTag : BorTag)
    (parent root : UniIndex) (offset length : Size) (inside : DedupRangeMap LocationState)
    (held : Bool) : Prop where
  coherent : CoherentForest tree
  parentFound : tree.indexOfTag parentTag = some parent
  parentPresent : ∃ node, tree.nodeAt parent = some node
  roots : tree.roots = #[root]
  fresh : tree.indexOfTag newTag = none
  room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295
  aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size
  reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
    index.toNat < tree.nodes.size ∧ tree.nodeAt index = none
  bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat
  span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
    offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat
  policy : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data
  owners : OwnedOn (fun row => LocationRights tree row tags parent)
    offset.bytes (offset.bytes+length.bytes) tree.locations
  scope : MaterializedWithin tree parent offset.bytes (offset.bytes+length.bytes)
  vacant : VacantRows tree

/-- An actual bounded read and child insertion, with a designated outer
holder's scope and lineage retained for its eventual release. -/
theorem retag
    {tree : BorrowTree} {tags mask : ProtectedTags} {parentTag newTag : BorTag}
    {parent root watch : UniIndex} {offset length : Size} {inside : DedupRangeMap LocationState}
    {held : Bool}
    (stage : Stage tree tags parentTag newTag parent root offset length inside held)
    (watchPresent : ∃ node, tree.nodeAt watch = some node)
    (watched : MaterializedWithin tree watch offset.bytes (offset.bytes+length.bytes))
    (oldPath : AsMutHolderScope.BetweenTags tree mask watch parent)
    (newUnheld : mask.contains newTag = false) :
    let read := tree.performNormalAccessRange parentTag offset length .Read tags .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) newTag inside (.ReservedFrz false) held
    read.status = .Completed ∧ result.outcome = .ok () ∧
      ∃ child, result.tree.indexOfTag newTag = some child ∧
        (∃ node, result.tree.nodeAt watch = some node) ∧
        MaterializedWithin result.tree watch offset.bytes (offset.bytes+length.bytes) ∧
        AsMutHolderScope.BetweenTags result.tree mask watch child ∧
        (∀ query, query ≠ newTag → result.tree.indexOfTag query = tree.indexOfTag query) ∧
        (∀ query data, tree.nodeAt query = some data →
          (result.tree.nodeAt query).map TreeNode.isExposed = some data.isExposed) := by
  obtain ⟨parentNode, found⟩ := stage.parentPresent
  obtain ⟨watchedNode, reallyWatched⟩ := watchPresent
  obtain ⟨rank, bounds, decreases⟩ := stage.coherent.parentDepth
  let initial : BorrowTree.ZeroProtection.ParentDepth tree.nodes :=
    ⟨rank,bounds,by
      intro index node lookup previous edge
      obtain ⟨prior, known⟩ := stage.coherent.parentPresent index node previous lookup edge
      exact ⟨prior, known, decreases index node previous lookup edge⟩⟩
  obtain ⟨tight, numerical⟩ := BorrowTree.ZeroProtection.ParentDepth.tight tree.nodes initial
  obtain ⟨readOk, installOk, nodes, child, key, attached, scope, oldMetadata, newMetadata, oldKeys, exposures⟩ :=
    FrozenReborrowScope.frozen_reborrow_preserves_scope tree tags parentTag newTag parent root watch offset length
      inside held stage.coherent parentNode watchedNode stage.parentFound found reallyWatched stage.roots tight
      (numerical parent parentNode found) stage.fresh stage.room stage.aligned stage.reuse stage.bounds
      stage.span stage.policy stage.owners stage.scope stage.vacant watched
  have readWatch : (tree.performNormalAccessRange parentTag offset length .Read tags .VisitChildrenOfAccessed).tree.nodeAt
      watch = some watchedNode := by
    simpa only [BorrowTree.nodeAt,nodes] using reallyWatched
  obtain ⟨still, planted, _⟩ := attached.oldEdges watch watchedNode readWatch
  exact ⟨readOk,installOk,child,key,⟨still,planted⟩,scope,oldPath.retag nodes attached oldMetadata newTag newUnheld newMetadata,oldKeys,exposures⟩

end DuplicatePrefix.FrozenReborrowInputs

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.FrozenReborrowInputs.retag) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved scoped reborrow input dependency {dependency}"

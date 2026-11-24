import duplicate_prefix.CopyHolderRights
import duplicate_prefix.RetagFrozenChild
import duplicate_prefix.RetagKeyFrame
import duplicate_prefix.RetagGraphFrame
import duplicate_prefix.SharedHolderAttach
import MutableSliceRetag

namespace DuplicatePrefix.FrozenReborrowScope

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open Miri.Verification.RangeModifyLaw
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint RetagFrozenChild
open Miri.Verification.MutableRetagFootprint

set_option maxRecDepth 65536
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

/-- The associated parent read can materialize permissions only inside its
actual checked interval. This frames the same extent for any older tag. -/
theorem read_scope (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (parent root watch : UniIndex) (offset length : Size)
    (coherent : CoherentForest tree) (node : TreeNode) (present : tree.nodeAt parent = some node)
    (roots : tree.roots = #[root]) (found : tree.indexOfTag tag = some parent)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights tree row tags parent)
      offset.bytes (offset.bytes+length.bytes) tree.locations)
    (scope : MaterializedWithin tree watch offset.bytes (offset.bytes+length.bytes)) :
    let read := tree.performNormalAccessRange tag offset length .Read tags .VisitChildrenOfAccessed
    MaterializedWithin read.tree watch offset.bytes (offset.bytes+length.bytes) := by
  have authorized := bounded_slots tree tags parent root .Read offset length coherent node present roots bounds owners
  let good (point : UInt64) (row : LocationTree) :=
    ∀ state, row.perms.get watch = some state →
      offset.bytes.toNat ≤ point.toNat ∧ point.toNat < (offset.bytes+length.bytes).toNat
  have result := preserve_range_property_with_byte_frame tree tag parent tags .Read .VisitChildrenOfAccessed
    offset length offset.bytes (offset.bytes+length.bytes) (fun _ => True) found coherent.ranges bounds
    (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ _ => True.intro) good scope
    (fun _ _ lo hi _ _ _ _ _ => ⟨lo,hi⟩) authorized
  exact result.2.2.2.2.2

/-- Exact frozen child attachment and the materialization footprint of an
older node. It uses the selected node used by the actual allocator. -/
theorem attach_scope (tree : BorrowTree) (offset length : Size)
    (parentTag tag : BorTag) (parent child watch : UniIndex) (parentNode watched : TreeNode)
    (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState) (held : Bool)
    (coherent : CoherentForest tree) (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode)
    (watchedPresent : tree.nodeAt watch = some watched)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (vacant : tree.nodeAt child = none)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get child = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data)
    (done : (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).outcome = .ok ())
    (scope : MaterializedWithin tree watch offset.bytes (offset.bytes+length.bytes)) :
    let after := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
    MutableSliceRights.Attachment tree after parent child ∧
      MaterializedWithin after watch offset.bytes (offset.bytes+length.bytes) ∧
      (∀ old node, old ≠ child → after.nodeAt old = some node →
        ∃ previous, tree.nodeAt old = some previous ∧ previous.tag = node.tag) ∧
      (∀ node, after.nodeAt child = some node → node.tag = tag) := by
  let after := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
  have framed : RetagLocationFrame.Framed tree.locations child after := by
    apply RetagLocationFrame.newChild_framed tree offset parentTag tag parent child mapping inside (.ReservedFrz false) held
      mapped parentFound parentNode present vacant coherent.ranges clean _ _ done
    · intro segment member start checked
      obtain ⟨ordered, bounded⟩ := span segment member
      obtain ⟨startNat, writtenEnd⟩ := RetagReleaseFootprint.finish_from offset start tree.locations
        segment.range ordered bounded checked
      omega
    · intro segment member
      rcases frozen segment member with exactState | exactState <;> rw [exactState] <;> rfl
  have away : watch ≠ child := by
    intro equal
    rw [equal,vacant] at watchedPresent
    contradiction
  obtain ⟨attached, newTag⟩ := MutableSliceRetag.attachment tree offset parentTag tag parent child mapping
    inside (.ReservedFrz false) held coherent mapped parentFound parentNode present vacant done
  have kept := SharedRelease.retained_materialization_after_attach framed away offset.bytes (offset.bytes+length.bytes) scope
  have metadata := newChild_nodeMetadata tree offset parentTag tag parent child mapping inside (.ReservedFrz false)
    held mapped parentFound parentNode present vacant done
  refine ⟨attached,kept,?_,newTag⟩
  intro old data different lookup
  change after.nodeAt old = some data at lookup
  have shape := metadata old
  change nodeMetadata after old = _ at shape
  simp only [ite_eq_right different, nodeMetadata, lookup, Option.map_some] at shape
  cases prev : tree.nodeAt old with
  | none => simp only [prev,Option.map_none,reduceCtorEq] at shape
  | some prior =>
    rw [prev, Option.map_some] at shape
    exact ⟨prior,rfl,(congrArg Prod.fst (Option.some.inj shape)).symm⟩

private theorem lift_old_path {before after : BorrowTree} {parent child watch index : UniIndex}
    (frame : MutableSliceRights.Attachment before after parent child)
    (path : Ancestor before index watch) : Ancestor after index watch := by
  induction path with
  | self => exact .self _
  | parent path node found edge ih =>
    obtain ⟨next, stored, unchanged⟩ := frame.oldEdges _ node found
    exact .parent ih next stored (unchanged.trans edge)

/-- A same-scope retag appends exactly one node to the prior ancestry.
The same unprotected-intermediate law extends when that new tag is unheld. -/
theorem append_unheld_scope {before after : BorrowTree} {parent child watch : UniIndex}
    (frame : MutableSliceRights.Attachment before after parent child)
    (watchPath : Ancestor before watch parent)
    (oldTags : ∀ index node, index ≠ child → after.nodeAt index = some node →
      ∃ prior, before.nodeAt index = some prior ∧ prior.tag = node.tag)
    (newTag : BorTag) (newTags : ∀ node, after.nodeAt child = some node → node.tag = newTag)
    (tags : ProtectedTags) (freshUnheld : tags.contains newTag = false)
    (oldUnheld : ∀ index node, before.nodeAt index = some node →
      Ancestor before index parent → ¬ Ancestor before index watch → tags.contains node.tag = false) :
    Ancestor after watch child ∧
      ∀ index node, after.nodeAt index = some node →
        Ancestor after index child → ¬ Ancestor after index watch → tags.contains node.tag = false := by
  refine ⟨frame.ancestry.mpr (Or.inr watchPath), ?_⟩
  intro index data stored localChild foreignWatch
  by_cases newest : index = child
  · subst index
    rw [newTags data stored]
    exact freshUnheld
  · have oldPath : Ancestor before index parent := by
      rcases frame.ancestry.mp localChild with equal | down
      · exact False.elim (newest equal)
      · exact down
    obtain ⟨prior, known, unchanged⟩ := oldTags index data newest stored
    rw [← unchanged]
    exact oldUnheld index prior known oldPath (fun up => foreignWatch (lift_old_path frame up))

/-- The composed real read and new-child operations preserve an already
scoped ancestor, and expose the selected child and exact graph attachment.
All premises concern the pre-access state and the retag policy. -/
theorem frozen_reborrow_preserves_scope
    (tree : BorrowTree) (tags : ProtectedTags) (parentTag tag : BorTag)
    (parent root watch : UniIndex) (offset length : Size) (inside : DedupRangeMap LocationState)
    (held : Bool) (coherent : CoherentForest tree) (parentNode watched : TreeNode)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode) (watchedPresent : tree.nodeAt watch = some watched)
    (roots : tree.roots = #[root])
    (graph : BorrowTree.ZeroProtection.ParentDepth tree.nodes)
    (rank : graph.depth parent < tree.nodes.size)
    (fresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size)
    (reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (policy : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data)
    (owners : OwnedOn (fun row => LocationRights tree row tags parent)
      offset.bytes (offset.bytes+length.bytes) tree.locations)
    (parentScope : MaterializedWithin tree parent offset.bytes (offset.bytes+length.bytes))
    (vacantRows : VacantRows tree)
    (watchScope : MaterializedWithin tree watch offset.bytes (offset.bytes+length.bytes)) :
    let read := tree.performNormalAccessRange parentTag offset length .Read tags .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held
    read.status = .Completed ∧ result.outcome = .ok () ∧
      read.tree.nodes = tree.nodes ∧
      ∃ child, result.tree.indexOfTag tag = some child ∧
        MutableSliceRights.Attachment read.tree result.tree parent child ∧
        MaterializedWithin result.tree watch offset.bytes (offset.bytes+length.bytes) ∧
        (∀ old node, old ≠ child → result.tree.nodeAt old = some node →
          ∃ previous, tree.nodeAt old = some previous ∧ previous.tag = node.tag) ∧
        (∀ node, result.tree.nodeAt child = some node → node.tag = tag) ∧
        (∀ query, query ≠ tag → result.tree.indexOfTag query = tree.indexOfTag query) ∧
        (∀ query data, tree.nodeAt query = some data →
          (result.tree.nodeAt query).map TreeNode.isExposed = some data.isExposed) := by
  let read := tree.performNormalAccessRange parentTag offset length .Read tags .VisitChildrenOfAccessed
  have footprint : CopyHolderRights.Footprint tree tags parent parent offset.bytes (offset.bytes+length.bytes) :=
    ⟨owners,owners,parentScope,vacantRows⟩
  obtain ⟨readDone, shape, readCoherent, size, readFootprint⟩ :=
    CopyHolderRights.accessRange_retains_holder tree tags parentTag parent parent root .Read offset length
      offset.bytes (offset.bytes+length.bytes) coherent parentNode present roots parentFound (.self parent)
      (fun _ _ _ same unconnected => False.elim (unconnected same)) bounds
      (Nat.le_refl _) (Nat.le_refl _) footprint
  change read.tree = {tree with locations := read.tree.locations} at shape
  have nodes := congrArg BorrowTree.nodes shape
  change read.tree.nodes = tree.nodes at nodes
  have table := congrArg BorrowTree.tagMapping shape
  change read.tree.tagMapping = tree.tagMapping at table
  have oldFound : read.tree.indexOfTag parentTag = some parent := by
    unfold BorrowTree.indexOfTag
    rwa [table]
  have readFresh : read.tree.indexOfTag tag = none := by
    unfold BorrowTree.indexOfTag
    rwa [table]
  have readPresent : read.tree.nodeAt parent = some parentNode := by
    simpa only [BorrowTree.nodeAt,nodes] using present
  have readWatch : read.tree.nodeAt watch = some watched := by
    simpa only [BorrowTree.nodeAt,nodes] using watchedPresent
  let readGraph : BorrowTree.ZeroProtection.ParentDepth read.tree.nodes := ⟨graph.depth,
    fun index node lookup => by
      simpa only [nodes] using graph.bounded index node (by simpa only [nodes] using lookup),
    fun index node lookup previous edge => by
      simpa only [nodes] using graph.parent index node (by simpa only [nodes] using lookup) previous edge⟩
  have readRank : readGraph.depth parent < read.tree.nodes.size := by
    change graph.depth parent < read.tree.nodes.size
    rwa [nodes]
  have readWatchScope := read_scope tree tags parentTag parent root watch offset length coherent parentNode
    present roots parentFound bounds owners watchScope
  have readReuse : ∀ index, read.tree.tagMapping.deassigned.back? = some index →
      index.toNat < read.tree.nodes.size ∧ read.tree.nodeAt index = none := by
    simpa only [BorrowTree.nodeAt,table,nodes] using reuse
  have readSpan : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ read.tree.locations.size.bytes.toNat := by
    simpa only [show read.tree.locations.size = tree.locations.size from size] using span
  obtain ⟨mapping, child, mapped, empty, completed, _⟩ :=
    newChild_frozen_frame_with_mode read.tree offset parentTag tag parent parentNode inside held
      oldFound readPresent readFresh (by simpa only [table] using room)
      (by simpa only [table,nodes] using aligned) readReuse readCoherent.ranges readGraph readRank
      readFootprint.vacant readSpan policy
  have winningKey := newChild_selected_key read.tree offset (.concrete parentTag) tag
    inside (.ReservedFrz false) held mapping child mapped
  obtain ⟨attached, kept, tagsFrame, newTag⟩ :=
    attach_scope read.tree offset length parentTag tag parent child watch parentNode watched mapping inside held
      readCoherent oldFound readPresent readWatch mapped empty (readFootprint.vacant child empty)
      readSpan policy completed readWatchScope
  refine ⟨readDone,completed,nodes,child,winningKey,attached,kept,?_,newTag,?_,?_⟩
  · intro old node distinct lookup
    obtain ⟨previous,known,same⟩ := tagsFrame old node distinct lookup
    exact ⟨previous,by simpa only [BorrowTree.nodeAt, nodes] using known,same⟩
  · intro old different
    have chosen := newChild_old_key read.tree offset (.concrete parentTag) tag old inside
      (.ReservedFrz false) held mapping child different mapped
    exact chosen.trans (by simp only [BorrowTree.indexOfTag,table])
  · intro query data before
    have old : read.tree.nodeAt query = some data := by simpa only [BorrowTree.nodeAt,nodes] using before
    have different : query ≠ child := by
      intro equality
      rw [equality,empty] at old
      contradiction
    have exactExposure := newChild_older_exposure read.tree offset parentTag tag parent child query
      mapping inside (.ReservedFrz false) held (if held then .None else .Read) rfl rfl (by cases held <;> rfl)
      mapped oldFound parentNode readPresent empty different completed
    exact exactExposure.trans (by rw [old]; rfl)

end DuplicatePrefix.FrozenReborrowScope

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.FrozenReborrowScope.read_scope,
      ``DuplicatePrefix.FrozenReborrowScope.attach_scope,
      ``DuplicatePrefix.FrozenReborrowScope.append_unheld_scope,
      ``DuplicatePrefix.FrozenReborrowScope.frozen_reborrow_preserves_scope] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved frozen scope dependency {dependency}"

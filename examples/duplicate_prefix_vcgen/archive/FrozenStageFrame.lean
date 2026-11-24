import duplicate_prefix.RetagSuccessorCapacity
import duplicate_prefix.NonemptyRetagWatch

namespace DuplicatePrefix.FrozenStageFrame

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open Miri.Verification.MutableRetagFootprint Miri.Verification.MutableReferenceRights
open SourceDomain FrozenReborrowInputs ArchiveForestProjection RetagReleaseFootprint RetagFrozenChild
open GeneralRangeMapOrigins NonemptyReturnWatch

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Exact metadata and permissions of one installed reborrow. -/
structure Applied (original read next : BorrowTree) (parentTag tag : BorTag)
    (parent child : UniIndex) (start length : Size)
    (inside : DedupRangeMap LocationState) (held : Bool) : Prop where
  nextExact : next = (read.newChild start (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
  readShape : read = {original with locations := read.locations}
  coherent : CoherentForest read
  size : read.locations.size = original.locations.size
  parentAt : ∃ node, read.nodeAt parent = some node
  parentKey : read.indexOfTag parentTag = some parent
  slot : ∃ mapping, read.tagMapping.insert tag = .Inserted mapping child
  vacant : read.nodeAt child = none
  complete : (read.newChild start (.concrete parentTag) tag inside (.ReservedFrz false) held).outcome = .ok ()
  frame : RetagLocationFrame.Framed read.locations child next
  childScope : MaterializedWithin next child start.bytes (start.bytes+length.bytes)
  attachment : MutableSliceRights.Attachment read next parent child
  keys : ∀ old, old ≠ tag → next.indexOfTag old = original.indexOfTag old
  oldNodes : ∀ i node, i ≠ child → next.nodeAt i = some node →
    ∃ prior, original.nodeAt i = some prior ∧ prior.tag = node.tag
  newTag : ∀ node, next.nodeAt child = some node → node.tag = tag
  exposure : ∀ i node, original.nodeAt i = some node →
    (next.nodeAt i).map TreeNode.isExposed = some node.isExposed

theorem apply
    (tree : BorrowTree) (tags : ProtectedTags) (parentTag tag : BorTag) (parent root : UniIndex)
    (start length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (stage : StageData tree tags parentTag tag parent root start length inside held)
    (insideBounds : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat) :
    let read := tree.performNormalAccessRange parentTag start length .Read tags .VisitChildrenOfAccessed
    let installed := read.tree.newChild start (.concrete parentTag) tag inside (.ReservedFrz false) held
    ∃ child, installed.tree.indexOfTag tag = some child ∧
      Applied tree read.tree installed.tree parentTag tag parent child start length inside held := by
  intro effect installed
  obtain ⟨parentNode, parentAt⟩ := stage.parentPresent
  obtain ⟨shape, readCoherent, size, clean⟩ :=
    RetagSuccessorCapacity.readKeepsVacant tree parentTag parent root tags start length stage.parentFound stage.coherent
      stage.roots parentNode parentAt stage.bounds stage.owners stage.vacant
  have readShape : effect.tree = {tree with locations := effect.tree.locations} := shape
  have nodes := congrArg BorrowTree.nodes readShape
  change effect.tree.nodes = tree.nodes at nodes
  have keys := congrArg BorrowTree.tagMapping readShape
  change effect.tree.tagMapping = tree.tagMapping at keys
  have parentKey : effect.tree.indexOfTag parentTag = some parent := by
    simpa only [BorrowTree.indexOfTag,keys] using stage.parentFound
  have tagFresh : effect.tree.indexOfTag tag = none := by
    simpa only [BorrowTree.indexOfTag,keys] using stage.fresh
  have present : effect.tree.nodeAt parent = some parentNode := by
    simpa only [BorrowTree.nodeAt,nodes] using parentAt
  have space (noFree : effect.tree.tagMapping.deassigned.back? = none) :
      effect.tree.tagMapping.mapping.size ≤ 4294967295 := by
    rw [keys] at noFree ⊢
    exact stage.room noFree
  have aligned (noFree : effect.tree.tagMapping.deassigned.back? = none) :
      effect.tree.tagMapping.mapping.size = effect.tree.nodes.size := by
    rw [keys] at noFree
    rw [keys,nodes]
    exact stage.aligned noFree
  have reuse (i : UniIndex) (saved : effect.tree.tagMapping.deassigned.back? = some i) :
      i.toNat < effect.tree.nodes.size ∧ effect.tree.nodeAt i = none := by
    rw [keys] at saved
    simpa only [BorrowTree.nodeAt,nodes] using stage.reuse i saved
  obtain ⟨rank, bound, decreases⟩ := readCoherent.parentDepth
  let depth : BorrowTree.ZeroProtection.ParentDepth effect.tree.nodes := ⟨rank,bound,by
    intro i node known parent edge
    obtain ⟨prior, found⟩ := readCoherent.parentPresent i node parent known edge
    exact ⟨prior,found,decreases i node parent known edge⟩⟩
  obtain ⟨tight,ranked⟩ := BorrowTree.ZeroProtection.ParentDepth.tight effect.tree.nodes depth
  have span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      start.bytes.toNat + segment.range.stop.toNat ≤ effect.tree.locations.size.bytes.toNat := by
    simpa only [show effect.tree.locations.size = tree.locations.size from size] using stage.span
  obtain ⟨mapping, child, mapped, empty, done, framed⟩ :=
    newChild_frozen_frame_with_mode effect.tree start parentTag tag parent parentNode inside held
      parentKey present tagFresh space aligned reuse readCoherent.ranges tight (ranked parent parentNode present)
      clean span stage.policy
  obtain ⟨attached, newTag⟩ := MutableSliceRetag.attachment effect.tree start parentTag tag parent child mapping
    inside (.ReservedFrz false) held readCoherent mapped parentKey parentNode present empty done
  have fits : start.bytes.toNat + length.bytes.toNat ≤ effect.tree.locations.size.bytes.toNat := by
    rw [show effect.tree.locations.size = tree.locations.size from size]
    exact stage.bounds
  have scopedChild := (materialized_and_vacant effect.tree start length parentTag tag parent child parentNode
    mapping inside (.ReservedFrz false) held readCoherent mapped parentKey present empty clean fits
    (fun segment included => ⟨(span segment included).1,insideBounds segment included⟩) done).1
  have mappedTree := newChild_keyMap effect.tree start (.concrete parentTag) tag inside
    (.ReservedFrz false) held mapping child mapped
  have index : installed.tree.indexOfTag tag = some child := by
    change installed.tree.tagMapping.get tag = some child
    rw [show installed.tree.tagMapping = mapping from mappedTree]
    exact inserted_lookup _ _ _ _ mapped
  have prior (old : BorTag) (different : old ≠ tag) : installed.tree.indexOfTag old = tree.indexOfTag old := by
    have still := newChild_old_key effect.tree start (.concrete parentTag) tag old inside (.ReservedFrz false)
      held mapping child different mapped
    simpa only [BorrowTree.indexOfTag,keys] using still
  have perNode := newChild_nodeMetadata effect.tree start parentTag tag parent child mapping inside
    (.ReservedFrz false) held mapped parentKey parentNode present empty done
  refine ⟨child,index,rfl,readShape,readCoherent,size,⟨parentNode,present⟩,parentKey,⟨mapping,mapped⟩,empty,done,framed,
    scopedChild,attached,prior,?_,newTag,?_⟩
  · intro i current old known
    obtain ⟨previous, priorFound, _⟩ := attached.newEdges i current old known
    have metadata := perNode i
    rw [ite_eq_right old] at metadata
    change nodeMetadata installed.tree i = nodeMetadata effect.tree i at metadata
    simp only [nodeMetadata, known, priorFound, Option.map_some] at metadata
    exact ⟨previous,by simpa only [BorrowTree.nodeAt,nodes] using priorFound,
      (congrArg Prod.fst (Option.some.inj metadata)).symm⟩
  · intro i node saved
    have readAt : effect.tree.nodeAt i = some node := by
      simpa only [BorrowTree.nodeAt,nodes] using saved
    have distinct : i ≠ child := by
      intro same
      rw [same,empty] at readAt
      contradiction
    have kept := newChild_older_exposure effect.tree start parentTag tag parent child i mapping inside
      (.ReservedFrz false) held (if held then .None else .Read) rfl rfl (by cases held <;> rfl)
      mapped parentKey parentNode present empty distinct done
    simpa only [readAt,Option.map_some] using kept

theorem Applied.keepsNode {original read next : BorrowTree} {parentTag tag : BorTag}
    {parent child : UniIndex} {start length : Size} {inside : DedupRangeMap LocationState} {held : Bool}
    (applied : Applied original read next parentTag tag parent child start length inside held)
    (watch : UniIndex) (node : TreeNode) (old : original.nodeAt watch = some node) :
    ∃ current, next.nodeAt watch = some current ∧ current.tag = node.tag ∧ current.parent = node.parent := by
  have saved : read.nodeAt watch = some node := by rw [applied.readShape]; exact old
  have distinct : watch ≠ child := by
    intro same
    rw [same,applied.vacant] at saved
    contradiction
  obtain ⟨current,found,parent⟩ := applied.attachment.oldEdges watch node saved
  obtain ⟨prior,priorAt,tag⟩ := applied.oldNodes watch current distinct found
  have same := Option.some.inj (priorAt.symm.trans old)
  subst prior
  exact ⟨current,found,tag.symm,parent⟩

theorem Applied.keepsOriginalActive
    {tree next : BorrowTree} {tags : ProtectedTags} {parentTag tag : BorTag} {parent child root watch : UniIndex}
    {start length : Size} {inside : DedupRangeMap LocationState} {held : Bool}
    (stage : StageData tree tags parentTag tag parent root start length inside held)
    (watchNode : TreeNode) (watchAt : tree.nodeAt watch = some watchNode)
    (scope : AccessedWithin tree watch start.bytes (start.bytes+length.bytes))
    (applied : let read := tree.performNormalAccessRange parentTag start length .Read tags .VisitChildrenOfAccessed
      Applied tree read.tree next parentTag tag parent child start length inside held) :
    AccessedWithin next watch start.bytes (start.bytes+length.bytes) := by
  dsimp only at applied ⊢
  obtain ⟨parentNode, known⟩ := stage.parentPresent
  have run := rangeKeepsWatch tree tags parentTag parent watch root .Read start length stage.coherent
    stage.roots parentNode watchNode known watchAt stage.parentFound stage.bounds
    (bounded_slots tree tags parent root .Read start length stage.coherent parentNode known stage.roots stage.bounds stage.owners)
    start.bytes (start.bytes+length.bytes) (.inr ⟨Nat.le_refl _,Nat.le_refl _⟩) scope
    (fun _ _ => True) (fun _ _ _ _ _ _ => True.intro)
  have different : watch ≠ child := by
    intro equal
    have active : (tree.performNormalAccessRange parentTag start length .Read tags .VisitChildrenOfAccessed).tree.nodeAt watch =
        some watchNode := by rw [applied.readShape]; exact watchAt
    rw [equal,applied.vacant] at active
    contradiction
  exact attachKeepsActiveScope applied.frame different start.bytes (start.bytes+length.bytes) run.2.2.2.2.1

/-- One actual reservation or strong FnEntry retag retains a disjoint
physical writer's permissions and the active extent of its protector. -/
theorem Applied.keepsOutput
    {tree next : BorrowTree} {tags : ProtectedTags} {parentTag tag : BorTag} {parent child root watch writer : UniIndex}
    {start length : Size} {inside : DedupRangeMap LocationState} {held : Bool}
    (stage : StageData tree tags parentTag tag parent root start length inside held)
    (watchNode writerNode : TreeNode) (watchAt : tree.nodeAt watch = some watchNode)
    (writerAt : tree.nodeAt writer = some writerNode) (foreign : ¬ Ancestor tree watch parent)
    (proofTags : ProtectedTags) (lo hi : UInt64) (scope : AccessedWithin tree watch lo hi)
    (observes : UInt64 → Prop)
    (rights : RangeModifyLaw.EachByte tree.locations (fun point row =>
      (point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) →
      observes point → LocationRights tree row proofTags writer))
    (applied : let read := tree.performNormalAccessRange parentTag start length .Read tags .VisitChildrenOfAccessed
      Applied tree read.tree next parentTag tag parent child start length inside held) :
    AccessedWithin next watch lo hi ∧ ¬ Ancestor next watch child ∧
    RangeModifyLaw.EachByte next.locations (fun point row =>
      (point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) →
      observes point → LocationRights next row proofTags writer) := by
  dsimp only at applied ⊢
  let read := tree.performNormalAccessRange parentTag start length .Read tags .VisitChildrenOfAccessed
  obtain ⟨actor,known⟩ := stage.parentPresent
  have run := rangeKeepsWatch tree tags parentTag parent watch root .Read start length stage.coherent
    stage.roots actor watchNode known watchAt stage.parentFound stage.bounds
    (bounded_slots tree tags parent root .Read start length stage.coherent actor known stage.roots stage.bounds stage.owners)
    lo hi (.inl foreign) scope (fun point row => observes point → LocationRights tree row proofTags writer) rights
  have readShape : read.tree = {tree with locations := read.tree.locations} := applied.readShape
  have same := congrArg BorrowTree.nodes readShape
  change read.tree.nodes = tree.nodes at same
  have readRights : RangeModifyLaw.EachByte read.tree.locations (fun point row =>
        (point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) →
        observes point → LocationRights read.tree row proofTags writer) := by
    intro point pos valid lower upper outside watched
    exact CopyHolderRights.rights_frame same.symm _ proofTags writer (run.2.2.2.2.2 point pos valid lower upper outside watched)
  obtain ⟨node,present⟩ := applied.parentAt
  obtain ⟨map,selected⟩ := applied.slot
  have frame := applied.frame
  have extent := applied.childScope
  rw [applied.nextExact] at frame extent ⊢
  exact childKeepsWatch read.tree start length proofTags proofTags parentTag tag parent child watch writer
    node map inside (.ReservedFrz false) held (.inr rfl) applied.coherent applied.parentKey present applied.vacant selected
    ⟨watchNode,by simpa only [BorrowTree.nodeAt,same] using watchAt⟩
    ⟨writerNode,by simpa only [BorrowTree.nodeAt,same] using writerAt⟩
    (fun path => foreign (AsMutHolderScope.ancestor_frame same path)) (fun _ _ _ => rfl)
    applied.complete frame extent lo hi run.2.2.2.2.1 observes readRights

end DuplicatePrefix.FrozenStageFrame

#print axioms DuplicatePrefix.FrozenStageFrame.apply
#print axioms DuplicatePrefix.FrozenStageFrame.Applied.keepsOriginalActive
#print axioms DuplicatePrefix.FrozenStageFrame.Applied.keepsOutput

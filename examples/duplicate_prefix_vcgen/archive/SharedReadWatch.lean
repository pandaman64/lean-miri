import duplicate_prefix.NonemptyRetagWatch
import duplicate_prefix.SharedReborrowContinuity
import duplicate_prefix.CopyHolderRights

namespace DuplicatePrefix.NonemptyReturnWatch

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open MutableSliceRights SourceDomain GeneralRangeMapOrigins RetagLocationFrame ArchiveForestProjection
open RetagReleaseFootprint Miri.Verification.RangeModifyLaw

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Write rights on a single byte, irrespective of how the range map is split. -/
def AtByte (tree : BorrowTree) (point : UInt64) (tags : ProtectedTags) (writer : UniIndex) : Prop :=
  ∀ position (valid : position < tree.locations.entries.size),
    tree.locations.entries[position].range.start ≤ point →
    point < tree.locations.entries[position].range.stop →
    LocationRights tree tree.locations.entries[position].data tags writer

theorem ancestryFrame {before after : BorrowTree} (same : before.nodes = after.nodes) {upper lower : UniIndex} :
    Ancestor before upper lower ↔ Ancestor after upper lower := by
  have unchanged (index : UniIndex) : before.nodeAt index = after.nodeAt index := by
    unfold BorrowTree.nodeAt
    rw [same]
  constructor
  · intro path
    induction path with
    | self => exact .self _
    | parent _ data present edge ih => exact .parent ih data ((unchanged _).symm ▸ present) edge
  · intro path
    induction path with
    | self => exact .self _
    | parent _ data present edge ih => exact .parent ih data ((unchanged _) ▸ present) edge

/-- An older slot outside the actual shared reborrow span retains its write
rights and scoped access bit across the concrete read and child insertion. -/
theorem sharedReadKeepsWatch
    (tree after : BorrowTree) (parentTag tag : BorTag) (parent child watch writer root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState)
    (forRead watchMask nextMask : ProtectedTags)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (actorNode watcher writerNode childNode : TreeNode)
    (actorAt : tree.nodeAt parent = some actorNode)
    (watchAt : tree.nodeAt watch = some watcher) (writerAt : tree.nodeAt writer = some writerNode)
    (childAt : after.nodeAt child = some childNode) (childDefault : childNode.defaultInitialPermission = .Frozen)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (reader : OwnedOn (fun row => LocationAccessRights tree row forRead parent .Read)
      offset.bytes (offset.bytes+length.bytes) tree.locations)
    (shape : SharedChildFrame tree
      (tree.performNormalAccessRange parentTag offset length .Read forRead .VisitChildrenOfAccessed).tree
      after parent child tag offset length inside)
    (extent : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat)
    (foreign : ¬ Ancestor tree watch parent)
    (mask : ∀ i data, tree.nodeAt i = some data → nextMask.contains data.tag = watchMask.contains data.tag)
    (lo hi point : UInt64)
    (outside : point.toNat < offset.bytes.toNat ∨ (offset.bytes+length.bytes).toNat ≤ point.toNat)
    (active : AccessedWithin tree watch lo hi)
    (rights : AtByte tree point watchMask writer) :
    AccessedWithin after watch lo hi ∧ ¬ Ancestor after watch child ∧ AtByte after point nextMask writer := by
  let read := (tree.performNormalAccessRange parentTag offset length .Read forRead .VisitChildrenOfAccessed).tree
  have auth := bounded_slots_from_rights tree forRead parent root .Read offset length coherent actorNode actorAt roots bounds reader
  have typedPoint : EachByte tree.locations (fun q row =>
      (q.toNat < offset.bytes.toNat ∨ (offset.bytes+length.bytes).toNat ≤ q.toNat) →
      q = point → LocationRights tree row watchMask writer) := by
    intro q pos valid start stop _ same
    subst q
    exact rights pos valid start stop
  have preserved := rangeKeepsWatch tree forRead parentTag parent watch root .Read offset length coherent
    roots actorNode watcher actorAt watchAt parentFound bounds auth lo hi (.inl foreign) active
    (fun q row => q = point → LocationRights tree row watchMask writer) typedPoint
  have sameNodes : tree.nodes = read.nodes := (congrArg BorrowTree.nodes shape.readMetadata).symm
  have olderWatch : read.nodeAt watch = some watcher := by
    unfold BorrowTree.nodeAt
    rw [← sameNodes]
    exact watchAt
  have olderWriter : read.nodeAt writer = some writerNode := by
    unfold BorrowTree.nodeAt
    rw [← sameNodes]
    exact writerAt
  have distinct : watch ≠ child := by
    intro eq
    rw [eq, shape.attached.fresh] at olderWatch
    contradiction
  have activeAfter : AccessedWithin after watch lo hi :=
    attachKeepsActiveScope shape.byteFrame distinct lo hi preserved.2.2.2.2.1
  have otherPath : ¬ Ancestor after watch child := by
    intro ancestor
    rcases shape.attached.ancestry.mp ancestor with same | path
    · exact distinct same
    · exact foreign ((ancestryFrame sameNodes).mpr path)
  refine ⟨activeAfter, otherPath, ?_⟩
  intro position valid begins ends
  let row := after.locations.entries[position].data
  have newAbsent : row.perms.get child = none := by
    cases chosen : row.perms.get child with
    | none => rfl
    | some state =>
      have pointIn := (shape.extent extent).1 point position valid begins ends state chosen
      exact False.elim (outside.elim (fun h => by omega) (fun h => by omega))
  have bound := shape.byteFrame.2.2 point position valid begins ends
  refine attachKeepsOutsideByte shape.attached ⟨writerNode, olderWriter⟩ watchMask nextMask point row
    bound ?_ newAbsent ?_ ?_
  · intro old stored
    obtain ⟨oldPos, oldValid, start, stop, same⟩ := stored
    have oldRight := preserved.2.2.2.2.2 point oldPos oldValid
      (UInt64.le_iff_toNat_le.mpr start) (UInt64.lt_iff_toNat_lt.mpr stop) outside rfl
    rw [← same]
    exact CopyHolderRights.rights_frame sameNodes _ watchMask writer oldRight
  · intro node atChild
    have same := Option.some.inj (atChild.symm.trans childAt)
    subst node
    unfold foreignCompatible TreeNode.defaultLocationState
    rw [childDefault]
    simp [LocationState.possible, Permission.isUnique]
  · intro index node distinct found
    obtain ⟨data, inOriginal, sameTag, permission⟩ := shape.olderNodes index node distinct found
    have inRead : read.nodeAt index = some data := by
      unfold BorrowTree.nodeAt
      rw [← sameNodes]
      exact inOriginal
    exact ⟨data, inRead, permission, by rw [← sameTag]; exact mask index data inOriginal⟩

/-- The shared reborrow retains every old node's identity, parent, and
exposure flag. A parent's children may acquire the new edge. -/
theorem sharedOlderNode {original read after : BorrowTree} {parent child : UniIndex}
    {tag : BorTag} {offset length : Size} {inside : DedupRangeMap LocationState}
    (shape : SharedChildFrame original read after parent child tag offset length inside)
    (index : UniIndex) (node : TreeNode) (present : original.nodeAt index = some node) :
    ∃ next, after.nodeAt index = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed := by
  have onRead : read.nodeAt index = some node := by rw [shape.readMetadata]; exact present
  have earlier : index ≠ child := by
    intro equal
    rw [equal,shape.attached.fresh] at onRead
    contradiction
  obtain ⟨next, stored, edge⟩ := shape.attached.oldEdges index node onRead
  obtain ⟨older, same, tagEq, _⟩ := shape.olderNodes index next earlier stored
  have identified := Option.some.inj (same.symm.trans present)
  subst older
  have visibility := shape.olderExposure index earlier
  rw [stored, present] at visibility
  exact ⟨next,stored,tagEq.symm,edge,Option.some.inj visibility⟩

/-- One exact read, attachment and release transports a return-slot
observation. The actor may be any admitted source-derived child. -/
structure SharedWatchTransfer (original final : BorrowTree) (parent recipient : UniIndex)
    (lower upper : UInt64) : Prop where
  key : ∀ key index, original.indexOfTag key = some index → final.indexOfTag key = some index
  node : ∀ index prior, original.nodeAt index = some prior →
    ∃ after, final.nodeAt index = some after ∧ after.tag = prior.tag ∧
      after.parent = prior.parent ∧ after.isExposed = prior.isExposed
  ancestry : ∀ old watch, (∃ prior, original.nodeAt old = some prior) →
    (Ancestor original watch old ↔ Ancestor final watch old)
  recipientForeign : ∀ watch, (∃ prior, original.nodeAt watch = some prior) →
    ¬ Ancestor original watch parent → ¬ Ancestor final watch recipient
  kept : ∀ (watch writer : UniIndex) (watchLo watchHi point : UInt64) (mask : ProtectedTags),
    (∃ prior, original.nodeAt watch = some prior) → (∃ prior, original.nodeAt writer = some prior) →
    ¬ Ancestor original watch parent →
    (point.toNat < lower.toNat ∨ upper.toNat ≤ point.toNat) →
    AccessedWithin original watch watchLo watchHi → AtByte original point mask writer →
    AccessedWithin final watch watchLo watchHi ∧ AtByte final point mask writer

theorem attachmentTransfer
    (tree after : BorrowTree) (parentTag tag : BorTag) (parent child root : UniIndex)
    (offset length : Size) (inside : DedupRangeMap LocationState) (forRead : ProtectedTags)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (actorNode childNode : TreeNode) (actorAt : tree.nodeAt parent = some actorNode)
    (childAt : after.nodeAt child = some childNode) (childDefault : childNode.defaultInitialPermission = .Frozen)
    (parentFound : tree.indexOfTag parentTag = some parent) (fresh : tree.indexOfTag tag = none)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (reader : OwnedOn (fun row => LocationAccessRights tree row forRead parent .Read)
      offset.bytes (offset.bytes+length.bytes) tree.locations)
    (shape : SharedChildFrame tree
      (tree.performNormalAccessRange parentTag offset length .Read forRead .VisitChildrenOfAccessed).tree
      after parent child tag offset length inside)
    (extent : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat) :
    SharedWatchTransfer tree after parent child offset.bytes (offset.bytes+length.bytes) := by
  let read := (tree.performNormalAccessRange parentTag offset length .Read forRead .VisitChildrenOfAccessed).tree
  have nodes : tree.nodes = read.nodes := (congrArg BorrowTree.nodes shape.readMetadata).symm
  have oldRead (index : UniIndex) (data : TreeNode) (stored : tree.nodeAt index = some data) :
      read.nodeAt index = some data := by
    unfold BorrowTree.nodeAt
    rw [← nodes]
    exact stored
  have different (index : UniIndex) (data : TreeNode) (stored : tree.nodeAt index = some data) : index ≠ child := by
    intro eq
    have contradict := oldRead index data stored
    rw [eq,shape.attached.fresh] at contradict
    contradiction
  constructor
  · intro key index stored
    have old : key ≠ tag := by intro eq; rw [eq,fresh] at stored; contradiction
    exact (shape.olderTags key old).trans stored
  · exact sharedOlderNode shape
  · rintro old watch ⟨data,stored⟩
    have same := SharedRelease.holder_ancestry (index := watch) shape.attached (different old data stored)
    exact (ancestryFrame nodes).trans ⟨same.2, fun walk => (same.1 walk).1⟩
  · rintro watch ⟨node,stored⟩ noOld path
    rcases shape.attached.ancestry.mp path with same | inherited
    · exact different watch node stored same
    · exact noOld ((ancestryFrame nodes).mpr inherited)
  · rintro watch writer lo hi point mask ⟨watchNode, watchAt⟩ ⟨writerNode, writerAt⟩ foreign outside active rights
    have kept := sharedReadKeepsWatch tree after parentTag tag parent child watch writer root offset length inside forRead mask mask
      coherent roots actorNode watchNode writerNode childNode actorAt watchAt writerAt childAt childDefault parentFound bounds
      reader shape extent foreign (fun _ _ _ => rfl) lo hi point outside active rights
    exact ⟨kept.1,kept.2.2⟩

theorem SharedWatchTransfer.trans {a b c : BorrowTree} {actor intermediate recipient : UniIndex}
    {lower upper : UInt64} (first : SharedWatchTransfer a b actor intermediate lower upper)
    (second : SharedWatchTransfer b c intermediate recipient lower upper) :
    SharedWatchTransfer a c actor recipient lower upper := by
  have retained (index : UniIndex) (present : ∃ node, a.nodeAt index = some node) :
      ∃ node, b.nodeAt index = some node := by
    obtain ⟨node,found⟩ := present
    obtain ⟨current,saved,_⟩ := first.node index node found
    exact ⟨current,saved⟩
  constructor
  · intro key index found
    exact second.key key index (first.key key index found)
  · intro index node found
    obtain ⟨mid,saved,tag,edge,visibility⟩ := first.node index node found
    obtain ⟨last,stored,tagFinal,edgeFinal,visibilityFinal⟩ := second.node index mid saved
    exact ⟨last,stored,tagFinal.trans tag,edgeFinal.trans edge,visibilityFinal.trans visibility⟩
  · intro old watch found
    exact (first.ancestry old watch found).trans (second.ancestry old watch (retained old found))
  · intro watch present foreign
    exact second.recipientForeign watch (retained watch present) (first.recipientForeign watch present foreign)
  · intro watch writer lo hi point mask watchPresent writerPresent foreign outside active right
    obtain ⟨midScope,midRight⟩ := first.kept watch writer lo hi point mask watchPresent writerPresent foreign outside active right
    exact second.kept watch writer lo hi point mask (retained watch watchPresent) (retained writer writerPresent)
      (first.recipientForeign watch watchPresent foreign) outside midScope midRight

#print axioms ancestryFrame
#print axioms sharedReadKeepsWatch
#print axioms sharedOlderNode
#print axioms attachmentTransfer
#print axioms SharedWatchTransfer.trans

end DuplicatePrefix.NonemptyReturnWatch

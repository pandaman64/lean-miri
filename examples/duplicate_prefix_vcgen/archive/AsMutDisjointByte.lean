import duplicate_prefix.AsMutActiveHolder
import duplicate_prefix.FrozenStageFrame
import duplicate_prefix.PositiveRetagResources

namespace DuplicatePrefix.AsMutDisjointByte

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open SourceDomain FrozenReborrowInputs FrozenStageFrame ArchiveForestProjection RetagReleaseFootprint
open GeneralRangeMapOrigins AsMutHolderScope NonemptyReturnWatch

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

abbrev reserved (tree : BorrowTree) (global : TreeBorrows.GlobalState) (inputTag : BorTag) (start length : Size) :=
  ExclusiveTwoPhaseRetag.reservationTree tree inputTag global.nextPointerTag start length global.protectedTags

abbrev rawTag (global : TreeBorrows.GlobalState) :=
  global.nextPointerTag.succ.getD global.nextPointerTag

abbrev mask (global : TreeBorrows.GlobalState) :=
  global.protectedTags.insert (rawTag global) .StrongProtector

abbrev installed (tree : BorrowTree) (global : TreeBorrows.GlobalState) (inputTag : BorTag) (start length : Size) :=
  ExclusiveTypedRetag.protectedFrozenTree (reserved tree global inputTag start length)
    global.protectedTags global.nextPointerTag (rawTag global) start length

abbrev firstRows (length : Size) := DedupRangeMap.new length ExclusiveTwoPhaseRetag.initial
abbrev secondRows (length : Size) := DedupRangeMap.new length ExclusiveTypedRetag.readState

/-- Seed the actual mutable reservation from the admitted byte loan and
the current key allocator. Dormant permissions outside the loan are allowed. -/
theorem reservationInputs
    {before : Miri.Interpreter.MachineHooks.State Miri.Memory.MiriMemoryKind DuplicatePrefix.Machine.RootUser} {length : UInt64}
    (storage : PreparedArguments.InitializedRegion before length)
    (tag : BorTag) (loan : ExclusiveRegion before length storage tag) (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (fits : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat) :
    StageData storage.entry.allocation.extra loan.tracker.global.protectedTags tag loan.tracker.global.nextPointerTag
      loan.source root storage.relativeStart (Size.ofBytes length) (firstRows (Size.ofBytes length)) false := by
  have span := RetagStageImage.uniform storage.relativeStart (Size.ofBytes length)
    storage.entry.allocation.extra.locations.size ExclusiveTwoPhaseRetag.initial false fits (.inl rfl)
  obtain ⟨node,found,_⟩ := loan.sourcePresent
  exact ⟨loan.coherent,loan.tagKnown,⟨node,found⟩,capacity.roots,capacity.freshKey,
    capacity.room,capacity.aligned,capacity.reuse,fits,(fun seg member => (span seg member).1),
    (fun seg member => (span seg member).2.1),
    RetagReleaseRights.region_owned before length storage tag loan fits,capacity.clean⟩

/-- The concrete choices made by both actual tree mutations, with the row
frame and selected keys needed to track an independent return carrier. -/
structure Stages (tree middle active : BorrowTree) (global : TreeBorrows.GlobalState) (inputTag : BorTag)
    (parent root intermediate raw : UniIndex) (start length : Size) : Prop where
  reservationKey : middle.indexOfTag global.nextPointerTag = some intermediate
  rawKey : active.indexOfTag (rawTag global) = some raw
  first : Applied tree
    (tree.performNormalAccessRange inputTag start length .Read global.protectedTags .VisitChildrenOfAccessed).tree
    middle inputTag global.nextPointerTag parent intermediate
    start length (firstRows length) false
  inner : StageData middle (mask global) global.nextPointerTag (rawTag global)
    intermediate root start length (secondRows length) true
  second : Applied middle
    (middle.performNormalAccessRange global.nextPointerTag start length
      .Read (mask global) .VisitChildrenOfAccessed).tree
    active global.nextPointerTag (rawTag global)
    intermediate raw start length (secondRows length) true
  release : RawHolderScope.ReleaseStage active (mask global) raw root start length
  absentFirst : global.protectedTags.contains global.nextPointerTag = false
  absentRaw : global.protectedTags.contains (rawTag global) = false

theorem stages
    (tree : BorrowTree) (global : TreeBorrows.GlobalState) (inputTag : BorTag)
    (parent root : UniIndex) (start length : Size)
    (source : StageData tree global.protectedTags inputTag global.nextPointerTag parent root start length (firstRows length) false)
    (ready : RetagInsertionCapacity.Ready tree) (space : tree.nodes.size+1 < 2^32)
    (age : ∀ index node, tree.nodeAt index = some node → node.tag.value.toNat < global.nextPointerTag.value.toNat)
    (protectors : ∀ old, global.protectedTags.contains old = true → old.value.toNat < global.nextPointerTag.value.toNat)
    (tagRoom : global.nextPointerTag.value.toNat+2 < 2^64) :
    ∃ intermediate raw, Stages tree (reserved tree global inputTag start length)
      (installed tree global inputTag start length) global inputTag parent root intermediate raw start length := by
  obtain ⟨firstAbsent, rawAbsent, inner, release⟩ := PositiveRetagResources.stageImages tree global inputTag parent root
    start length source ready space age protectors tagRoom
  have firstBounds := RetagStageImage.uniform start length tree.locations.size ExclusiveTwoPhaseRetag.initial false
    source.bounds (.inl rfl)
  obtain ⟨intermediate,middleKey,first⟩ := FrozenStageFrame.apply tree global.protectedTags inputTag global.nextPointerTag
    parent root start length (firstRows length) false source (fun seg member => (firstBounds seg member).2.2)
  have selected : (reserved tree global inputTag start length).indexOfTag global.nextPointerTag = some intermediate := middleKey
  have secondInputs := inner intermediate selected
  have secondBounds := RetagStageImage.uniform start length (reserved tree global inputTag start length).locations.size
    ExclusiveTypedRetag.readState true secondInputs.bounds (.inl rfl)
  obtain ⟨raw,rawKey,second⟩ := FrozenStageFrame.apply (reserved tree global inputTag start length)
    (mask global) global.nextPointerTag (rawTag global) intermediate root start length (secondRows length) true
    secondInputs.data (fun seg member => (secondBounds seg member).2.2)
  exact ⟨intermediate,raw,selected,rawKey,first,secondInputs.data,second,release raw rawKey,firstAbsent,rawAbsent⟩

abbrev released (tree : BorrowTree) (global : TreeBorrows.GlobalState) (inputTag : BorTag) (start length : Size) :=
  ((installed tree global inputTag start length).releaseProtector (rawTag global) (mask global)).tree

/-- The actual bb7 tree carries the original mutable slice's release
footprint, even when dormant rows for its tag existed outside the slice. -/
theorem Stages.activeHolder {tree middle active : BorrowTree} {global : TreeBorrows.GlobalState} {inputTag : BorTag}
    {parent root intermediate raw : UniIndex} {start length : Size}
    (stage : Stages tree middle active global inputTag parent root intermediate raw start length)
    (source : StageData tree global.protectedTags inputTag global.nextPointerTag parent root start length (firstRows length) false)
    (holder : TreeNode) (present : tree.nodeAt parent = some holder) (hidden : holder.isExposed = false)
    (scope : AccessedWithin tree parent start.bytes (start.bytes+length.bytes)) :
    let final := (active.releaseProtector (rawTag global) (mask global)).tree
    final.indexOfTag inputTag = some parent ∧
    (final.nodeAt parent).map TreeNode.isExposed = some false ∧
    final.indexOfTag (rawTag global) = some raw ∧
    BetweenTags final global.protectedTags parent raw ∧
    AccessedCopyHolderRights.Footprint final global.protectedTags raw parent start.bytes (start.bytes+length.bytes) ∧
    final.locations.size = tree.locations.size := by
  intro final
  have firstNodes := congrArg BorrowTree.nodes stage.first.readShape
  have secondNodes := congrArg BorrowTree.nodes stage.second.readShape
  have firstPath := BetweenTags.retag (BetweenTags.self tree global.protectedTags parent) firstNodes
    stage.first.attachment stage.first.oldNodes global.nextPointerTag stage.absentFirst stage.first.newTag
  have secondPath := BetweenTags.retag firstPath secondNodes stage.second.attachment stage.second.oldNodes
    (rawTag global) stage.absentRaw stage.second.newTag
  have oldFirst := stage.first.keepsOriginalActive source holder present scope
  obtain ⟨middleNode, middleAt, _, _⟩ := stage.first.keepsNode parent holder present
  have oldSecond := stage.second.keepsOriginalActive stage.inner middleNode middleAt oldFirst
  obtain ⟨activeNode, activeAt, _, _⟩ := stage.second.keepsNode parent middleNode middleAt
  have restored : (mask global).remove (rawTag global) = global.protectedTags :=
    RawHolderScope.fresh_mask_restored global.protectedTags (rawTag global) .StrongProtector stage.absentRaw
  have stable := AsMutHolderScope.finishActive active (mask global) (rawTag global) raw parent root start length
    stage.rawKey stage.release activeNode activeAt oldSecond (by rw [restored]; exact secondPath)
  have differentFirst : inputTag ≠ global.nextPointerTag := by
    intro eq
    have stale := source.fresh
    rw [← eq, source.parentFound] at stale
    contradiction
  have kept : middle.indexOfTag inputTag = some parent :=
    (stage.first.keys inputTag differentFirst).trans source.parentFound
  have differentSecond : inputTag ≠ rawTag global := by
    intro eq
    have stale := stage.inner.fresh
    rw [← eq, kept] at stale
    contradiction
  have finalKey : active.indexOfTag inputTag = some parent := (stage.second.keys inputTag differentSecond).trans kept
  have middleFlag : middleNode.isExposed = false := by
    have keepFlag := stage.first.exposure parent holder present
    rw [middleAt,Option.map_some,hidden] at keepFlag
    exact Option.some.inj keepFlag
  have activeFlag : (active.nodeAt parent).map TreeNode.isExposed = some false :=
    (stage.second.exposure parent middleNode middleAt).trans (congrArg some middleFlag)
  have shape : final = {active with locations := final.locations} := stable.2.1
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [shape]; exact finalKey
  · rw [shape]; exact activeFlag
  · rw [shape]; exact stage.rawKey
  · have path := stable.2.2.2.2.1
    rw [restored] at path
    exact path
  · have footprint := stable.2.2.2.2.2
    rw [restored] at footprint
    exact footprint

  · exact stable.2.2.2.1.trans (stage.second.frame.1.trans
      (stage.second.size.trans (stage.first.frame.1.trans stage.first.size)))

/-- The two mutable retags and actual helper release preserve an
independent output carrier at a byte outside the borrowed slice. -/
theorem Stages.output {tree middle active : BorrowTree} {global : TreeBorrows.GlobalState} {inputTag : BorTag}
    {parent root intermediate raw : UniIndex} {start length : Size}
    (stage : Stages tree middle active global inputTag parent root intermediate raw start length)
    (source : StageData tree global.protectedTags inputTag global.nextPointerTag parent root start length (firstRows length) false)
    (watch writer : UniIndex) (watchNode writerNode : TreeNode)
    (watchAt : tree.nodeAt watch = some watchNode) (writerAt : tree.nodeAt writer = some writerNode)
    (foreign : ¬ Ancestor tree watch parent)
    (proofTags : ProtectedTags) (lo hi : UInt64) (scope : AccessedWithin tree watch lo hi)
    (observes : UInt64 → Prop)
    (rights : RangeModifyLaw.EachByte tree.locations (fun point row =>
      (point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) →
      observes point → LocationRights tree row proofTags writer)) :
    let final := (active.releaseProtector (rawTag global) (mask global)).tree
    AccessedWithin final watch lo hi ∧ ¬ Ancestor final watch raw ∧
    (∀ old, old ≠ global.nextPointerTag → old ≠ rawTag global → final.indexOfTag old = tree.indexOfTag old) ∧
    (∃ node, final.nodeAt watch = some node ∧ node.tag = watchNode.tag ∧ node.parent = watchNode.parent ∧ node.isExposed = watchNode.isExposed) ∧
    (∃ node, final.nodeAt writer = some node ∧ node.tag = writerNode.tag ∧ node.parent = writerNode.parent ∧ node.isExposed = writerNode.isExposed) ∧
    RangeModifyLaw.EachByte final.locations (fun point row =>
      (point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) →
      observes point → LocationRights final row proofTags writer) := by
  intro final
  have first := stage.first.keepsOutput source watchNode writerNode watchAt writerAt foreign proofTags lo hi scope observes rights
  obtain ⟨w1,w1At,w1Tag,w1Parent⟩ := stage.first.keepsNode watch watchNode watchAt
  obtain ⟨r1,r1At,r1Tag,r1Parent⟩ := stage.first.keepsNode writer writerNode writerAt
  have second := stage.second.keepsOutput stage.inner w1 r1 w1At r1At first.2.1 proofTags lo hi first.1 observes first.2.2
  obtain ⟨w2,w2At,w2Tag,w2Parent⟩ := stage.second.keepsNode watch w1 w1At
  obtain ⟨r2,r2At,r2Tag,r2Parent⟩ := stage.second.keepsNode writer r1 r1At
  have retired := ActiveReleaseOutside.keepsWatch active (mask global) (rawTag global) raw root watch start length
    stage.rawKey stage.release w2 w2At lo hi (.inl second.2.1) second.1
    (fun point row => observes point → LocationRights active row proofTags writer) second.2.2
  have shape : final = {active with locations := final.locations} := retired.2.1
  have nodeTable := congrArg BorrowTree.nodes shape
  change final.nodes = active.nodes at nodeTable
  have watchFlag : w2.isExposed = watchNode.isExposed := by
    have first := stage.first.exposure watch watchNode watchAt
    have second := stage.second.exposure watch w1 w1At
    rw [w1At,Option.map_some] at first
    rw [w2At,Option.map_some] at second
    exact (Option.some.inj second).trans (Option.some.inj first)
  have writerFlag : r2.isExposed = writerNode.isExposed := by
    have first := stage.first.exposure writer writerNode writerAt
    have second := stage.second.exposure writer r1 r1At
    rw [r1At,Option.map_some] at first
    rw [r2At,Option.map_some] at second
    exact (Option.some.inj second).trans (Option.some.inj first)
  refine ⟨retired.2.2.1, fun path => second.2.1 (ancestor_frame nodeTable path), ?_,
    ⟨w2,?_,w2Tag.trans w1Tag,w2Parent.trans w1Parent,watchFlag⟩, ⟨r2,?_,r2Tag.trans r1Tag,r2Parent.trans r1Parent,writerFlag⟩,?_⟩
  · intro old firstNot secondNot
    rw [shape]
    exact (stage.second.keys old secondNot).trans (stage.first.keys old firstNot)
  · change final.nodeAt watch = some w2
    rw [shape]
    exact w2At
  · change final.nodeAt writer = some r2
    rw [shape]
    exact r2At
  · intro point pos valid lower upper away seen
    exact CopyHolderRights.rights_frame nodeTable.symm _ proofTags writer (retired.2.2.2 point pos valid lower upper away seen)

end DuplicatePrefix.AsMutDisjointByte

#print axioms DuplicatePrefix.AsMutDisjointByte.stages
#print axioms DuplicatePrefix.AsMutDisjointByte.Stages.activeHolder
#print axioms DuplicatePrefix.AsMutDisjointByte.Stages.output

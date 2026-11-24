import duplicate_prefix.FrozenReborrowInputs
import duplicate_prefix.RetagCapacityFrame

namespace DuplicatePrefix.RetagSuccessorCapacity
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification.MutableRetagFootprint Miri.Verification.MutableTypedRetag
open ArchiveForestProjection FrozenReborrowInputs SourceDomain RetagInsertionCapacity
open GeneralRangeMapOrigins RetagReleaseFootprint RetagFrozenChild
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The real associated read and child attach preserve sufficient insertion
resources for the next fresh tag. Existing keys are tied to occupied node tags
and the fresh allocator generation must strictly increase. -/
theorem next
    (tree : BorrowTree) (tags : ProtectedTags) (parentTag newTag following : BorTag)
    (parent root : UniIndex) (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (stage : Stage tree tags parentTag newTag parent root offset length inside held)
    (ready : Ready tree) (space : tree.nodes.size + 1 < 2^32)
    (ages : ∀ i data, tree.nodeAt i = some data → data.tag.value.toNat < newTag.value.toNat)
    (successor : newTag.value.toNat < following.value.toNat)
    (insideBounds : ∀ seg ∈ inside.iterAll.toList, seg.range.stop.toNat ≤ length.bytes.toNat) :
    let read := tree.performNormalAccessRange parentTag offset length .Read tags .VisitChildrenOfAccessed
    let result := read.tree.newChild offset (.concrete parentTag) newTag inside (.ReservedFrz false) held
    Ready result.tree ∧
    ∀ selected, result.tree.indexOfTag newTag = some selected →
      CurrentTwoPhaseStructural.InsertionCapacity result.tree selected root following := by
  intro read result
  obtain ⟨parentNode,present⟩ := stage.parentPresent
  have currentFresh : ∀ i data, tree.nodeAt i = some data → data.tag ≠ newTag := by
    intro i data stored equal
    have strict := ages i data stored
    rw [equal] at strict
    exact (Nat.lt_irrefl _ strict)
  have capacity := RetagInsertionCapacity.derive tree parent root newTag stage.coherent stage.roots parentNode
    present ready currentFresh
  obtain ⟨graph,rank⟩ := capacity.ranked
  let original : CopyHolderRights.Footprint tree tags parent parent offset.bytes (offset.bytes+length.bytes) :=
    ⟨stage.owners,stage.owners,stage.scope,stage.vacant⟩
  obtain ⟨readDone, readShape, readCoherent, readSize, readFootprint⟩ :=
    CopyHolderRights.accessRange_retains_holder tree tags parentTag parent parent root .Read offset length
      offset.bytes (offset.bytes+length.bytes) stage.coherent parentNode present stage.roots stage.parentFound (.self parent)
      (fun _ _ _ same away => False.elim (away same)) stage.bounds (Nat.le_refl _) (Nat.le_refl _) original
  change read.tree = {tree with locations := read.tree.locations} at readShape
  change read.tree.locations.size = tree.locations.size at readSize
  have nodes := congrArg BorrowTree.nodes readShape
  change read.tree.nodes = tree.nodes at nodes
  have table := congrArg BorrowTree.tagMapping readShape
  change read.tree.tagMapping = tree.tagMapping at table
  have readPresent : read.tree.nodeAt parent = some parentNode := by
    simpa only [BorrowTree.nodeAt,nodes] using present
  have readParent : read.tree.indexOfTag parentTag = some parent := by
    simpa only [BorrowTree.indexOfTag,table] using stage.parentFound
  have readSpace : read.tree.nodes.size + 1 < 2^32 := by rwa [nodes]
  have readFollowing : ∀ i data, read.tree.nodeAt i = some data → data.tag.value.toNat < newTag.value.toNat := by
    intro i data stored
    exact ages i data (by simpa only [BorrowTree.nodeAt,nodes] using stored)
  have readFresh : ∀ i data, read.tree.nodeAt i = some data → data.tag ≠ newTag := by
    intro i data stored equal
    have strict := readFollowing i data stored
    rw [equal] at strict
    exact Nat.lt_irrefl _ strict
  have readReady := RetagCapacityFrame.afterRangeUpdate tree read.tree ready table nodes readFootprint.vacant
  have readCapacity := RetagInsertionCapacity.derive read.tree parent root newTag readCoherent
    (by rw [readShape]; exact stage.roots) parentNode readPresent readReady readFresh
  obtain ⟨readGraph,readRank⟩ := readCapacity.ranked
  have readSpan : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ read.tree.locations.size.bytes.toNat := by
    simpa only [readSize] using stage.span
  obtain ⟨mapping,child,mappingEq,empty,done,_⟩ :=
    newChild_frozen_frame_with_mode read.tree offset parentTag newTag parent parentNode inside held
      readParent readPresent readCapacity.freshKey readCapacity.room readCapacity.aligned readCapacity.reuse
      readCoherent.ranges readGraph readRank readCapacity.clean readSpan stage.policy
  obtain ⟨_, _, size, coherent, roots, exactChild, childKey, actualNode, footprint, _⟩ :=
    coherent_frozen_reborrow_with_footprint tree tags parentTag newTag parent root offset length inside held
      stage.coherent parentNode present stage.roots stage.parentFound graph rank capacity.freshKey currentFresh
      capacity.room capacity.aligned capacity.reuse capacity.clean stage.span stage.policy stage.bounds stage.owners
  obtain ⟨node,stored,_,_⟩ := actualNode
  have postReady := RetagCapacityFrame.preserves read.tree offset parentTag newTag parent child parentNode mapping inside
    held readReady readSpace readCapacity.freshKey mappingEq readParent readPresent empty done (footprint insideBounds).2
  refine ⟨postReady,?_⟩
  intro selected key
  have same : selected = exactChild := Option.some.inj (key.symm.trans childKey)
  subst selected
  apply RetagInsertionCapacity.derive result.tree exactChild root following coherent roots node stored postReady
  intro index data found equal
  have distinct : data.tag.value.toNat < following.value.toNat := by
    have metadata := newChild_nodeMetadata read.tree offset parentTag newTag parent child mapping inside
      (.ReservedFrz false) held mappingEq readParent parentNode readPresent empty done index
    change nodeMetadata result.tree index = _ at metadata
    unfold nodeMetadata at metadata
    rw [found] at metadata
    by_cases new : index = child
    · rw [ite_eq_left new] at metadata
      have chosen := congrArg Prod.fst (Option.some.inj metadata)
      change data.tag = newTag at chosen
      rw [chosen]
      exact successor
    · rw [ite_eq_right new] at metadata
      cases old : read.tree.nodeAt index with
      | none => simp [old] at metadata
      | some prior =>
        rw [old] at metadata
        have sameTag := congrArg Prod.fst (Option.some.inj metadata)
        change data.tag = prior.tag at sameTag
        rw [sameTag]
        exact Nat.lt_trans (readFollowing index prior old) successor
  rw [equal] at distinct
  exact Nat.lt_irrefl _ distinct

theorem allocated_tag_value (old after : TreeBorrows.GlobalState)
    (allocated : old.newPointerTag = .ok (after,old.nextPointerTag))
    (budget : old.nextPointerTag.value.toNat + 2 < 2 ^ 64) :
    after.nextPointerTag.value.toNat = old.nextPointerTag.value.toNat + 1 := by
  have notMax : old.nextPointerTag.value ≠ 18446744073709551615 := by
    intro equal
    rw [equal] at budget
    simp at budget
  have sum : (old.nextPointerTag.value + 1).toNat = old.nextPointerTag.value.toNat + 1 := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using (show old.nextPointerTag.value.toNat + 1 < 2^64 by omega))]
  have notZero : old.nextPointerTag.value + 1 ≠ 0 := by
    intro equal
    rw [equal] at sum
    simp at sum
  unfold TreeBorrows.GlobalState.newPointerTag BorTag.succ BorTag.ofUInt64 at allocated
  simp [notMax, notZero] at allocated
  have advanced := congrArg (fun state : TreeBorrows.GlobalState => state.nextPointerTag.value.toNat) allocated
  rw [← advanced]
  exact sum

theorem successor_tag_value (tag : BorTag) (budget : tag.value.toNat+2 < 2^64) :
    (tag.succ.getD tag).value.toNat = tag.value.toNat+1 := by
  have notMax : tag.value ≠ 18446744073709551615 := by
    intro equal
    rw [equal] at budget
    simp at budget
  have sum : (tag.value+1).toNat = tag.value.toNat+1 := by
    simp [UInt64.toNat_add,Nat.mod_eq_of_lt (by simpa using (show tag.value.toNat+1 < 2^64 by omega))]
  have notZero : tag.value+1 ≠ 0 := by
    intro equal
    rw [equal] at sum
    simp at sum
  simp only [BorTag.succ,BorTag.ofUInt64,notMax,ite_false,notZero,dite_false,Option.getD_some]
  exact sum

theorem successor_unprotected (global : TreeBorrows.GlobalState)
    (budget : global.nextPointerTag.value.toNat+2 < 2^64)
    (order : ∀ old, global.protectedTags.contains old = true → old.value.toNat < global.nextPointerTag.value.toNat) :
    global.protectedTags.contains (global.nextPointerTag.succ.getD global.nextPointerTag) = false := by
  cases active : global.protectedTags.contains (global.nextPointerTag.succ.getD global.nextPointerTag)
  · rfl
  · have less := order _ active
    rw [successor_tag_value _ budget] at less
    omega

theorem afterReservation
    (tree : BorrowTree) (global : TreeBorrows.GlobalState) (parentTag : BorTag)
    (parent root : UniIndex) (offset length : Size)
    (stage : Stage tree global.protectedTags parentTag global.nextPointerTag parent root offset length
      (DedupRangeMap.new length ExclusiveTwoPhaseRetag.initial) false)
    (ready : Ready tree) (space : tree.nodes.size + 1 < 2^32)
    (ages : ∀ i node, tree.nodeAt i = some node → node.tag.value.toNat < global.nextPointerTag.value.toNat)
    (budget : global.nextPointerTag.value.toNat + 2 < 2 ^ 64) :
    ∀ (after : TreeBorrows.GlobalState) (selected : UniIndex),
      let advanced := ExclusiveTwoPhaseRetag.reservationTree tree parentTag global.nextPointerTag offset length global.protectedTags
      global.newPointerTag = .ok (after,global.nextPointerTag) →
      advanced.indexOfTag global.nextPointerTag = some selected →
      after.nextPointerTag.value ≠ 18446744073709551615 ∧
        CurrentTwoPhaseStructural.InsertionCapacity advanced selected root after.nextPointerTag := by
  intro after selected advanced allocated key
  have age := allocated_tag_value global after allocated budget
  have following : global.nextPointerTag.value.toNat < after.nextPointerTag.value.toNat := by omega
  have fits : after.nextPointerTag.value ≠ 18446744073709551615 := by
    intro equal
    rw [equal] at age
    change 18446744073709551615 = global.nextPointerTag.value.toNat + 1 at age
    omega
  have span : ∀ seg ∈ (DedupRangeMap.new length ExclusiveTwoPhaseRetag.initial).iterAll.toList,
        seg.range.stop.toNat ≤ length.bytes.toNat := by
    intro seg member
    by_cases empty : length.bytes = 0
    · simp [DedupRangeMap.new,DedupRangeMap.iterAll,empty] at member
    · simp [DedupRangeMap.new,DedupRangeMap.iterAll,beq_iff_eq,empty] at member
      subst seg
      exact Nat.le_refl _
  exact ⟨fits,(next tree global.protectedTags parentTag global.nextPointerTag after.nextPointerTag
    parent root offset length (DedupRangeMap.new length ExclusiveTwoPhaseRetag.initial) false
    stage ready space ages following span).2 selected key⟩

end DuplicatePrefix.RetagSuccessorCapacity

#print axioms DuplicatePrefix.RetagSuccessorCapacity.next

#print axioms DuplicatePrefix.RetagSuccessorCapacity.afterReservation

#print axioms DuplicatePrefix.RetagSuccessorCapacity.successor_unprotected

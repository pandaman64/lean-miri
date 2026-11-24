import duplicate_prefix.RetagInsertionCapacity
import duplicate_prefix.RetagGraphFrame

namespace DuplicatePrefix.RetagCapacityFrame
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree.ZeroProtection Miri.Verification.MutableRetagFootprint
open ArchiveForestProjection RetagInsertionCapacity
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem afterRangeUpdate (tree next : BorrowTree)
    (ready : Ready tree) (keys : next.tagMapping = tree.tagMapping) (nodes : next.nodes = tree.nodes)
    (clean : ∀ index, next.nodeAt index = none → ∀ position (valid : position < next.locations.entries.size),
        next.locations.entries[position].data.perms.get index = none) : Ready next := by
  have slots : next.nodeAt = tree.nodeAt := by
    funext index
    simp [BorrowTree.nodeAt,nodes]
  refine ⟨?_,?_,?_,?_,?_,clean⟩
  · simpa only [keys,slots] using ready.keys
  · simpa only [keys,nodes,slots] using ready.free
  · rw [keys]
    exact ready.freeDistinct
  · rw [keys,nodes]
    exact ready.balanced
  · rw [nodes]
    exact ready.headroom

/-- The actual frozen child insertion preserves the key-table invariant whether
the allocated index is appended or recycled. -/
theorem preserves (tree : BorrowTree) (offset : Size) (parentTag tag : BorTag)
    (parent child : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inside : DedupRangeMap LocationState) (held : Bool)
    (ready : Ready tree) (space : tree.nodes.size + 1 < 2^32)
    (fresh : tree.tagMapping.get tag = none)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentKey : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).outcome = .ok ())
    (clean : let after := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
      ∀ index, after.nodeAt index = none → ∀ position (valid : position < after.locations.entries.size),
        after.locations.entries[position].data.perms.get index = none) :
    Ready (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree := by
  let defaultSifa : IdempotentForeignAccess := if held then .None else .Read
  let after := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
  let install := initialChildNode tag parent (.ReservedFrz false) defaultSifa
  have exactKeys : after.tagMapping = mapping :=
    newChild_keyMap tree offset (.concrete parentTag) tag inside (.ReservedFrz false) held mapping child mapped
  have graph := newChild_graph_initial tree offset parentTag tag parent child mapping inside
    (.ReservedFrz false) held defaultSifa rfl rfl (by cases held <;> rfl)
    mapped parentKey parentNode present vacant complete
  have exactSize : after.nodes.size = (Append.attachedNodes tree.nodes child parent parentNode install).size :=
    congrArg (fun x => x.2.1) graph
  have distinct : parent ≠ child := by
    intro same
    rw [same,vacant] at present
    contradiction
  have parentStill : (tree.nodes.insert child install).get parent = some parentNode :=
    (Sparse.get_other tree.nodes child parent install distinct).trans present
  have sizeAfter : after.nodes.size = (tree.nodes.insert child install).size := by
    rw [exactSize]
    exact insert_existing_size _ _ _ _ parentStill
  have mappedAfter : tree.tagMapping.insert tag = .Inserted after.tagMapping child := by rw [exactKeys]; exact mapped
  have metadata := newChild_nodeMetadata tree offset parentTag tag parent child mapping inside
    (.ReservedFrz false) held mapped parentKey parentNode present vacant complete
  have oldNodes (index : UniIndex) (node : TreeNode) (before : tree.nodeAt index = some node) :
      ∃ retained, after.nodeAt index = some retained ∧ retained.tag = node.tag := by
    have other : index ≠ child := by
      intro same
      rw [same,vacant] at before
      contradiction
    have same : nodeMetadata after index = nodeMetadata tree index := by
      simpa only [ite_eq_right other] using metadata index
    unfold nodeMetadata at same
    rw [before] at same
    cases found : after.nodeAt index with
    | none => rw [found] at same; cases same
    | some retained =>
      rw [found] at same
      exact ⟨retained, rfl, congrArg Prod.fst (Option.some.inj same)⟩
  have newNode : ∃ node, after.nodeAt child = some node ∧ node.tag = tag := by
    have installed : nodeMetadata after child = some (tag,some parent,.ReservedFrz false) := by
      simpa only [ite_true] using metadata child
    unfold nodeMetadata at installed
    cases found : after.nodeAt child with
    | none => rw [found] at installed; cases installed
    | some node =>
      rw [found] at installed
      exact ⟨node,rfl,congrArg Prod.fst (Option.some.inj installed)⟩
  have reserved (index : UniIndex) (other : index ≠ child) (empty : tree.nodeAt index = none) :
      after.nodeAt index = none := by
    have same : nodeMetadata after index = none := by
      change nodeMetadata (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree index = none
      rw [metadata, ite_eq_right other]
      simp [nodeMetadata, empty]
    unfold nodeMetadata at same
    cases found : after.nodeAt index with
    | none => rfl
    | some node => rw [found] at same; cases same
  cases free : tree.tagMapping.deassigned.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp free
    obtain ⟨_,_, selected⟩ := inserted_append tree.tagMapping tag mapping child empty fresh mapped
    have align : tree.tagMapping.mapping.size = tree.nodes.size := by simpa [empty] using ready.balanced
    have atEnd : child.toNat = tree.nodes.data.size := selected.trans align
    have size : after.nodes.size = tree.nodes.size + 1 := sizeAfter.trans (Append.append_size _ _ _ atEnd)
    exact (preserves_append tree after tag child ready space empty fresh mappedAfter size oldNodes newNode clean).1
  | some index =>
    obtain ⟨_,unavailable | reused⟩ := inserted_table tree.tagMapping mapping tag child fresh mapped
    · rw [free] at unavailable
      have impossible : some index = none := unavailable.1
      cases impossible
    have reusedIndex : index = child := Option.some.inj (free.symm.trans reused.1)
    subst index
    have bounded := (ready.free child (Array.mem_of_back? free)).1
    have size : after.nodes.size = tree.nodes.size := by
      rw [sizeAfter,Reuse.bounded_size _ _ _ bounded]
    exact preserves_reuse tree after tag child ready free fresh mappedAfter size oldNodes newNode reserved clean

end DuplicatePrefix.RetagCapacityFrame

#print axioms DuplicatePrefix.RetagCapacityFrame.afterRangeUpdate
#print axioms DuplicatePrefix.RetagCapacityFrame.preserves

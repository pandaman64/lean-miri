import duplicate_prefix.EmptySharedTree
import duplicate_prefix.RetagInsertionCapacity
import duplicate_prefix.RetagGraphFrame

namespace DuplicatePrefix.EmptySharedCapacity
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree.ZeroProtection Miri.Verification.MutableRetagFootprint
open ArchiveForestProjection RetagInsertionCapacity
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual shared child insertion preserves the key-table invariant whether
the allocated index is appended or recycled. -/
theorem preserves (tree : BorrowTree) (offset : Size) (parentTag tag : BorTag)
    (parent child : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (inside : DedupRangeMap LocationState) (held : Bool)
    (ready : Ready tree) (space : tree.nodes.size + 1 < 2^32)
    (fresh : tree.tagMapping.get tag = none)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentKey : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).outcome = .ok ())
    (clean : let after := (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree
      ∀ index, after.nodeAt index = none → ∀ position (valid : position < after.locations.entries.size),
        after.locations.entries[position].data.perms.get index = none) :
    Ready (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree := by
  let defaultSifa : IdempotentForeignAccess := .Read
  let after := (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree
  let install := initialChildNode tag parent .Frozen defaultSifa
  have exactKeys : after.tagMapping = mapping :=
    newChild_keyMap tree offset (.concrete parentTag) tag inside .Frozen held mapping child mapped
  have graph := newChild_graph_initial tree offset parentTag tag parent child mapping inside
    .Frozen held defaultSifa rfl rfl rfl
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
    .Frozen held mapped parentKey parentNode present vacant complete
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
    have installed : nodeMetadata after child = some (tag,some parent,.Frozen) := by
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
      change nodeMetadata (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree index = none
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

/-- A zero-width insertion preserves an unmaterialized old node at every row. -/
theorem preserveAbsentRow (initial : DedupRangeMap LocationTree) (after : BorrowTree)
    (child index : UniIndex) (different : index ≠ child)
    (framed : RetagLocationFrame.FramedAt (fun _ _ => False) initial child after)
    (before : ∀ position (valid : position < initial.entries.size), initial.entries[position].data.perms.get index = none)
    (position : Nat) (valid : position < after.locations.entries.size) :
    after.locations.entries[position].data.perms.get index = none := by
  have formed : after.locations.WellFormed := framed.2.1
  have nonempty : after.locations.entries.size ≠ 0 := by omega
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at formed
  let part := after.locations.entries[position]
  obtain ⟨⟨prior, ⟨priorPosition, bound, _, _, aligned⟩, oldRows⟩, _⟩ :=
    framed.2.2 part.range.start position valid (UInt64.le_refl _) (formed.2.1 position valid)
  have unchanged : storedPermission part.data index = storedPermission prior index := oldRows index different
  have oldMissing := before priorPosition bound
  rw [← aligned] at unchanged
  simp only [storedPermission, oldMissing, Option.map_none] at unchanged
  cases found : part.data.perms.get index with
  | none => rfl
  | some actual => simp [found] at unchanged

/-- The actual empty child keeps all previously vacant rows unmaterialized. -/
theorem preserveVacancy (tree : BorrowTree) (offset : Size) (parentTag tag : BorTag)
    (parent child : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag) (held : Bool)
    (ready : Ready tree)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentKey : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (complete : (tree.newChild offset (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).outcome = .ok ())
    (framed : RetagLocationFrame.FramedAt (fun _ _ => False) tree.locations child
      (tree.newChild offset (.concrete parentTag) tag
       (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree) :
    let after := (tree.newChild offset (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree
    ∀ index, after.nodeAt index = none → ∀ position (valid : position < after.locations.entries.size),
        after.locations.entries[position].data.perms.get index = none := by
  let inside := DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState
  let after := (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree
  have metadata := newChild_nodeMetadata tree offset parentTag tag parent child mapping inside .Frozen held
    mapped parentKey parentNode present vacant complete
  change ∀ index, after.nodeAt index = none → ∀ position (valid : position < after.locations.entries.size),
      after.locations.entries[position].data.perms.get index = none
  intro index missing position valid
  by_cases eq : index = child
  · subst index
    exact EmptySharedTree.childUnmaterialized tree.locations child after framed position valid
  have before : tree.nodeAt index = none := by
    have same : nodeMetadata after index = nodeMetadata tree index := by
      simpa only [ite_eq_right eq] using metadata index
    unfold nodeMetadata at same
    rw [missing] at same
    cases other : tree.nodeAt index with
    | none => rfl
    | some previous => rw [other] at same; cases same
  exact preserveAbsentRow tree.locations after child index eq framed (ready.rowVacant index before) position valid

end DuplicatePrefix.EmptySharedCapacity

#print axioms DuplicatePrefix.EmptySharedCapacity.preserves

#print axioms DuplicatePrefix.EmptySharedCapacity.preserveVacancy

#print axioms DuplicatePrefix.EmptySharedCapacity.preserveAbsentRow

import duplicate_prefix.CurrentTwoPhaseStructural
import duplicate_prefix.TightParentDepth

namespace DuplicatePrefix.RetagInsertionCapacity
open Miri.Memory Miri.TreeBorrows
open SourceDomain CurrentTwoPhaseStructural

/-- Representation invariant for the occupied key table and its reusable slots.
The next insertion may pop a vacant slot or extend the node table. -/
structure Ready (tree : BorrowTree) : Prop where
  keys : ∀ key ∈ tree.tagMapping.mapping,
    ∃ node, tree.nodeAt key.2 = some node ∧ node.tag = key.1
  free : ∀ index ∈ tree.tagMapping.deassigned,
    index.toNat < tree.nodes.size ∧ tree.nodeAt index = none
  freeDistinct : tree.tagMapping.deassigned.toList.Nodup
  balanced : tree.tagMapping.mapping.size + tree.tagMapping.deassigned.size = tree.nodes.size
  headroom : tree.nodes.size < 2 ^ 32
  rowVacant : ∀ index, tree.nodeAt index = none →
    ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none

theorem derive (tree : BorrowTree) (parent root : UniIndex) (tag : BorTag)
    (forest : CoherentForest tree) (rooted : tree.roots = #[root])
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (ready : Ready tree)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag) :
    InsertionCapacity tree parent root tag := by
  obtain ⟨depth, bounded, smaller⟩ := forest.parentDepth
  let certificate : BorrowTree.ZeroProtection.ParentDepth tree.nodes :=
    ⟨depth, bounded, fun index node found previous edge => by
      obtain ⟨old, present⟩ := forest.parentPresent index node previous found edge
      exact ⟨old,present,smaller index node previous found edge⟩⟩
  obtain ⟨tight, below⟩ := BorrowTree.ZeroProtection.ParentDepth.tight tree.nodes certificate
  have aligned (empty : tree.tagMapping.deassigned.back? = none) :
      tree.tagMapping.mapping.size = tree.nodes.size := by
    have emptySlots := Array.back?_eq_none_iff.mp empty
    simpa [emptySlots] using ready.balanced
  refine ⟨rooted, ⟨tight,below parent parentNode present⟩, ?_, fresh, ?_, aligned, ?_, ready.rowVacant⟩
  · unfold BorrowTree.indexOfTag UniKeyMap.get
    have missing : tree.tagMapping.mapping.find? (fun entry => entry.1 == tag) = none := by
      apply Array.find?_eq_none.mpr
      intro key member matchTag
      obtain ⟨node, atKey, keyTag⟩ := ready.keys key member
      exact fresh key.2 node atKey (keyTag.trans (beq_iff_eq.mp matchTag))
    rw [missing]
    rfl
  · intro noFree
    rw [aligned noFree]
    have room := ready.headroom
    omega
  · intro index reused
    exact ready.free index (Array.mem_of_back? reused)

theorem inserted_table (table result : UniKeyMap BorTag) (tag : BorTag) (index : UniIndex)
    (fresh : table.get tag = none)
    (inserted : table.insert tag = .Inserted result index) :
    result.mapping = table.mapping.push (tag,index) ∧
      (table.deassigned.back? = none ∧ result.deassigned = #[] ∨
        table.deassigned.back? = some index ∧ result.deassigned = table.deassigned.pop) := by
  have noKey : table.mapping.find? (fun pair => pair.1 == tag) = none := by
    unfold UniKeyMap.get at fresh
    cases found : table.mapping.find? (fun pair => pair.1 == tag) with
    | none => rfl
    | some pair => simp [found] at fresh
  have unchanged : (table.mapping.filter fun pair => pair.1 != tag) = table.mapping := by
    apply Array.filter_eq_self.mpr
    intro pair member
    have different := Array.find?_eq_none.mp noKey pair member
    simp [bne,different]
  unfold UniKeyMap.insert at inserted
  cases back : table.deassigned.back? with
  | none =>
    cases selected : UniIndex.ofNat? table.mapping.size with
    | none => simp [back,selected,Id.run,pure] at inserted
    | some newIndex =>
      simp [back,selected,fresh,unchanged,Id.run,bind,pure] at inserted
      obtain ⟨rfl,rfl⟩ := inserted
      exact ⟨rfl,Or.inl ⟨rfl,Array.back?_eq_none_iff.mp back⟩⟩
  | some reusable =>
    simp [back,fresh,unchanged,Id.run,bind,pure] at inserted
    obtain ⟨rfl,rfl⟩ := inserted
    exact ⟨rfl,Or.inr ⟨rfl,rfl⟩⟩

theorem preserves_append (tree next : BorrowTree) (tag : BorTag) (child : UniIndex)
    (ready : Ready tree) (space : tree.nodes.size + 1 < 2 ^ 32)
    (noFree : tree.tagMapping.deassigned = #[]) (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted next.tagMapping child)
    (size : next.nodes.size = tree.nodes.size + 1)
    (oldNodes : ∀ index node, tree.nodeAt index = some node →
      ∃ retained, next.nodeAt index = some retained ∧ retained.tag = node.tag)
    (newNode : ∃ installed, next.nodeAt child = some installed ∧ installed.tag = tag)
    (vacant : ∀ index, next.nodeAt index = none →
      ∀ position (valid : position < next.locations.entries.size),
        next.locations.entries[position].data.perms.get index = none) :
    Ready next ∧ next.tagMapping.deassigned = #[] := by
  obtain ⟨mapping,unused|reused⟩ := inserted_table tree.tagMapping next.tagMapping tag child fresh inserted
  · obtain ⟨_,empty⟩ := unused
    refine ⟨⟨?_, ?_, by simp [empty], ?_, ?_, vacant⟩,empty⟩
    · intro key included
      rw [mapping,Array.mem_push] at included
      rcases included with kept | added
      · obtain ⟨node,present,same⟩ := ready.keys key kept
        obtain ⟨retained,found,tagStill⟩ := oldNodes key.2 node present
        exact ⟨retained,found,tagStill.trans same⟩
      · subst key
        exact newNode
    · intro index member
      simp [empty] at member
    · have oldSize : tree.tagMapping.mapping.size = tree.nodes.size := by
        simpa [noFree] using ready.balanced
      rw [mapping,empty,size]
      simp [oldSize]
    · rwa [size]
  · simp [noFree] at reused

theorem preserves_reuse (tree next : BorrowTree) (tag : BorTag) (child : UniIndex)
    (ready : Ready tree) (reusing : tree.tagMapping.deassigned.back? = some child)
    (fresh : tree.tagMapping.get tag = none)
    (inserted : tree.tagMapping.insert tag = .Inserted next.tagMapping child)
    (size : next.nodes.size = tree.nodes.size)
    (oldNodes : ∀ index node, tree.nodeAt index = some node →
      ∃ retained, next.nodeAt index = some retained ∧ retained.tag = node.tag)
    (newNode : ∃ installed, next.nodeAt child = some installed ∧ installed.tag = tag)
    (reserved : ∀ index, index ≠ child → tree.nodeAt index = none → next.nodeAt index = none)
    (vacant : ∀ index, next.nodeAt index = none →
      ∀ position (valid : position < next.locations.entries.size),
        next.locations.entries[position].data.perms.get index = none) :
    Ready next := by
  obtain ⟨mapping,unused|reused⟩ := inserted_table tree.tagMapping next.tagMapping tag child fresh inserted
  · rw [reusing] at unused
    have impossible : some child = none := unused.1
    cases impossible
  obtain ⟨pool,oldPool⟩ := Array.back?_eq_some_iff.mp reusing
  have newPool : next.tagMapping.deassigned = pool := by rw [reused.2,oldPool,Array.pop_push]
  have distinct : pool.toList.Nodup ∧ child ∉ pool.toList := by
    have all := ready.freeDistinct
    rw [oldPool,Array.toList_push,List.nodup_append] at all
    exact ⟨all.1, fun present => all.2.2 child present child (by simp) rfl⟩
  refine ⟨?_, ?_, by rw [newPool]; exact distinct.1, ?_, ?_, vacant⟩
  · intro key included
    rw [mapping,Array.mem_push] at included
    rcases included with kept | added
    · obtain ⟨node,present,same⟩ := ready.keys key kept
      obtain ⟨retained,found,tagStill⟩ := oldNodes key.2 node present
      exact ⟨retained,found,tagStill.trans same⟩
    · subst key
      exact newNode
  · intro index member
    rw [newPool] at member
    have beforeMember : index ∈ tree.tagMapping.deassigned := by
      rw [oldPool]
      exact Array.mem_push.mpr (Or.inl member)
    obtain ⟨bounded,empty⟩ := ready.free index beforeMember
    refine ⟨size.symm ▸ bounded, reserved index ?_ empty⟩
    rintro rfl
    exact distinct.2 (by simpa using member)
  · have oldSize := ready.balanced
    rw [oldPool,Array.size_push] at oldSize
    rw [mapping,newPool,Array.size_push,size]
    omega
  · rw [size]
    exact ready.headroom

end DuplicatePrefix.RetagInsertionCapacity

#print axioms DuplicatePrefix.RetagInsertionCapacity.derive
#print axioms DuplicatePrefix.RetagInsertionCapacity.inserted_table

#print axioms DuplicatePrefix.RetagInsertionCapacity.preserves_append

#print axioms DuplicatePrefix.RetagInsertionCapacity.preserves_reuse

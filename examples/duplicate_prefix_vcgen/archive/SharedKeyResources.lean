import duplicate_prefix.SharedReborrowContinuity
import duplicate_prefix.RetagInsertionCapacity

namespace DuplicatePrefix.ArchiveForestProjection
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open RetagReleaseFootprint

/-- Append-mode shared retag preserves the occupied-key and free-slot
representation invariant needed by later mutable reborrows. -/
theorem SharedChildFrame.readyAfterAppend {original read after : BorrowTree}
    {parent child : UniIndex} {tag : BorTag} {offset length : Size} {inside : DedupRangeMap LocationState}
    (frame : SharedChildFrame original read after parent child tag offset length inside)
    (ready : RetagInsertionCapacity.Ready original) (space : original.nodes.size+1 < 2^32)
    (noFree : original.tagMapping.deassigned = #[]) (fresh : original.indexOfTag tag = none)
    (newNode : ∃ installed, after.nodeAt child = some installed ∧ installed.tag = tag)
    (vacant : VacantRows after) :
    RetagInsertionCapacity.Ready after := by
  have aligned : original.tagMapping.mapping.size = original.nodes.size := by simpa [noFree] using ready.balanced
  obtain ⟨_, _, size⟩ := frame.appended noFree aligned
  have oldNodes (index : UniIndex) (node : TreeNode) (known : original.nodeAt index = some node) :
      ∃ retained, after.nodeAt index = some retained ∧ retained.tag = node.tag := by
    have available : read.nodeAt index = some node := by rw [frame.readMetadata]; exact known
    have distinct : index ≠ child := by
      intro equal
      rw [equal, frame.attached.fresh] at available
      contradiction
    obtain ⟨retained, found, _⟩ := frame.attached.oldEdges index node available
    obtain ⟨prior, oldFound, sameTag, _⟩ := frame.olderNodes index retained distinct found
    have equal := Option.some.inj (oldFound.symm.trans known)
    exact ⟨retained, found, sameTag.symm.trans (congrArg TreeNode.tag equal)⟩
  exact (RetagInsertionCapacity.preserves_append original after tag child ready space noFree fresh frame.inserted size
    oldNodes newNode vacant).1

theorem ready_following_release (before after : BorrowTree)
    (shape : after = {before with locations := after.locations})
    (ready : RetagInsertionCapacity.Ready before) (vacant : VacantRows after) :
    RetagInsertionCapacity.Ready after := by
  rw [shape]
  exact { ready with rowVacant := by rw [← shape]; exact vacant }

theorem ready_tag_at (tree : BorrowTree) (ready : RetagInsertionCapacity.Ready tree)
    (index : UniIndex) (tag : BorTag) (node : TreeNode)
    (selected : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node) :
    node.tag = tag := by
  unfold BorrowTree.indexOfTag UniKeyMap.get at selected
  cases lookup : tree.tagMapping.mapping.find? (fun row => row.1 == tag) with
  | none => simp [lookup] at selected
  | some row =>
    have accepts : (row.1 == tag) = true := Array.find?_some (p := fun value : BorTag × UniIndex => value.1 == tag) lookup
    have same := beq_iff_eq.mp accepts
    have member := Array.mem_of_find?_eq_some lookup
    obtain ⟨prior, observed, priorTag⟩ := ready.keys row member
    have rowIndex : row.2 = index := Option.some.inj (by simpa [lookup] using selected)
    rw [rowIndex, present] at observed
    exact (congrArg TreeNode.tag (Option.some.inj observed)).trans (priorTag.trans same)

#print axioms SharedChildFrame.readyAfterAppend
#print axioms ready_following_release
#print axioms ready_tag_at
end DuplicatePrefix.ArchiveForestProjection

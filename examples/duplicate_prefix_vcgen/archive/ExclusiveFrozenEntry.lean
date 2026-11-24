import duplicate_prefix.ExclusiveRetagFrame
import duplicate_prefix.RetagFrozenChild
import duplicate_prefix.RetagKeyFrame

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open DuplicatePrefix.MutableSliceRights DuplicatePrefix.SourceDomain
open DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.RetagFrozenChild
open Miri.TreeBorrows.BorrowTree.ZeroProtection

private theorem selected_inside (offset : Size) (range : ByteRange) (capacity : Size)
    (ordered : range.start ≤ range.stop)
    (fits : offset.bytes.toNat + range.stop.toNat ≤ capacity.bytes.toNat)
    (start : Size) (added : Size.add (Size.ofBytes range.start) offset = .ok start) :
    start.bytes.toNat + (range.stop - range.start).toNat ≤ capacity.bytes.toNat := by
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  have nooverflow : range.start.toNat + offset.bytes.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (by omega) capacity.bytes.toNat_lt
  have sum : (range.start + offset.bytes).toNat = range.start.toNat + offset.bytes.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt nooverflow]
  have ordinary : ¬ range.start + offset.bytes < range.start := by
    intro impossible
    have less := UInt64.lt_iff_toNat_lt.mp impossible
    omega
  have actual : Size.add (Size.ofBytes range.start) offset =
      .ok (Size.ofBytes (range.start + offset.bytes)) := by
    simp [Size.add, Size.ofBytes, ordinary]
  have exactStart := Except.ok.inj (actual.symm.trans added)
  rw [← exactStart]
  simp only [Size.ofBytes, sum, UInt64.toNat_sub_of_le _ _ ordered]
  omega

/-- A fresh frozen mutable receiver is actually installed and inherits the
admitted byte ownership of its parent. Slot, graph and range hypotheses are
structural and no child- or byte-access-success condition is an input. -/
theorem install_frozen_entry
    (tree : BorrowTree) (offset : Size) (protections : ProtectedTags)
    (parentTag tag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (inside : DedupRangeMap LocationState)
    (coherent : CoherentForest tree)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode)
    (tagFresh : tree.indexOfTag tag = none)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (appendAligned : tree.tagMapping.deassigned.back? = none →
      tree.tagMapping.mapping.size = tree.nodes.size)
    (reuseValid : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (graph : ParentDepth tree.nodes) (rank : graph.depth parent < tree.nodes.size)
    (freshRows : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenEntryState segment.data)
    (lower upper : UInt64)
    (owned : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      ∀ prior, ValueAt tree.locations point prior → OwnsByte tree prior protections parent) :
    ∃ mapping child, tree.tagMapping.insert tag = .Inserted mapping child ∧
      let result := tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) true
      result.outcome = .ok () ∧ result.tree.indexOfTag tag = some child ∧
      (∃ node, result.tree.nodeAt child = some node ∧ node.tag = tag) ∧
      result.tree.locations.size = tree.locations.size ∧
      result.tree.locations.WellFormed ∧
      ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
        ∀ location, ValueAt result.tree.locations point location →
          OwnsByte result.tree location (protections.insert tag .StrongProtector) child := by
  obtain ⟨mapping, child, mapped, vacant, complete, _⟩ := newChild_frozen_frame
    tree offset parentTag tag parent parentNode inside parentFound present tagFresh
    room appendAligned reuseValid coherent.ranges graph rank freshRows span frozen
  have key := MutableRetagFootprint.newChild_selected_key tree offset (.concrete parentTag)
    tag inside (.ReservedFrz false) true mapping child mapped
  obtain ⟨attachment, childTag⟩ := MutableSliceRetag.attachment tree offset parentTag tag parent child
    mapping inside (.ReservedFrz false) true coherent mapped parentFound parentNode present vacant complete
  obtain ⟨node, stored, _⟩ := attachment.childParent
  refine ⟨mapping, child, mapped, complete, key, ⟨node, stored, childTag node stored⟩, ?_⟩
  apply installed_frozen_rights tree offset protections parentTag tag parent child mapping inside
    coherent mapped parentFound parentNode present vacant fresh (freshRows child vacant)
    ?_ ?_ complete lower upper owned
  · intro segment member start added
    exact selected_inside offset segment.range tree.locations.size (span segment member).1
      (span segment member).2 start added
  · intro segment member
    rcases frozen segment member with state | state <;> rw [state] <;> rfl

#print axioms install_frozen_entry
end DuplicatePrefix.ArchiveForestProjection

import MutableSliceRights
import Miri.Verification.MutableRetagFootprint

namespace DuplicatePrefix.MutableSliceRetag

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.Verification
open DuplicatePrefix.MutableSliceRights DuplicatePrefix.SourceDomain

/-- A successful concrete `newChild` establishes the structural relation
needed to carry byte rights from its parent. The attachment preserves the
old parent edges even when ancestor SIFA bookkeeping updates those nodes. -/
theorem attachment (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent child : UniIndex) (mapping : UniKeyMap BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (coherent : CoherentForest tree)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ()) :
    let next := (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
    Attachment tree next parent child ∧
      (∀ node, next.nodeAt child = some node → node.tag = tag) := by
  let next := (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
  have entries := MutableRetagFootprint.newChild_nodeMetadata tree offset parentTag tag parent child
    mapping inside outside held mapped parentFound parentNode present vacant complete
  have freshEntry := entries child
  simp only [MutableRetagFootprint.nodeMetadata] at freshEntry
  have childPresent : ∃ node, next.nodeAt child = some node ∧ node.tag = tag ∧ node.parent = some parent := by
    cases lookup : next.nodeAt child with
    | none => change ((next.nodeAt child).map _) = _ at freshEntry
              simp [lookup] at freshEntry
    | some node =>
      change ((next.nodeAt child).map _) = _ at freshEntry
      rw [lookup] at freshEntry
      have shape := Option.some.inj freshEntry
      exact ⟨node, rfl, congrArg Prod.fst shape, congrArg (fun row => row.2.1) shape⟩
  obtain ⟨childNode, stored, installedTag, parentEdge⟩ := childPresent
  refine ⟨⟨vacant, ⟨parentNode, present⟩, ⟨childNode, stored, parentEdge⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro index node found
    have distinct : index ≠ child := by
      intro same
      rw [same, vacant] at found
      contradiction
    have relation := entries index
    simp only [ite_eq_right distinct, MutableRetagFootprint.nodeMetadata, found, Option.map_some] at relation
    change ((next.nodeAt index).map _) = _ at relation
    cases lookup : next.nodeAt index with
    | none => simp [lookup] at relation
    | some nextNode =>
      rw [lookup] at relation
      exact ⟨nextNode, rfl, congrArg (fun row => row.2.1) (Option.some.inj relation)⟩
  · intro index node distinct found
    change next.nodeAt index = some node at found
    have relation := entries index
    change MutableRetagFootprint.nodeMetadata next index = _ at relation
    simp only [ite_eq_right distinct, MutableRetagFootprint.nodeMetadata, found, Option.map_some] at relation
    cases lookup : tree.nodeAt index with
    | none => simp [lookup] at relation
    | some previous =>
      rw [lookup] at relation
      exact ⟨previous, rfl, congrArg (fun row => row.2.1) (Option.some.inj relation).symm⟩
  · intro index node found edge
    obtain ⟨_, parentFound⟩ := coherent.parentPresent index node child found edge
    rw [vacant] at parentFound
    contradiction
  · intro node found
    rw [stored] at found
    cases found
    exact installedTag

end DuplicatePrefix.MutableSliceRetag

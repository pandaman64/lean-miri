import Miri.TreeBorrows.TreeState

namespace Miri.Verification.MutableRetagFootprint

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open BorrowTree BorrowTree.ZeroProtection BorrowTree.MutationVerification

/-- Old nodes may change child lists and SIFAs during retag. The identity,
parent edge and default permission remain observable at the same index. -/
def nodeMetadata (tree : BorrowTree) (index : UniIndex) : Option (BorTag × Option UniIndex × Permission) :=
  (tree.nodeAt index).map (fun node => (node.tag, node.parent, node.defaultInitialPermission))

private theorem weaken_preserves (current : BorrowTree) (index : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess) (present : current.nodeAt index = some node) :
    nodeMetadata (weakened current index node strongest) = nodeMetadata current := by
  have lookup : current.nodes.get index = some node := present
  funext query
  unfold nodeMetadata
  change ((current.nodes.insert index _).get query).map _ = (current.nodes.get query).map _
  by_cases equal : query = index
  · subst query
    rw [Sparse.get_same, lookup]
    rfl
  · rw [Sparse.get_other _ _ _ _ equal]

private theorem weakenAncestorPre_preserves (start : UniIndex) (strongest : IdempotentForeignAccess)
    (keep : (UniIndex → Option (BorTag × Option UniIndex × Permission)) → Prop)
    (fuel steps : Nat) (cursor : Option UniIndex) (current : BorrowTree) (valid : keep (nodeMetadata current)) :
    weakenAncestorPre start strongest (fun updated => keep (nodeMetadata updated)) (fun _ _ => True)
      fuel steps cursor current := by
  induction fuel generalizing steps cursor current with
  | zero => trivial
  | succ fuel ih =>
    unfold weakenAncestorPre
    split
    · trivial
    · cases cursor with
      | none => exact valid
      | some index =>
        cases found : current.nodes.get index with
        | none => simp [found]
        | some node =>
          simp only [found]
          have retained : keep (nodeMetadata (weakened current index node strongest)) := by
            rw [weaken_preserves current index node strongest found]
            exact valid
          split
          · exact ih _ _ _ retained
          · exact retained

private theorem childSegmentsPre_preserves (offset : Size) (index : UniIndex) (parent : Option UniIndex)
    (held : Bool) (segments : List (RangeMapSegment Tree.LocationState)) (current : BorrowTree)
    (minimum : IdempotentForeignAccess)
    (keep : (UniIndex → Option (BorTag × Option UniIndex × Permission)) → Prop)
    (valid : keep (nodeMetadata current)) :
    childSegmentsPre offset index parent held (fun updated => keep (nodeMetadata updated)) (fun _ _ => True)
      segments current minimum := by
  induction segments generalizing current minimum with
  | nil =>
    simp only [childSegmentsPre, finishChildPre]
    cases parent with
    | none => exact valid
    | some parent =>
      unfold weakenAncestorsPre
      by_cases strongest : (minimum == .Write) = true
      · simpa only [strongest, ↓reduceIte] using valid
      · simp only [ite_eq_right strongest]
        exact weakenAncestorPre_preserves _ _ _ _ _ _ _ valid
  | cons segment rest ih =>
    simp only [childSegmentsPre, childSegmentPre]
    repeat' first
      | exact ih _ _ valid
      | trivial
      | split

/-- A successful actual insertion into the selected concrete vacant slot
preserves the identity, ancestry and defaults of every old node. This
property covers all inside segments and any ancestor SIFA weakening. -/
theorem newChild_nodeMetadata (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent child : UniIndex) (mapping : UniKeyMap BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (result : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ()) :
    ∀ query, nodeMetadata (tree.newChild offset (.concrete parentTag) tag inside outside held).tree query =
      if query = child then some (tag, some parent, outside) else nodeMetadata tree query := by
  let expected query := if query = child then some (tag, some parent, outside) else nodeMetadata tree query
  have distinct : parent ≠ child := by
    intro equal
    rw [equal, vacant] at present
    contradiction
  have pre : insertChildPre tree offset (.concrete parentTag) tag inside outside held
      (fun after => nodeMetadata after = expected) (fun _ _ => True) := by
    have parentLookup : tree.tagMapping.get parentTag = some parent := parentFound
    have parentNodeLookup : tree.nodes.get parent = some parentNode := present
    unfold insertChildPre
    simp only [mapped, parentLookup, Option.map_some]
    by_cases valid : (!outside.isInitial) = true
    · simp [valid]
    · rw [ite_eq_right valid]
      by_cases unique : outside.isUnique = true
      · simp [unique]
      · rw [ite_eq_right unique]
        cases strength : outside.strongestIdempotentForeignAccess held with
        | ImpossibleProtectedReservedIM => trivial
        | Access defaultSifa =>
          simp only [finishInsertedChildPre, Sparse.get_other _ _ _ _ distinct, parentNodeLookup]
          apply childSegmentsPre_preserves _ _ _ _ _ _ _ (fun projection => projection = expected)
          funext query
          unfold nodeMetadata BorrowTree.nodeAt
          by_cases fresh : query = child
          · subst query
            simp [expected, Sparse.get_same, Sparse.get_other _ _ _ _ (Ne.symm distinct)]
          · by_cases isParent : query = parent
            · subst query
              simp [expected, distinct, Sparse.get_same, nodeMetadata, present]
            · simp [expected, fresh, Sparse.get_other _ _ _ _ isParent,
                Sparse.get_other _ _ _ _ fresh, nodeMetadata, BorrowTree.nodeAt]
  have post := (insertChildPre_iff tree offset (.concrete parentTag) tag inside outside held
    (fun after => nodeMetadata after = expected) (fun _ _ => True)).mp pre
  simp only [childResultPre, result] at post
  intro query
  exact congrFun post query

end Miri.Verification.MutableRetagFootprint

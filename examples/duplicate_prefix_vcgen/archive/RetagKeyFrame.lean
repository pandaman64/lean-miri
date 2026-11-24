import Miri.Verification.TreeMutationWP

namespace Miri.Verification.MutableRetagFootprint

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open BorrowTree BorrowTree.MutationVerification

set_option maxHeartbeats 1000000

private theorem ancestor_keys (mapping : UniKeyMap BorTag) (start : UniIndex)
    (strongest : IdempotentForeignAccess) (fuel steps : Nat) (cursor : Option UniIndex)
    (tree : BorrowTree) (keys : tree.tagMapping = mapping) :
    weakenAncestorPre start strongest (fun t => t.tagMapping = mapping)
      (fun _ t => t.tagMapping = mapping) fuel steps cursor tree := by
  induction fuel generalizing steps cursor tree with
  | zero => exact keys
  | succ fuel ih =>
    unfold weakenAncestorPre
    split
    · exact keys
    · cases cursor with
      | none => exact keys
      | some index =>
        cases current : tree.nodes.get index with
        | none => simpa only [current] using keys
        | some node =>
          simp only [current]
          split
          · exact ih _ _ _ keys
          · exact keys

private theorem segment_keys (mapping : UniKeyMap BorTag) (offset : Size)
    (child : UniIndex) (parent : Option UniIndex) (held : Bool)
    (segments : List (RangeMapSegment Tree.LocationState)) (tree : BorrowTree)
    (sifa : IdempotentForeignAccess) (keys : tree.tagMapping = mapping) :
    childSegmentsPre offset child parent held (fun t => t.tagMapping = mapping)
      (fun _ t => t.tagMapping = mapping) segments tree sifa := by
  induction segments generalizing tree sifa with
  | nil =>
    cases parent with
    | none => exact keys
    | some index =>
      simp only [childSegmentsPre, finishChildPre, weakenAncestorsPre]
      split
      · exact keys
      · exact ancestor_keys mapping index sifa _ _ _ tree keys
  | cons segment rest ih =>
    simp only [childSegmentsPre, childSegmentPre]
    split
    · exact keys
    · split
      · exact keys
      · split
        · exact keys
        · split
          · exact keys
          · split
            · exact keys
            · exact ih _ _ keys

/-- Once the key is inserted, later child-attachment and SIFA work retain
that exact map, including on partial failure. -/
theorem newChild_keyMap (tree : BorrowTree) (offset : Size) (source : ProvenanceExtra)
    (tag : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (outside : Permission) (held : Bool)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index) :
    (tree.newChild offset source tag inside outside held).tree.tagMapping = mapping := by
  have pre : insertChildPre tree offset source tag inside outside held
      (fun t => t.tagMapping = mapping) (fun _ t => t.tagMapping = mapping) := by
    unfold insertChildPre
    simp only [inserted]
    split
    · exact True.intro
    · split
      · exact True.intro
      · split
        · exact True.intro
        · split
          · exact True.intro
          · unfold finishInsertedChildPre
            dsimp only
            split
            · exact segment_keys mapping offset index _ held _ _ _ rfl
            · split
              · rfl
              · exact segment_keys mapping offset index _ held _ _ _ rfl
  have post := (insertChildPre_iff tree offset source tag inside outside held
    (fun t => t.tagMapping = mapping) (fun _ t => t.tagMapping = mapping)).mp pre
  generalize fixed : tree.newChild offset source tag inside outside held = outcome at post ⊢
  rcases outcome with ⟨after, result⟩
  cases result with
  | ok value => cases value; exact post
  | error _ => exact post

private theorem pushed_key (table : Array (BorTag × UniIndex)) (pool : Array UniIndex)
    (tag : BorTag) (index : UniIndex) :
    (⟨(table.filter fun pair => pair.1 != tag).push (tag, index), pool⟩ : UniKeyMap BorTag).get tag =
      some index := by
  unfold UniKeyMap.get
  rw [Array.find?_push, Array.find?_filter]
  have empty : (table.find? fun pair => (pair.1 != tag) ∧ (pair.1 == tag)) = none := by
    apply Array.find?_eq_none.mpr
    intro pair _
    by_cases equal : (pair.1 == tag) = true <;> simp [bne, equal]
  simp only [empty, beq_self_eq_true, ↓reduceIte, Option.none_or, Option.map_some]

theorem inserted_lookup (tree : UniKeyMap BorTag) (tag : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (inserted : tree.insert tag = .Inserted mapping index) :
    mapping.get tag = some index := by
  unfold UniKeyMap.insert at inserted
  cases reusable : tree.deassigned.back? with
  | none =>
    cases selected : UniIndex.ofNat? tree.mapping.size with
    | none => simp [reusable, selected, Id.run, pure] at inserted
    | some selected =>
      simp only [reusable, selected, Id.run, bind, pure] at inserted
      split at inserted
      · contradiction
      · injection inserted with mapEq indexEq
        cases mapEq
        cases indexEq
        exact pushed_key _ _ _ _
  | some selected =>
    simp only [reusable, Id.run, bind, pure] at inserted
    split at inserted
    · contradiction
    · injection inserted with mapEq indexEq
      cases mapEq
      cases indexEq
      exact pushed_key _ _ _ _

/-- The concrete tag lookup resolves the actual newly installed key after the
ordered mutation has run. -/
theorem newChild_selected_key (tree : BorrowTree) (offset : Size) (source : ProvenanceExtra)
    (tag : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (outside : Permission) (held : Bool)
    (mapping : UniKeyMap BorTag) (index : UniIndex)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index) :
    (tree.newChild offset source tag inside outside held).tree.indexOfTag tag = some index := by
  unfold BorrowTree.indexOfTag
  rw [newChild_keyMap tree offset source tag inside outside held mapping index inserted]
  exact inserted_lookup tree.tagMapping tag mapping index inserted

#print axioms newChild_selected_key
end Miri.Verification.MutableRetagFootprint

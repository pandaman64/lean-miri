import Miri.Verification.TreeMutationWP

namespace Miri.Verification.MutableRetagFootprint

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open BorrowTree BorrowTree.MutationVerification

set_option maxHeartbeats 1000000

private theorem ancestor_frame (keep : BorrowTree → Prop) (start : UniIndex)
    (strongest : IdempotentForeignAccess)
    (weaken : ∀ current index node, current.nodeAt index = some node → keep current →
      keep (BorrowTree.ZeroProtection.weakened current index node strongest))
    (fuel steps : Nat) (cursor : Option UniIndex) (tree : BorrowTree) (valid : keep tree) :
    weakenAncestorPre start strongest keep (fun _ => keep) fuel steps cursor tree := by
  induction fuel generalizing steps cursor tree with
  | zero => exact valid
  | succ fuel ih =>
    unfold weakenAncestorPre
    split
    · exact valid
    · cases cursor with
      | none => exact valid
      | some index =>
        cases found : tree.nodes.get index with
        | none => simpa only [found] using valid
        | some node =>
          simp only [found]
          have next := weaken tree index node found valid
          split
          · exact ih _ _ _ next
          · exact next

/-- Range writes and ancestor bookkeeping retain a structural invariant when
each update preserves it. The same property holds on partial failure. -/
theorem childSegmentsFrame (keep : BorrowTree → Prop)
    (relocate : ∀ current locations, keep current → keep {current with locations := locations})
    (weaken : ∀ current index node strongest, current.nodeAt index = some node → keep current →
      keep (BorrowTree.ZeroProtection.weakened current index node strongest))
    (offset : Size) (child : UniIndex) (parent : Option UniIndex) (held : Bool)
    (segments : List (RangeMapSegment Tree.LocationState)) (tree : BorrowTree)
    (sifa : IdempotentForeignAccess) (valid : keep tree) :
    childSegmentsPre offset child parent held keep (fun _ => keep) segments tree sifa := by
  induction segments generalizing tree sifa with
  | nil =>
    cases parent with
    | none => exact valid
    | some index =>
      simp only [childSegmentsPre, finishChildPre, weakenAncestorsPre]
      split
      · exact valid
      · exact ancestor_frame keep index sifa
          (fun current index node found => weaken current index node sifa found) _ _ _ tree valid
  | cons segment rest ih =>
    simp only [childSegmentsPre, childSegmentPre]
    split
    · exact valid
    · split
      · exact valid
      · split
        · exact valid
        · split
          · exact valid
          · split
            · exact relocate _ _ valid
            · exact ih _ _ (relocate _ _ valid)

private theorem segment_keys (mapping : UniKeyMap BorTag) (offset : Size)
    (child : UniIndex) (parent : Option UniIndex) (held : Bool)
    (segments : List (RangeMapSegment Tree.LocationState)) (tree : BorrowTree)
    (sifa : IdempotentForeignAccess) (keys : tree.tagMapping = mapping) :
    childSegmentsPre offset child parent held (fun t => t.tagMapping = mapping)
      (fun _ t => t.tagMapping = mapping) segments tree sifa :=
  childSegmentsFrame (fun t => t.tagMapping = mapping) (fun _ _ h => h)
    (fun _ _ _ _ _ h => h) offset child parent held segments tree sifa keys

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
private theorem pushed_other (table : Array (BorTag × UniIndex)) (pool : Array UniIndex)
    (tag query : BorTag) (index : UniIndex) (different : query ≠ tag) :
    (⟨(table.filter fun pair => pair.1 != tag).push (tag, index), pool⟩ : UniKeyMap BorTag).get query =
      (⟨table, pool⟩ : UniKeyMap BorTag).get query := by
  unfold UniKeyMap.get
  rw [Array.find?_push, Array.find?_filter]
  have same : (fun pair : BorTag × UniIndex => decide ((pair.1 != tag) = true ∧ (pair.1 == query) = true)) =
      (fun pair => pair.1 == query) := by
    funext pair
    by_cases equal : pair.1 = query
    · simp [equal, different]
    · simp [equal]
  rw [same]
  simp [Ne.symm different]

theorem inserted_lookup_other (table : UniKeyMap BorTag) (tag query : BorTag)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (different : query ≠ tag)
    (inserted : table.insert tag = .Inserted mapping index) :
    mapping.get query = table.get query := by
  unfold UniKeyMap.insert at inserted
  cases reusable : table.deassigned.back? with
  | none =>
    cases selected : UniIndex.ofNat? table.mapping.size with
    | none => simp [reusable, selected, Id.run, pure] at inserted
    | some selected =>
      simp only [reusable, selected, Id.run, bind, pure] at inserted
      split at inserted
      · contradiction
      · injection inserted with mapEq indexEq
        cases mapEq
        cases indexEq
        exact pushed_other _ _ _ _ _ different
  | some selected =>
    simp only [reusable, Id.run, bind, pure] at inserted
    split at inserted
    · contradiction
    · injection inserted with mapEq indexEq
      cases mapEq
      cases indexEq
      change ((⟨(table.mapping.filter fun pair => pair.1 != tag).push (tag, index),
        table.deassigned.pop⟩ : UniKeyMap BorTag).get query) = table.get query
      have kept := pushed_other table.mapping table.deassigned.pop tag query index different
      exact kept

theorem newChild_old_key (tree : BorrowTree) (offset : Size) (source : ProvenanceExtra)
    (tag query : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (outside : Permission) (held : Bool)
    (mapping : UniKeyMap BorTag) (index : UniIndex) (different : query ≠ tag)
    (inserted : tree.tagMapping.insert tag = .Inserted mapping index) :
    (tree.newChild offset source tag inside outside held).tree.indexOfTag query =
      tree.indexOfTag query := by
  unfold BorrowTree.indexOfTag
  rw [newChild_keyMap tree offset source tag inside outside held mapping index inserted]
  exact inserted_lookup_other tree.tagMapping tag query mapping index different inserted

#print axioms newChild_old_key
end Miri.Verification.MutableRetagFootprint

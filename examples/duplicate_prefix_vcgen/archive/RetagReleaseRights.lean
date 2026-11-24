import duplicate_prefix.ExclusiveNormalRights

namespace DuplicatePrefix.RetagReleaseRights

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection

theorem contains_remove_other (tags : ProtectedTags) (removed queried : BorTag)
    (different : queried ≠ removed) :
    (tags.remove removed).contains queried = tags.contains queried := by
  unfold ProtectedTags.contains ProtectedTags.get ProtectedTags.remove
  rw [Array.find?_filter]
  congr 3
  funext pair
  by_cases eq : pair.1 = queried <;> simp [eq, different]

private theorem local_unheld (state : LocationState) (held : Bool)
    (rights : localOwns state held) : localOwns state false := by
  obtain ⟨possible, own⟩ := rights
  refine ⟨possible, ?_⟩
  cases permission : state.permission <;> simp [permission] at own ⊢
  case ReservedFrz conflicted => cases conflicted <;> trivial

private theorem foreign_unheld (state : LocationState) (held : Bool)
    (rights : foreignCompatible state held) : foreignCompatible state false :=
  ⟨rights.1, Or.inl rfl⟩

/-- Removing a protector preserves each byte's existing exclusive grant for
the raw pointer. The tag's node and permission state still exist. -/
theorem remove_preserves (tree : BorrowTree) (row : LocationTree) (source : UniIndex)
    (tags : ProtectedTags) (removed : BorTag) (rights : LocationRights tree row tags source) :
    LocationRights tree row (tags.remove removed) source := by
  intro index node found
  obtain ⟨state, stored, own, foreign⟩ := rights index node found
  by_cases same : node.tag = removed
  · have unheld : (tags.remove removed).contains node.tag = false := by
      simp [same, ProtectedTags.contains]
    simp only [unheld]
    exact ⟨state, stored, fun path => local_unheld _ _ (own path),
      fun away => foreign_unheld _ _ (foreign away)⟩
  · simpa only [contains_remove_other tags removed node.tag same] using
      (show ∃ state, tree.locationStateAt row index = some state ∧
        (Ancestor tree index source → localOwns state (tags.contains node.tag)) ∧
        (¬ Ancestor tree index source → foreignCompatible state (tags.contains node.tag)) from
        ⟨state, stored, own, foreign⟩)

theorem ancestor_trans {tree : BorrowTree} {ancestor middle source : UniIndex}
    (above : Ancestor tree ancestor middle) (below : Ancestor tree middle source) :
    Ancestor tree ancestor source := by
  induction above with
  | self => exact below
  | parent _ node found edge ih => exact .parent (ih below) node found edge

/-- A returned raw grant also gives its ancestor holder the original scope
when each intervening descendant is now unprotected. -/
theorem return_to_ancestor (tree : BorrowTree) (row : LocationTree)
    (tags : ProtectedTags) (raw holder : UniIndex) (lineage : Ancestor tree holder raw)
    (released : ∀ index node, tree.nodeAt index = some node →
      Ancestor tree index raw → ¬ Ancestor tree index holder → tags.contains node.tag = false)
    (rights : LocationRights tree row tags raw) : LocationRights tree row tags holder := by
  intro index node found
  obtain ⟨state, stored, own, foreign⟩ := rights index node found
  refine ⟨state, stored, fun path => own (ancestor_trans path lineage), ?_⟩
  intro away
  by_cases rawPath : Ancestor tree index raw
  · exact ⟨(own rawPath).1, Or.inl (released index node found rawPath away)⟩
  · exact foreign rawPath

end DuplicatePrefix.RetagReleaseRights

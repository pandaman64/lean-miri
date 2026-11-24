import duplicate_prefix.ActiveReleaseOwned
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowEvents

namespace DuplicatePrefix.ActiveRelease

private theorem setAtPos_eq {A : Type} (table : DedupRangeMap A) (position : Nat) (data : A)
    (inside : position < table.entries.size) :
    table.setAtPos position data =
      ⟨⟨table.entries.set position {table.entries[position] with data} inside⟩, .ok ()⟩ := by
  unfold DedupRangeMap.setAtPos
  change ((match (if ok : position < table.entries.size then some table.entries[position] else none) with
    | none => ⟨table, .error (.indexOutOfBounds position table.entries.size)⟩
    | some segment =>
      match (if ok : position < table.entries.size then
                Except.ok (table.entries.set position {segment with data} ok)
              else Except.error (.indexOutOfBounds position table.entries.size)) with
      | .error error => ⟨table, .error error⟩
      | .ok entries => ⟨⟨entries⟩, .ok ()⟩) : DedupMutationResult (DedupRangeMap A)) = _
  simp [inside]

private theorem otherIndex {A : Type} (table : DedupRangeMap A) (position other : Nat) (data : A)
    (inside : position < table.entries.size) (different : position ≠ other) :
    (table.setAtPos position data).state.index other = table.index other := by
  rw [setAtPos_eq _ _ _ inside]
  simp only [DedupRangeMap.index]
  have same : (table.entries.set position {table.entries[position] with data} inside)[other]? =
      table.entries[other]? := Array.getElem?_set_ne inside different
  change (match (table.entries.set position {table.entries[position] with data} inside)[other]? with
    | some x => Except.ok x
    | none => Except.error (DedupRangeMapError.indexOutOfBounds other (table.entries.set position _ inside).size)) =
    (match table.entries[other]? with
    | some x => Except.ok x
    | none => Except.error (DedupRangeMapError.indexOutOfBounds other table.entries.size))
  simp only [same, Array.size_set]

/-- Per-location ownership of the associated access of an active protector. -/
def ReleaseOwnership (tree : BorrowTree) (source root : UniIndex) (tags : ProtectedTags)
    (slot : RangeMapSegment LocationTree) : Prop :=
  ∀ localState kind, slot.data.perms.get source = some localState →
    localState.accessed = true → localState.permission.associatedAccess = some kind →
    let projected := source_normal_projection tree slot.data tags
    ∃ _forest : GeneralBorrowForest.Forest projected.topology,
      (∃ component : GeneralBorrowExposedScopedNormal.Component projected.topology source.toNat,
        GeneralBorrowExposedScopedNormal.Owned projected source.toNat kind component) ∧
      UniIndex.ofNat? (projected.topology.ancestorPath source.toNat).getLast! = some root

private def applyVisit (tree : BorrowTree) (source : UniIndex) (tags : ProtectedTags)
    (position : Nat) : DedupRangeMap LocationTree :=
  match tree.locations.index position with
  | .error _ => tree.locations
  | .ok slot =>
    match slot.data.perms.get source with
    | none => tree.locations
    | some permission =>
      match permission.permission.associatedAccess with
      | none => tree.locations
      | some kind =>
        if permission.accessed then
          let visited := tree.performTreeAccessAt slot.data (some source) kind tags .SkipChildrenOfAccessed slot.range
          (tree.locations.setAtPos position visited.location).state
        else tree.locations

private theorem step_release (original : BorrowTree) (source root : UniIndex)
    (tags : ProtectedTags) (table : DedupRangeMap LocationTree) (position : Nat)
    (sized : table.entries.size = original.locations.entries.size)
    (inside : position < original.locations.entries.size)
    (slot : RangeMapSegment LocationTree) (indexed : table.index position = .ok slot)
    (owned : ReleaseOwnership original source root tags slot)
    (roots : original.roots = #[root]) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth original.nodes)
    (children : GeneralBorrowGraph.ChildNodes original) (node : TreeNode)
    (present : original.nodeAt source = some node)
    (next : BorrowTree → Prop) (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) :
    let tree := { original with locations := table }
    let after := applyVisit tree source tags position
    (ProtectorReleaseWP.segmentPre source tags position next failure tree ↔
      next { original with locations := after }) ∧
    after.entries.size = table.entries.size ∧
    ∀ other, position ≠ other → after.index other = table.index other := by
  let tree := { original with locations := table }
  have sameIndex : tree.locations.index position = .ok slot := indexed
  have bound : position < table.entries.size := by rwa [sized]
  dsimp only
  cases state : slot.data.perms.get source with
  | none => simp [ProtectorReleaseWP.segmentPre, applyVisit, indexed, state]
  | some permission =>
    cases association : permission.permission.associatedAccess with
    | none => simp [ProtectorReleaseWP.segmentPre, applyVisit, indexed, state, association]
    | some kind =>
      cases accessed : permission.accessed with
      | false => simp [ProtectorReleaseWP.segmentPre, applyVisit, indexed, state, association, accessed]
      | true =>
        obtain ⟨forest, ⟨component, own⟩, rootPath⟩ := owned permission kind state accessed association
        have hit := segment tree source root tags position slot bound sameIndex permission state accessed
          kind association roots depth children node present forest component own rootPath next failure
        dsimp only at hit
        simp only [applyVisit, indexed, state, association, accessed, ↓reduceIte]
        refine ⟨hit, ?_, ?_⟩
        · rw [setAtPos_eq _ _ _ bound]
          simp
        · intro other different
          exact otherIndex _ _ _ _ bound different

/-- Successively visit the original range-map positions. The write at an
earlier slot preserves every later slot's ownership evidence. -/
theorem releaseAll (original : BorrowTree) (tag : BorTag) (source root : UniIndex)
    (tags : ProtectedTags) (tagIndex : original.indexOfTag tag = some source)
    (roots : original.roots = #[root]) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth original.nodes)
    (children : GeneralBorrowGraph.ChildNodes original) (node : TreeNode)
    (present : original.nodeAt source = some node) (unexposed : node.isExposed = false)
    (owned : ∀ position < original.locations.entries.size, ∃ slot,
      original.locations.index position = .ok slot ∧ ReleaseOwnership original source root tags slot) :
    ∃ after, ∀ post failure,
      ProtectorReleaseWP.releasePre tag tags post failure original ↔ post after := by
  have go (positions : List Nat) (table : DedupRangeMap LocationTree)
      (sized : table.entries.size = original.locations.entries.size)
      (unique : positions.Nodup)
      (inside : ∀ position ∈ positions, position < original.locations.entries.size)
      (untouched : ∀ position ∈ positions, table.index position = original.locations.index position) :
      ∃ after, ∀ post failure,
        ProtectorReleaseWP.segmentsPre tag tags source post failure positions
          { original with locations := table } ↔ post after := by
    induction positions generalizing table with
    | nil =>
      refine ⟨{ original with locations := table }, ?_⟩
      intro post failure
      have idx : ({ original with locations := table } : BorrowTree).indexOfTag tag = some source := tagIndex
      have atNode : ({ original with locations := table } : BorrowTree).nodeAt source = some node := present
      simp [ProtectorReleaseWP.segmentsPre, BorrowTree.MutationVerification.releaseExposurePre,
        idx, atNode, unexposed]
    | cons position rest ih =>
      have bound := inside position (List.mem_cons_self)
      obtain ⟨slot, indexed, authorized⟩ := owned position bound
      have find : table.index position = .ok slot :=
        (untouched position List.mem_cons_self).trans indexed
      let after := applyVisit { original with locations := table } source tags position
      have changes := step_release original source root tags table position sized bound slot find
        authorized roots depth children node present
      have stays := (changes (fun _ => True) (fun _ _ => False)).2
      obtain ⟨final, restProof⟩ := ih after (stays.1.trans sized) (List.nodup_cons.mp unique).2
        (fun other mem => inside other (List.mem_cons_of_mem _ mem))
        (fun other mem => (stays.2 other (fun eq => (List.nodup_cons.mp unique).1 (eq ▸ mem))).trans
          (untouched other (List.mem_cons_of_mem _ mem)))
      refine ⟨final, ?_⟩
      intro post failure
      exact (changes (ProtectorReleaseWP.segmentsPre tag tags source post failure rest) failure).1.trans
        (restProof post failure)
  let positions := List.range' 0 original.locations.entries.size
  obtain ⟨after, checked⟩ := go positions original.locations rfl (List.nodup_range')
    (by intro position member; simpa [positions] using member)
    (fun _ _ => rfl)
  exact ⟨after, fun post failure => by simpa only [ProtectorReleaseWP.releasePre, tagIndex] using checked post failure⟩

#print axioms releaseAll
end DuplicatePrefix.ActiveRelease

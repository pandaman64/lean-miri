import Miri.Verification.ProtectorReleaseWP
import duplicate_prefix.GeneralBorrowExposedScopedNormal

namespace DuplicatePrefix.ActiveRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowEvents

private theorem normalComplete (tree : BorrowTree) (location : LocationTree) (source root : UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (roots : tree.roots = #[root])
    (outcome : (tree.performNormalAccessAt location source kind protections .SkipChildrenOfAccessed).outcome =
      .ok ())
    (normal : (tree.performNormalAccessAt location source kind protections .SkipChildrenOfAccessed).access.status =
      .Completed)
    (rootIndex : UniIndex.ofNat?
      (tree.performNormalAccessAt location source kind protections .SkipChildrenOfAccessed).access.root =
        some root) :
    (tree.performTreeAccessAt location (some source) kind protections .SkipChildrenOfAccessed range).status =
      none := by
  unfold BorrowTree.performTreeAccessAt
  simp only [Id.run, outcome, normal, rootIndex, roots, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Array.size_singleton, List.range',
    List.forIn_cons, List.forIn_nil, Array.getElem?_singleton, bind, Bind.bind, pure, Pure.pure]
  simp [beq_iff_eq]
  split <;> rename_i equation <;> split at equation <;> simp_all
  all_goals (try split at equation) <;> cases equation <;> rfl

private theorem setAtPos_ok {A : Type} (table : DedupRangeMap A) (position : Nat) (data : A)
    (inside : position < table.entries.size) :
    (table.setAtPos position data).outcome = .ok () ∧
      (table.setAtPos position data).state.entries.size = table.entries.size := by
  have changed : table.setAtPos position data =
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
  simp [changed]

/-- One active call-release slot is safe when structural ownership admits its
associated access. This proof runs the actual skip-children traversal and the
actual writeback; it does not assume that either action returned successfully. -/
theorem segment (tree : BorrowTree) (source root : UniIndex) (protections : ProtectedTags)
    (position : Nat) (slot : RangeMapSegment LocationTree)
    (inBounds : position < tree.locations.entries.size)
    (indexed : tree.locations.index position = .ok slot)
    (locationState : LocationState) (localState : slot.data.perms.get source = some locationState)
    (accessed : locationState.accessed = true) (kind : AccessKind)
    (association : locationState.permission.associatedAccess = some kind)
    (roots : tree.roots = #[root])
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (present : tree.nodeAt source = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree slot.data protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection tree slot.data protections).topology source.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned
      (source_normal_projection tree slot.data protections) source.toNat kind component)
    (rootPath : UniIndex.ofNat?
      ((source_normal_projection tree slot.data protections).topology.ancestorPath source.toNat).getLast! =
      some root)
    (next : BorrowTree → Prop) (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) :
    let visit := tree.performTreeAccessAt slot.data (some source) kind protections .SkipChildrenOfAccessed slot.range
    let changed := tree.locations.setAtPos position visit.location
    ProtectorReleaseWP.segmentPre source protections position next failure tree ↔
      next {tree with locations := changed.state} := by
  let visit := tree.performTreeAccessAt slot.data (some source) kind protections .SkipChildrenOfAccessed slot.range
  have normal := GeneralBorrowExposedScopedNormal.access tree slot.data protections source kind
    .SkipChildrenOfAccessed forest component owned depth children anchorNode present
  have rootIndex : UniIndex.ofNat?
      (tree.performNormalAccessAt slot.data source kind protections .SkipChildrenOfAccessed).access.root = some root := by
    change UniIndex.ofNat?
      ((source_normal_projection tree slot.data protections).performAccess source.toNat
        kind .SkipChildrenOfAccessed).root = some root
    rw [performAccess_as_schedule]
    change UniIndex.ofNat? (sourceNormalEvents (source_normal_projection tree slot.data protections) _ kind _).root =
      some root
    rw [GeneralBorrowStorage.events_root]
    exact rootPath
  have complete : visit.status = none := normalComplete tree slot.data source root kind protections slot.range
    roots normal.2 normal.1 rootIndex
  have writeback := setAtPos_ok tree.locations position visit.location inBounds
  simp only [ProtectorReleaseWP.segmentPre, indexed, localState, association, accessed, ↓reduceIte]
  rw [← BorrowTree.RangeVerification.locationContract_iff]
  change (match (tree.locations.setAtPos position visit.location).outcome with
    | .error error => failure (.LocationMapFailure error)
        {tree with locations := (tree.locations.setAtPos position visit.location).state}
    | .ok () => match visit.status with
      | some error => failure (.AccessFailure slot.range error)
          {tree with locations := (tree.locations.setAtPos position visit.location).state}
      | none => next {tree with locations := (tree.locations.setAtPos position visit.location).state}) ↔ _
  rw [writeback.1, complete]

#print axioms segment
end DuplicatePrefix.ActiveRelease

import duplicate_prefix.ReleaseFromHolderRights
import duplicate_prefix.CopyHolderRights
import duplicate_prefix.ActiveReleaseRange
import duplicate_prefix.SharedReleaseRange

namespace DuplicatePrefix.ScopedReleaseMaterialization

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification Miri.Verification.RangeModifyLaw
open SourceDomain RetagReleaseRights RetagReleaseFootprint ActiveRelease ArchiveForestProjection
open GeneralBorrowExposure GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowProjection BorrowRangeAccess

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Releasing a tag can materialize an older node only in the released
tag's existing byte scope. In particular, a shared outer scope is stable
through the release of a nested mutable reference. -/
theorem release_preserves_scope (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (source root watch : UniIndex) (lower upper : UInt64)
    (node : TreeNode) (found : tree.nodeAt source = some node)
    (index : tree.indexOfTag tag = some source) (unexposed : node.isExposed = false)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (extent : MaterializedWithin tree source lower upper) (vacant : VacantRows tree)
    (rights : OwnedOn (fun row => LocationRights tree row tags source) lower upper tree.locations)
    (scope : MaterializedWithin tree watch lower upper) :
    ∃ after, MaterializedWithin after watch lower upper ∧ VacantRows after ∧
      ∀ post failure, ProtectorReleaseWP.releasePre tag tags post failure tree ↔ post after := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index data present parent edge
    obtain ⟨up, held⟩ := coherent.parentPresent index data parent present edge
    exact ⟨up, held, decreases index data parent present edge⟩⟩
  have childData := forest_children tree coherent
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro index data present child member
    obtain ⟨off, childPresent, _⟩ := (childData index data present).2.1 child member
    exact ⟨off, childPresent⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index node present edge
    simpa using (coherent.rootEdges index node present).mp edge
  have authorized := ReleaseFromHolderRights.releaseOwnership tree tags source root node found
    coherent roots lower upper extent vacant rights
  let retained (point : UInt64) (row : LocationTree) : Prop :=
    ∀ state, row.perms.get watch = some state → lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat
  let invariant (table : DedupRangeMap LocationTree) :=
    EachByte table retained ∧
    ∀ query, tree.nodeAt query = none → Every (fun row => row.perms.get query = none) table
  have step : ∀ table position slot, invariant table →
      table.index position = .ok slot → tree.locations.index position = .ok slot →
      position < table.entries.size → ReleaseOwnership tree source root tags slot →
      invariant (applyVisit {tree with locations := table} source tags position) := by
    intro table position slot stable currentIndex originalIndex inside _
    have originalInside : position < tree.locations.entries.size := by
      unfold DedupRangeMap.index at originalIndex
      split at originalIndex
      · rename_i segment known
        exact (Array.getElem?_eq_some_iff.mp known).1
      · contradiction
    have origSlot : tree.locations.entries[position] = slot :=
      Except.ok.inj ((index_exact tree.locations position originalInside).symm.trans originalIndex)
    unfold applyVisit
    change invariant (match table.index position with
      | .error _ => table
      | .ok segment =>
        match segment.data.perms.get source with
        | none => table
        | some state =>
          match state.permission.associatedAccess with
          | none => table
          | some kind =>
            if state.accessed then
              let access := ({tree with locations := table} : BorrowTree).performTreeAccessAt
                segment.data (some source) kind tags .SkipChildrenOfAccessed segment.range
              (table.setAtPos position access.location).state
            else table)
    simp only [currentIndex]
    cases stored : slot.data.perms.get source with
    | none => simpa only [stored] using stable
    | some state =>
      cases assoc : state.permission.associatedAccess with
      | none => simpa only [assoc] using stable
      | some kind =>
        cases accessed : state.accessed with
        | false => simpa only [assoc,accessed,Bool.false_eq_true,↓reduceIte] using stable
        | true =>
          simp only [assoc,accessed,↓reduceIte,frame_access]
          let updated := (tree.performTreeAccessAt slot.data (some source) kind tags
            .SkipChildrenOfAccessed slot.range).location
          rw [setAtPos_exact table position inside updated]
          constructor
          · apply replace_each_byte retained table position inside updated stable.1
            intro point lo hi _ _
            have currentSlot := Except.ok.inj ((index_exact table position inside).symm.trans currentIndex)
            rw [currentSlot] at lo hi
            exact extent point position originalInside
              (by rw [origSlot]; exact lo) (by rw [origSlot]; exact hi) state (by rwa [origSlot])
          · intro query empty
            apply replaced_every _ table position inside updated (stable.2 query empty)
            have saved : tree.locations.entries[position].data.perms.get source = some state := by
              rwa [origSlot]
            obtain ⟨positive, starts, stops⟩ := SharedRelease.materializedRowIntersects tree source lower upper
              coherent extent position originalInside state saved
            have permits := rights position originalInside positive starts stops
            have accessRight : LocationAccessRights tree slot.data tags source kind := by
              rw [origSlot] at permits
              cases kind
              · exact LocationRights.readRights permits
              · exact permits
            have cleanSlot : ∀ index, tree.nodeAt index = none → slot.data.perms.get index = none := by
              intro index absent
              rw [← origSlot]
              exact vacant index absent position originalInside
            have normalOwner := normal_access_owned tree slot.data tags source kind depth node found
              coherent.indexFits cleanSlot accessRight
            have graph := forest tree slot.data tags coherent.indexFits depth childData
            have asNormal : updated = (tree.performNormalAccessAt slot.data source kind tags
                .SkipChildrenOfAccessed).location :=
              GeneralBorrowRangePreserves.single_root_location tree slot.data tags source root kind
                .SkipChildrenOfAccessed slot.range graph normalOwner depth childNodes node found roots covered
            rw [asNormal]
            exact GeneralBorrowRangePreserves.normal_no_stale tree slot.data tags source query kind
              .SkipChildrenOfAccessed depth childNodes node found empty (cleanSlot query empty)
  obtain ⟨after, shape, stable, checked⟩ := releaseAll_frame tree tag source root tags index roots
    depth childNodes node found unexposed authorized invariant ⟨scope,vacant⟩ step
  refine ⟨after,stable.1,?_,checked⟩
  intro query empty
  apply stable.2 query
  have unchanged := congrArg (fun next : BorrowTree => next.nodeAt query) shape
  exact unchanged.symm.trans empty

end DuplicatePrefix.ScopedReleaseMaterialization

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ScopedReleaseMaterialization.release_preserves_scope) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved release scope dependency {dependency}"

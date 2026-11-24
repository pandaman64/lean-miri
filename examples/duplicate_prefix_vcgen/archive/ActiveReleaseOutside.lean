import duplicate_prefix.RawHolderScope
import duplicate_prefix.ScopedReleaseMaterialization
import duplicate_prefix.ExclusiveCopyRanges

namespace DuplicatePrefix.ActiveReleaseOutside

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification Miri.Verification.RangeModifyLaw
open SourceDomain RetagReleaseRights RetagReleaseFootprint ActiveRelease ArchiveForestProjection
open GeneralBorrowExposure GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowProjection BorrowRangeAccess

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- An invariant of each byte survives the actual release if it survives the
effect at every visited row inside the released range. -/
theorem framed (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (source root : UniIndex) (lower upper : UInt64)
    (node : TreeNode) (found : tree.nodeAt source = some node)
    (index : tree.indexOfTag tag = some source) (unexposed : node.isExposed = false)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (extent : MaterializedWithin tree source lower upper) (vacant : VacantRows tree)
    (rights : OwnedOn (fun row => LocationRights tree row tags source) lower upper tree.locations)
    (property : UInt64 → LocationTree → Prop)
    (initial : EachByte tree.locations property)
    (preserves : ∀ (point : UInt64) (segment : RangeMapSegment LocationTree) (kind : AccessKind),
      lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      LocationRights tree segment.data tags source →
      (∀ index, tree.nodeAt index = none → segment.data.perms.get index = none) →
      property point segment.data →
      property point (tree.performTreeAccessAt segment.data (some source) kind tags
        .SkipChildrenOfAccessed segment.range).location) :
    let actual := tree.releaseProtector tag tags
    actual.status = .Released ∧ actual.tree = {tree with locations := actual.tree.locations} ∧
      EachByte actual.tree.locations property := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro i data present parent edge
    obtain ⟨up, held⟩ := coherent.parentPresent i data parent present edge
    exact ⟨up,held,decreases i data parent present edge⟩⟩
  have childData := forest_children tree coherent
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro i data present child member
    obtain ⟨off, childPresent, _⟩ := (childData i data present).2.1 child member
    exact ⟨off,childPresent⟩
  have authorized := ReleaseFromHolderRights.releaseOwnership tree tags source root node found
    coherent roots lower upper extent vacant rights
  let invariant := fun table : DedupRangeMap LocationTree => EachByte table property
  have frame : ∀ table pos slot, invariant table →
      table.index pos = .ok slot → tree.locations.index pos = .ok slot →
      pos < table.entries.size → ReleaseOwnership tree source root tags slot →
      invariant (applyVisit {tree with locations := table} source tags pos) := by
    intro table pos slot held currentIndex originalIndex inside _
    have originalInside : pos < tree.locations.entries.size := by
      unfold DedupRangeMap.index at originalIndex
      split at originalIndex
      · rename_i segment saved
        exact (Array.getElem?_eq_some_iff.mp saved).1
      · contradiction
    have oldSlot := Except.ok.inj ((index_exact tree.locations pos originalInside).symm.trans originalIndex)
    have currentSlot := Except.ok.inj ((index_exact table pos inside).symm.trans currentIndex)
    unfold applyVisit
    change invariant (match table.index pos with
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
              (table.setAtPos pos access.location).state
            else table)
    simp only [currentIndex]
    cases saved : slot.data.perms.get source with
    | none => simpa only [saved] using held
    | some state =>
      cases assoc : state.permission.associatedAccess with
      | none => simpa only [assoc] using held
      | some kind =>
        cases accessed : state.accessed with
        | false => simpa only [assoc,accessed,Bool.false_eq_true,↓reduceIte] using held
        | true =>
          simp only [assoc,accessed,↓reduceIte,frame_access]
          rw [setAtPos_exact table pos inside]
          apply replace_each_byte property table pos inside _ held
          intro point lo hi
          have before := held point pos inside lo hi
          rw [currentSlot] at lo hi before
          have stays := extent point pos originalInside (by rwa [oldSlot]) (by rwa [oldSlot]) state (by rwa [oldSlot])
          have rowRights := rights pos originalInside (by omega)
            (by rw [oldSlot]; exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp lo) stays.2)
            (by rw [oldSlot]; exact Nat.lt_of_le_of_lt stays.1 (UInt64.lt_iff_toNat_lt.mp hi))
          rw [oldSlot] at rowRights
          have clean (query : UniIndex) (empty : tree.nodeAt query = none) : slot.data.perms.get query = none := by
            rw [← oldSlot]
            exact vacant query empty pos originalInside
          exact preserves point slot kind stays.1 stays.2 rowRights clean before
  obtain ⟨after, shape, keeps, wlp⟩ := releaseAll_frame tree tag source root tags index roots
    depth childNodes node found unexposed authorized invariant initial frame
  have works := (ProtectorReleaseWP.releasePre_iff tag tags (· = after) (fun _ _ => False) tree).mp
    ((wlp (· = after) (fun _ _ => False)).mpr rfl)
  change (match (tree.releaseProtector tag tags).status with
    | .Released => (tree.releaseProtector tag tags).tree = after
    | _ => False) at works
  dsimp only
  cases h : (tree.releaseProtector tag tags).status
  case Released =>
    simp only [h] at works
    rw [works]
    exact ⟨rfl,shape,keeps⟩
  all_goals simp [h] at works

/-- Releasing an owned protector retains every row predicate at points
outside its materialized range. -/
theorem preservesOutside (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (source root : UniIndex) (lower upper : UInt64)
    (node : TreeNode) (found : tree.nodeAt source = some node)
    (index : tree.indexOfTag tag = some source) (unexposed : node.isExposed = false)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (extent : MaterializedWithin tree source lower upper) (vacant : VacantRows tree)
    (rights : OwnedOn (fun row => LocationRights tree row tags source) lower upper tree.locations)
    (property : UInt64 → LocationTree → Prop)
    (initial : EachByte tree.locations fun point row =>
      (point.toNat < lower.toNat ∨ upper.toNat ≤ point.toNat) → property point row) :
    let actual := tree.releaseProtector tag tags
    actual.status = .Released ∧ actual.tree = {tree with locations := actual.tree.locations} ∧
      EachByte actual.tree.locations (fun point row =>
        (point.toNat < lower.toNat ∨ upper.toNat ≤ point.toNat) → property point row) := by
  apply framed tree tags tag source root lower upper node found index unexposed coherent roots extent vacant rights _ initial
  intro point segment kind lo hi _ _ _ outside
  rcases outside with below | above <;> omega

end DuplicatePrefix.ActiveReleaseOutside

#print axioms DuplicatePrefix.ActiveReleaseOutside.framed
#print axioms DuplicatePrefix.ActiveReleaseOutside.preservesOutside

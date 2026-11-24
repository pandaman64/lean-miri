import duplicate_prefix.ReleaseFromHolderRights
import duplicate_prefix.SharedReleaseRange

namespace DuplicatePrefix.ScopedPhysicalRelease

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowExposure
open ActiveRelease SourceDomain RetagReleaseFootprint RetagReleaseRights

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Scope only rows that perform an associated access during a release.
Cached inactive permissions are permitted outside the released byte span. -/
def VisitsWithin (tree : BorrowTree) (source : UniIndex) (lower upper : Nat) : Prop :=
  RangeModifyLaw.EachByte tree.locations fun point row =>
    ∀ state kind, row.perms.get source = some state → state.accessed = true →
      state.permission.associatedAccess = some kind → lower ≤ point.toNat ∧ point.toNat < upper

def RetainsOutside (before after : DedupRangeMap LocationTree) (lower upper : Nat) : Prop :=
  ∃ same : after.entries.size = before.entries.size,
    ∀ position (inside : position < after.entries.size),
      let old := before.entries[position]'(same ▸ inside)
      after.entries[position].range = old.range ∧
        (∀ point, old.range.start ≤ point → point < old.range.stop →
          point.toNat < lower ∨ upper ≤ point.toNat → after.entries[position].data = old.data)

def FramesRows (relation : LocationTree → LocationTree → Prop)
    (before after : DedupRangeMap LocationTree) : Prop :=
  ∃ same : after.entries.size = before.entries.size,
    ∀ position (inside : position < after.entries.size),
      relation (before.entries[position]'(same ▸ inside)).data after.entries[position].data

private theorem framesRowsReplacement (relation : LocationTree → LocationTree → Prop)
    (original table : DedupRangeMap LocationTree) (frames : FramesRows relation original table)
    (position : Nat) (inside : position < table.entries.size) (row : LocationTree)
    (localChange : ∀ earlier : position < original.entries.size,
      relation original.entries[position].data row) :
    FramesRows relation original (replaced table position inside row) := by
  obtain ⟨same, retains⟩ := frames
  refine ⟨(replaced_length _ _ _ _).trans same,?_⟩
  intro i valid
  have oldBound : i < table.entries.size := by simpa only [replaced_length] using valid
  by_cases selected : position = i
  · subst i
    simpa [replaced] using localChange (same ▸ inside)
  · simpa [replaced,Array.getElem_set,selected] using retains i oldBound

theorem VisitsWithin.ofMaterialized {tree : BorrowTree} {source : UniIndex} {lower upper : UInt64}
    (extent : MaterializedWithin tree source lower upper) : VisitsWithin tree source lower.toNat upper.toNat := by
  intro point position inside lo hi state _ saved _ _
  exact extent point position inside lo hi state saved

private theorem retainsReplacement
    (original table : DedupRangeMap LocationTree) (lower upper : Nat)
    (retains : RetainsOutside original table lower upper)
    (position : Nat) (inside : position < table.entries.size) (row : LocationTree)
    (touched : ∀ point, table.entries[position].range.start ≤ point →
      point < table.entries[position].range.stop → lower ≤ point.toNat ∧ point.toNat < upper) :
    RetainsOutside original (replaced table position inside row) lower upper := by
  obtain ⟨same, saved⟩ := retains
  refine ⟨(replaced_length _ _ _ _).trans same,?_⟩
  intro i valid
  have earlier : i < table.entries.size := by simpa only [replaced_length] using valid
  have keep := saved i earlier
  refine ⟨(replaced_range table position inside row i earlier).trans keep.1, ?_⟩
  intro point lo hi outside
  by_cases here : position = i
  · subst i
    have within := touched point (by rwa [keep.1]) (by rwa [keep.1])
    rcases outside with outside | outside <;> omega
  · simpa [replaced,Array.getElem_set,here] using keep.2 point lo hi outside

/-- The real protector release preserves every row segment covering an
outside byte, as well as the row geometry and node graph. -/
theorem releaseFramesRows
    (tree : BorrowTree) (tag : BorTag) (source root : UniIndex) (tags : ProtectedTags)
    (key : tree.indexOfTag tag = some source)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (node : TreeNode) (present : tree.nodeAt source = some node) (hidden : node.isExposed = false)
    (lower upper : Nat) (withinScope : VisitsWithin tree source lower upper)
    (authorized : ∀ position < tree.locations.entries.size, ∃ slot,
      tree.locations.index position = .ok slot ∧ ReleaseOwnership tree source root tags slot)
    (relation : LocationTree → LocationTree → Prop)
    (refl : ∀ row, relation row row)
    (watch : ∀ position (inside : position < tree.locations.entries.size) state kind,
      tree.locations.entries[position].data.perms.get source = some state →
      state.accessed = true → state.permission.associatedAccess = some kind →
      relation tree.locations.entries[position].data
        (tree.performTreeAccessAt tree.locations.entries[position].data (some source)
          kind tags .SkipChildrenOfAccessed tree.locations.entries[position].range).location) :
    ∃ after, tree.releaseProtector tag tags = ⟨after,.Released⟩ ∧
      after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧ RetainsOutside tree.locations after.locations lower upper ∧
      FramesRows relation tree.locations after.locations := by
  obtain ⟨rank,bounded,decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank,bounded,fun index data found parent edge => by
    obtain ⟨up, atParent⟩ := coherent.parentPresent index data parent found edge
    exact ⟨up,atParent,decreases index data parent found edge⟩⟩
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index data found child member
    obtain ⟨off,childPresent,_⟩ := (forest_children tree coherent index data found).2.1 child member
    exact ⟨off,childPresent⟩
  let invariant (table : DedupRangeMap LocationTree) : Prop :=
    table.WellFormed ∧ table.size = tree.locations.size ∧ RetainsOutside tree.locations table lower upper ∧ FramesRows relation tree.locations table
  have frame : ∀ table position slot, invariant table → table.index position = .ok slot →
      tree.locations.index position = .ok slot → position < table.entries.size →
      ReleaseOwnership tree source root tags slot →
      invariant (applyVisit {tree with locations := table} source tags position) := by
    intro table position slot stable indexed initial inside _
    have rowHere := Except.ok.inj ((index_exact table position inside).symm.trans indexed)
    have originalInside : position < tree.locations.entries.size := by
      unfold DedupRangeMap.index at initial
      split at initial
      · rename_i row lookup
        exact (Array.getElem?_eq_some_iff.mp lookup).1
      · contradiction
    have rowBefore := Except.ok.inj ((index_exact tree.locations position originalInside).symm.trans initial)
    unfold applyVisit
    change invariant (match table.index position with
      | .error _ => table
      | .ok segment => match segment.data.perms.get source with
        | none => table
        | some state => match state.permission.associatedAccess with
          | none => table
          | some kind => if state.accessed then
            (table.setAtPos position
              (({tree with locations := table} : BorrowTree).performTreeAccessAt
                segment.data (some source) kind tags .SkipChildrenOfAccessed segment.range).location).state
            else table)
    simp only [indexed]
    cases stored : slot.data.perms.get source with
    | none => simpa only [stored] using stable
    | some state =>
      cases associated : state.permission.associatedAccess with
      | none => simpa only [stored,associated] using stable
      | some kind =>
        cases accessed : state.accessed with
        | false => simpa only [stored,associated,accessed,Bool.false_eq_true,ite_false] using stable
        | true =>
          simp only [associated,accessed,frame_access]
          let next := (tree.performTreeAccessAt slot.data (some source) kind tags .SkipChildrenOfAccessed slot.range).location
          rw [setAtPos_exact table position inside next]
          refine ⟨replaced_wellFormed _ _ _ _ stable.1,(replaced_size _ _ _ _).trans stable.2.1, ?_, ?_⟩
          · apply retainsReplacement _ _ _ _ stable.2.2.1 _ _ _
            intro point lo hi
            have starts : tree.locations.entries[position].range.start ≤ point := by rwa [rowBefore,← rowHere]
            have stops : point < tree.locations.entries[position].range.stop := by rwa [rowBefore,← rowHere]
            exact withinScope point position originalInside starts stops state kind (by rwa [rowBefore]) accessed associated
          · apply framesRowsReplacement relation _ _ stable.2.2.2
            intro earlier
            have agreed := watch position originalInside state kind (by rwa [rowBefore]) accessed associated
            simpa only [rowBefore,next] using agreed
  obtain ⟨after,shape,formed,exactRelease⟩ :=
    releaseAll_frame tree tag source root tags key roots depth children node present hidden authorized invariant
      ⟨coherent.ranges,rfl,⟨rfl,fun _ _ => ⟨rfl,fun _ _ _ _ => rfl⟩⟩,
        ⟨rfl,fun i inside => refl tree.locations.entries[i].data⟩⟩ frame
  have actual := (ProtectorReleaseWP.releasePre_iff tag tags (· = after) (fun _ _ => False) tree).mp
    ((exactRelease _ _).mpr rfl)
  have released : tree.releaseProtector tag tags = ⟨after,.Released⟩ := by
    cases selected : tree.releaseProtector tag tags with
    | mk output status =>
      rw [selected] at actual
      cases status
      all_goals first | contradiction | exact congrArg (fun t => BorrowTree.ProtectorReleaseResult.mk t .Released) actual
  refine ⟨after,released,shape,?_,formed.2.1,formed.2.2.1,formed.2.2.2⟩
  rw [shape]
  exact {coherent with ranges := formed.1}

#print axioms releaseFramesRows
end DuplicatePrefix.ScopedPhysicalRelease

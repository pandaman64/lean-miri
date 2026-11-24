import ActiveReleaseRangeOfCall
import duplicate_prefix.NonemptyReturnWatch
import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.ScopedPhysicalRelease

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection RetagReleaseFootprint RetagReleaseRights
open GeneralBorrowExposure GeneralBorrowProjection BorrowRangeAccess GeneralRangeMapState GeneralRangeMapOrigins
open CanonicalCallDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Releasing the source preserves another protector's accessed scope if
the second protector is outside the source's ancestor chain. -/
theorem releasePreservesWatch
    (tree : BorrowTree) (tag : BorTag) (source root watch : UniIndex) (tags : ProtectedTags)
    (key : tree.indexOfTag tag = some source)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (actor watched : TreeNode) (present : tree.nodeAt source = some actor) (hidden : actor.isExposed = false)
    (atWatch : tree.nodeAt watch = some watched) (foreign : ¬ Ancestor tree watch source)
    (lower upper : UInt64) (withinScope : VisitsWithin tree source lower.toNat upper.toNat)
    (vacant : VacantRows tree)
    (sourceRights : OwnedOn (fun row => LocationRights tree row tags source) lower upper tree.locations)
    (watchLower watchUpper : Nat) (watchScope : AccessedOnlyWithin tree watch watchLower watchUpper) :
    ∃ after, tree.releaseProtector tag tags = ⟨after,.Released⟩ ∧
      after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧ RetainsOutside tree.locations after.locations lower.toNat upper.toNat ∧
      VacantRows after ∧ AccessedOnlyWithin after watch watchLower watchUpper := by
  obtain ⟨rank,bounded,decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank,bounded,fun index data found parent edge => by
    obtain ⟨up, atParent⟩ := coherent.parentPresent index data parent found edge
    exact ⟨up,atParent,decreases index data parent found edge⟩⟩
  have childData := forest_children tree coherent
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index data found child member
    obtain ⟨off,childPresent,_⟩ := (childData index data found).2.1 child member
    exact ⟨off,childPresent⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data found rootEdge
    simpa using (coherent.rootEdges index data found).mp rootEdge
  have authorized := accessedAuthorization tree tags source root actor present coherent roots lower upper
    withinScope vacant sourceRights
  have active := activeRights tree tags source lower upper coherent withinScope vacant sourceRights
  let relation (before after : LocationTree) : Prop :=
    ((tree.locationStateAt after watch).map LocationState.accessed =
      (tree.locationStateAt before watch).map LocationState.accessed) ∧
    ∀ index, tree.nodeAt index = none → before.perms.get index = none → after.perms.get index = none
  have preserves (position : Nat) (inside : position < tree.locations.entries.size) (state : LocationState)
      (kind : AccessKind) (stored : tree.locations.entries[position].data.perms.get source = some state)
      (accessed : state.accessed = true) (assoc : state.permission.associatedAccess = some kind) :
      relation tree.locations.entries[position].data
        (tree.performTreeAccessAt tree.locations.entries[position].data (some source)
          kind tags .SkipChildrenOfAccessed tree.locations.entries[position].range).location := by
    let row := tree.locations.entries[position].data
    obtain ⟨rights,clean⟩ := active position inside state kind stored accessed assoc
    have forest := forest tree row tags coherent.indexFits depth childData
    have own : LocationAccessRights tree row tags source kind := by
      cases kind
      · exact LocationRights.readRights rights
      · exact rights
    have owner := normal_access_owned tree row tags source kind depth actor present coherent.indexFits clean own
    have location := GeneralBorrowRangePreserves.single_root_location tree row tags source root kind
      .SkipChildrenOfAccessed tree.locations.entries[position].range forest owner depth children actor present roots covered
    change (tree.performTreeAccessAt row (some source) kind tags .SkipChildrenOfAccessed
      tree.locations.entries[position].range).location =
      (tree.performNormalAccessAt row source kind tags .SkipChildrenOfAccessed).location at location
    change relation row (tree.performTreeAccessAt row (some source) kind tags .SkipChildrenOfAccessed
      tree.locations.entries[position].range).location
    rw [location]
    exact ⟨NonemptyReturnWatch.normalKeepsAccessed tree row tags source watch kind .SkipChildrenOfAccessed
      coherent actor watched present atWatch foreign,
      fun index absent empty => GeneralBorrowRangePreserves.normal_no_stale tree row tags source index kind
        .SkipChildrenOfAccessed depth children actor present absent empty⟩
  obtain ⟨after,released,shape,formed,size,outside,framed⟩ := releaseFramesRows tree tag source root tags key
    coherent roots actor present hidden lower.toNat upper.toNat withinScope authorized relation
    (fun _ => ⟨rfl,fun _ _ same => same⟩) preserves
  obtain ⟨rowCount,rowFrame⟩ := framed
  have ⟨_,geometry⟩ := outside
  refine ⟨after,released,shape,formed,size,outside,?_,?_⟩
  · intro index absent position inside
    have beforeAbsent : tree.nodeAt index = none := by
      have equality := congrArg (fun t : BorrowTree => t.nodeAt index) shape
      exact equality.symm.trans absent
    exact (rowFrame position inside).2 index beforeAbsent (vacant index beforeAbsent position (rowCount ▸ inside))
  · intro point position inside lo hi state seen accessed
    have beforeRange := (geometry position inside).1
    rw [beforeRange] at lo hi
    have bit := (rowFrame position inside).1
    change (tree.locationStateAt after.locations.entries[position].data watch).map LocationState.accessed = _ at bit
    simp only [BorrowTree.locationStateAt,atWatch,Option.map_some] at bit
    simp [seen,accessed] at bit
    cases saved : (tree.locations.entries[position]'(rowCount ▸ inside)).data.perms.get watch with
    | none => simp [saved,TreeNode.defaultLocationState] at bit
    | some c =>
      have on : c.accessed = true := by simpa [saved] using bit.symm
      exact watchScope point position (rowCount ▸ inside) lo hi c saved on

#print axioms releasePreservesWatch
end DuplicatePrefix.ScopedPhysicalRelease

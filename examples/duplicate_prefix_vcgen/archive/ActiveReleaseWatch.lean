import duplicate_prefix.ActiveReleaseOutside
import duplicate_prefix.NonemptyReturnWatch

namespace DuplicatePrefix.ActiveReleaseOutside

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification Miri.Verification.RangeModifyLaw
open SourceDomain RetagReleaseRights RetagReleaseFootprint ActiveRelease ArchiveForestProjection
open GeneralBorrowExposure GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowProjection BorrowRangeAccess NonemptyReturnWatch

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- A released range retains an ancestor watch whose own scope covers that
range, and retains a foreign watch even outside its own scope. -/
theorem keepsWatch (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (source root watch : UniIndex) (start length : Size) (index : tree.indexOfTag tag = some source)
    (stage : RawHolderScope.ReleaseStage tree tags source root start length)
    (watchNode : TreeNode) (watchAt : tree.nodeAt watch = some watchNode)
    (watchLo watchHi : UInt64)
    (watchRule : ¬ Ancestor tree watch source ∨
      (watchLo.toNat ≤ start.bytes.toNat ∧ (start.bytes+length.bytes).toNat ≤ watchHi.toNat))
    (watchScope : AccessedWithin tree watch watchLo watchHi)
    (property : UInt64 → LocationTree → Prop)
    (initial : EachByte tree.locations fun point row =>
      (point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) →
        property point row) :
    let run := tree.releaseProtector tag tags
    run.status = .Released ∧ run.tree = {tree with locations := run.tree.locations} ∧
    AccessedWithin run.tree watch watchLo watchHi ∧
    EachByte run.tree.locations (fun point row =>
      (point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) →
      property point row) := by
  obtain ⟨node,found,hidden⟩ := stage.hidden
  obtain ⟨rank,bounded,decreases⟩ := stage.coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank,bounded,by
    intro i data present parent edge
    obtain ⟨up, held⟩ := stage.coherent.parentPresent i data parent present edge
    exact ⟨up,held,decreases i data parent present edge⟩⟩
  have childData := forest_children tree stage.coherent
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro i data present child member
    obtain ⟨off, atNode, _⟩ := (childData i data present).2.1 child member
    exact ⟨off,atNode⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro i data present edge
    simpa using (stage.coherent.rootEdges i data present).mp edge
  let holds (point : UInt64) (row : LocationTree) :=
    (∀ state, row.perms.get watch = some state → state.accessed = true →
      watchLo.toNat ≤ point.toNat ∧ point.toNat < watchHi.toNat) ∧
    ((point.toNat < start.bytes.toNat ∨ (start.bytes+length.bytes).toNat ≤ point.toNat) → property point row)
  have ready : EachByte tree.locations holds := by
    intro point pos valid lo hi
    exact ⟨watchScope point pos valid lo hi, initial point pos valid lo hi⟩
  have preserves (point : UInt64) (segment : RangeMapSegment LocationTree) (kind : AccessKind)
      (lo : start.bytes.toNat ≤ point.toNat) (hi : point.toNat < (start.bytes+length.bytes).toNat)
      (owners : LocationRights tree segment.data tags source)
      (clean : ∀ i, tree.nodeAt i = none → segment.data.perms.get i = none)
      (before : holds point segment.data) :
      holds point (tree.performTreeAccessAt segment.data (some source) kind tags
        .SkipChildrenOfAccessed segment.range).location := by
    refine ⟨?_,fun off => (off.elim (fun h => by omega) (fun h => by omega) : False).elim⟩
    intro state stored active
    rcases watchRule with foreign | containment
    · have normal := normalKeepsAccessed tree segment.data tags source watch kind .SkipChildrenOfAccessed
        stage.coherent node watchNode found watchAt foreign
      have rights : LocationAccessRights tree segment.data tags source kind := by
        cases kind
        · exact LocationRights.readRights owners
        · exact owners
      have normalOwned := normal_access_owned tree segment.data tags source kind depth node found
        stage.coherent.indexFits clean rights
      have graph := forest tree segment.data tags stage.coherent.indexFits depth childData
      have asNormal : (tree.performTreeAccessAt segment.data (some source) kind tags .SkipChildrenOfAccessed segment.range).location =
          (tree.performNormalAccessAt segment.data source kind tags .SkipChildrenOfAccessed).location :=
        GeneralBorrowRangePreserves.single_root_location tree segment.data tags source root kind
          .SkipChildrenOfAccessed segment.range graph normalOwned depth children node found stage.roots covered
      rw [asNormal] at stored
      let next := (tree.performNormalAccessAt segment.data source kind tags .SkipChildrenOfAccessed).location
      change (tree.locationStateAt next watch).map LocationState.accessed =
        (tree.locationStateAt segment.data watch).map LocationState.accessed at normal
      have afterState : tree.locationStateAt next watch = some state := by
        simp only [BorrowTree.locationStateAt, watchAt, bind, Option.bind_some, pure,
          show next.perms.get watch = some state from stored, Option.getD_some]
      rw [afterState] at normal
      cases old : segment.data.perms.get watch with
      | none =>
        have initial : tree.locationStateAt segment.data watch = some watchNode.defaultLocationState := by
          simp only [BorrowTree.locationStateAt, watchAt, bind, Option.bind_some, pure, old, Option.getD_none]
        rw [initial] at normal
        exact False.elim (Bool.noConfusion (active.symm.trans (Option.some.inj normal)))
      | some oldState =>
        have initial : tree.locationStateAt segment.data watch = some oldState := by
          simp only [BorrowTree.locationStateAt, watchAt, bind, Option.bind_some, pure, old, Option.getD_some]
        rw [initial] at normal
        exact before.1 _ old ((Option.some.inj normal).symm.trans active)
    · exact ⟨by omega,by omega⟩
  obtain ⟨status, shape, result⟩ := framed tree tags tag source root start.bytes (start.bytes+length.bytes)
    node found index hidden stage.coherent stage.roots stage.materialized stage.vacant stage.ownership holds ready preserves
  exact ⟨status,shape,fun point pos valid lo hi => (result point pos valid lo hi).1,
    fun point pos valid lo hi => (result point pos valid lo hi).2⟩

end DuplicatePrefix.ActiveReleaseOutside

#print axioms DuplicatePrefix.ActiveReleaseOutside.keepsWatch

import duplicate_prefix.RetagSuccessorCapacity
import duplicate_prefix.ActiveStackReleaseExclusive

namespace DuplicatePrefix.RetagStageImage
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open Miri.Verification.MutableTypedRetag
open ArchiveForestProjection FrozenReborrowInputs SourceDomain RetagInsertionCapacity MutableSliceRights
open GeneralRangeMapOrigins RetagReleaseFootprint RetagFrozenChild
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem owners_of_points (tree : BorrowTree) (tags : ProtectedTags) (source : UniIndex)
    (start length : Size) (coherent : CoherentForest tree)
    (points : ∀ point : UInt64, start.bytes.toNat ≤ point.toNat →
      point.toNat < (start.bytes+length.bytes).toNat → ∀ row, ValueAt tree.locations point row →
        OwnsByte tree row tags source) :
    OwnedOn (fun row => LocationRights tree row tags source)
      start.bytes (start.bytes+length.bytes) tree.locations := by
  intro position valid positive lower upper
  let row := tree.locations.entries[position]
  have nonempty : tree.locations.entries.size ≠ 0 := by omega
  have partition := coherent.ranges
  simp only [DedupRangeMap.WellFormed,nonempty,↓reduceDIte] at partition
  have rowNonempty : row.range.start.toNat < row.range.stop.toNat :=
    UInt64.lt_iff_toNat_lt.mp (partition.2.1 position valid)
  change row.range.start.toNat < (start.bytes+length.bytes).toNat at lower
  change start.bytes.toNat < row.range.stop.toNat at upper
  let n := max start.bytes.toNat row.range.start.toNat
  have bound : n < 2^64 := by
    have first := start.bytes.toNat_lt
    have last := row.range.start.toNat_lt
    dsimp only [n]
    omega
  let atPoint := UInt64.ofNat n
  have atStart : atPoint.toNat = n := by simp [atPoint,Nat.mod_eq_of_lt bound]
  have starts : row.range.start.toNat ≤ atPoint.toNat := by rw [atStart]; exact Nat.le_max_right _ _
  have stops : atPoint.toNat < row.range.stop.toNat := by rw [atStart]; dsimp only [n]; omega
  have present : ValueAt tree.locations atPoint row.data :=
    ⟨position,valid,starts,stops,rfl⟩
  have facts := points atPoint (by rw [atStart]; exact Nat.le_max_left _ _)
    (by rw [atStart]; dsimp only [n]; omega) row.data present
  intro index node found
  obtain ⟨state,current,localRight,foreignRight⟩ := facts index node found
  exact ⟨state,current,fun path => (localOwns_iff _ _).mpr (localRight path),
    fun away => (foreignCompatible_iff _ _).mpr (foreignRight away)⟩

structure Installed (tree : BorrowTree) (tags : ProtectedTags) (source root : UniIndex) (start length : Size) : Prop where
  coherent : CoherentForest tree
  roots : tree.roots = #[root]
  found : ∃ node, tree.nodeAt source = some node ∧ node.isExposed = false
  scope : MaterializedWithin tree source start.bytes (start.bytes+length.bytes)
  vacant : VacantRows tree
  owners : OwnedOn (fun row => LocationRights tree row tags source) start.bytes (start.bytes+length.bytes)
    tree.locations

theorem uniform (offset size capacity : Size) (initial : LocationState) (held : Bool)
    (bounded : offset.bytes.toNat+size.bytes.toNat ≤ capacity.bytes.toNat)
    (frozen : FrozenChildState held initial) :
    ∀ segment ∈ (DedupRangeMap.new size initial).iterAll.toList,
      (segment.range.start ≤ segment.range.stop ∧
        offset.bytes.toNat + segment.range.stop.toNat ≤ capacity.bytes.toNat) ∧
      FrozenChildState held segment.data ∧ segment.range.stop.toNat ≤ size.bytes.toNat := by
  intro segment member
  by_cases empty : size.bytes = 0
  · simp [DedupRangeMap.new,DedupRangeMap.iterAll,empty] at member
  · simp [DedupRangeMap.new,DedupRangeMap.iterAll,beq_iff_eq,empty] at member
    subst segment
    exact ⟨⟨by simp,bounded⟩,frozen,Nat.le_refl _⟩

theorem installedWithData (tree : BorrowTree) (tags : ProtectedTags) (parentTag tag : BorTag)
    (parent root : UniIndex) (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (stage : StageData tree tags parentTag tag parent root offset length inside held)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (insideBounds : ∀ seg ∈ inside.iterAll.toList, seg.range.stop.toNat ≤ length.bytes.toNat) :
    let read := tree.performNormalAccessRange parentTag offset length .Read tags .VisitChildrenOfAccessed
    let after := (read.tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
    after.locations.size = tree.locations.size ∧
    (∃ index, after.indexOfTag tag = some index) ∧
    ∀ index, after.indexOfTag tag = some index →
      Installed after (childProtections tags tag held) index root offset length := by
  intro read after
  obtain ⟨depth,bounded,decreases⟩ := stage.coherent.parentDepth
  let graph : BorrowTree.ZeroProtection.ParentDepth tree.nodes :=
    ⟨depth,bounded,fun index node found parent edge => by
      obtain ⟨before,present⟩ := stage.coherent.parentPresent index node parent found edge
      exact ⟨before,present,decreases index node parent found edge⟩⟩
  obtain ⟨tight,rank⟩ := BorrowTree.ZeroProtection.ParentDepth.tight tree.nodes graph
  obtain ⟨parentNode,present⟩ := stage.parentPresent
  obtain ⟨_,_,size,coherent,roots,child,key,found,scope,own⟩ :=
    coherent_frozen_reborrow_with_footprint tree tags parentTag tag parent root offset length inside held
      stage.coherent parentNode present stage.roots stage.parentFound tight (rank parent parentNode present)
      stage.fresh fresh stage.room stage.aligned stage.reuse stage.vacant stage.span stage.policy stage.bounds stage.owners
  obtain ⟨insideScope,rows⟩ := scope insideBounds
  obtain ⟨node,atNode,_,unexposed⟩ := found
  refine ⟨size,⟨child,key⟩,?_⟩
  intro index chosen
  have same : index = child := Option.some.inj (chosen.symm.trans key)
  subst index
  exact ⟨coherent,roots,⟨node,atNode,unexposed⟩,insideScope,rows,
    owners_of_points after (childProtections tags tag held) child offset length coherent own⟩

theorem installed (tree : BorrowTree) (tags : ProtectedTags) (parentTag tag : BorTag)
    (parent root : UniIndex) (offset length : Size) (inside : DedupRangeMap LocationState) (held : Bool)
    (stage : Stage tree tags parentTag tag parent root offset length inside held)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (insideBounds : ∀ seg ∈ inside.iterAll.toList, seg.range.stop.toNat ≤ length.bytes.toNat) :
    let read := tree.performNormalAccessRange parentTag offset length .Read tags .VisitChildrenOfAccessed
    let after := (read.tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
    after.locations.size = tree.locations.size ∧
    (∃ index, after.indexOfTag tag = some index) ∧
    ∀ index, after.indexOfTag tag = some index →
      Installed after (childProtections tags tag held) index root offset length :=
  installedWithData tree tags parentTag tag parent root offset length inside held stage.data fresh insideBounds

end DuplicatePrefix.RetagStageImage

#print axioms DuplicatePrefix.RetagStageImage.installed

#print axioms DuplicatePrefix.RetagStageImage.installedWithData

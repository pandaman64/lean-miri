import duplicate_prefix.SharedReadWatch
import ScopedPhysicalRelease

namespace DuplicatePrefix.NonemptyReturnWatch

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open ArchiveForestProjection SourceDomain GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowProjection GeneralBorrowExposure BorrowRangeAccess RetagReleaseRights RetagReleaseFootprint
open ScopedPhysicalRelease ActiveRelease

set_option maxRecDepth 65536
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

/-- The shared Len protector visits only its initialized reference extent.
Every visited row is proved readable from its current permission data. -/
theorem sharedReleaseFrames
    (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (child root : UniIndex) (node : TreeNode)
    (found : tree.nodeAt child = some node) (unexposed : node.isExposed = false)
    (tagFound : tree.indexOfTag tag = some child)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (lower upper : UInt64) (extent : MaterializedWithin tree child lower upper) (vacant : VacantRows tree)
    (frozen : Every (fun row => ∀ state, row.perms.get child = some state → state.permission = .Frozen) tree.locations)
    (reader : OwnedOn (fun row => LocationAccessRights tree row tags child .Read) lower upper tree.locations)
    (relation : LocationTree → LocationTree → Prop) (refl : ∀ row, relation row row)
    (watch : ∀ position (inside : position < tree.locations.entries.size) state,
      tree.locations.entries[position].data.perms.get child = some state →
      state.accessed = true →
      relation tree.locations.entries[position].data
        (tree.performTreeAccessAt tree.locations.entries[position].data (some child)
          .Read tags .SkipChildrenOfAccessed tree.locations.entries[position].range).location) :
    ∃ after, tree.releaseProtector tag tags = ⟨after,.Released⟩ ∧
      after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧
      RetainsOutside tree.locations after.locations lower.toNat upper.toNat ∧
      FramesRows relation tree.locations after.locations := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index data present parent edge
    obtain ⟨up, atParent⟩ := coherent.parentPresent index data parent present edge
    exact ⟨up,atParent,decreases index data parent present edge⟩⟩
  have childData := forest_children tree coherent
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data present rootEdge
    simpa using (coherent.rootEdges index data present).mp rootEdge
  have authorized : ∀ position < tree.locations.entries.size, ∃ slot,
      tree.locations.index position = .ok slot ∧ ReleaseOwnership tree child root tags slot := by
    intro position inside
    let slot := tree.locations.entries[position]
    refine ⟨slot,index_exact _ _ inside,?_⟩
    intro state kind saved _ associated
    have isFrozen := frozen position inside state saved
    rw [isFrozen] at associated
    have kindRead : kind = .Read := (Option.some.inj associated).symm
    subst kind
    obtain ⟨positive,start,stop⟩ := SharedRelease.materializedRowIntersects tree child lower upper coherent extent position inside state saved
    have graph := forest tree slot.data tags coherent.indexFits depth childData
    have owner := normal_access_owned tree slot.data tags child .Read depth node found coherent.indexFits
      (fun query absent => vacant query absent position inside) (reader position inside positive start stop)
    let view := source_normal_projection tree slot.data tags
    let component : GeneralBorrowExposedScopedNormal.Component view.topology child.toNat :=
      ⟨fun _ => True,trivial,fun _ _ _ _ => trivial,fun _ _ _ _ => trivial⟩
    have path := GeneralBorrowTerminal.ancestor_root_present view.topology graph
      (GeneralBorrowGraph.Present tree) (GeneralBorrowGraph.parents_closed tree slot.data tags depth)
      child.toNat root.toNat owner.anchorValid ⟨child,node,rfl,found⟩
      (fun index _ => GeneralBorrowGraph.unique_root tree slot.data tags root roots covered index)
    refine ⟨graph,⟨component,fun index _ bound => owner.permissions index bound⟩,?_⟩
    rw [path]
    exact index_self root
  refine releaseFramesRows tree tag child root tags tagFound coherent roots node found unexposed
    lower.toNat upper.toNat ?_ authorized relation refl ?_
  · intro point position valid start stop state _ saved _ _
    exact extent point position valid start stop state saved
  · intro position inside state kind saved active association
    rw [frozen position inside state saved] at association
    have kindRead : kind = .Read := (Option.some.inj association).symm
    subst kind
    exact watch position inside state saved active

/-- An existing active scope still holds after a release that modified only
rows wholly inside that same extent. -/
theorem activeFromOutside {before after : BorrowTree} {watch : UniIndex} {lo hi : UInt64}
    (unchanged : RetainsOutside before.locations after.locations lo.toNat hi.toNat)
    (scope : AccessedWithin before watch lo hi) : AccessedWithin after watch lo hi := by
  intro point position valid start stop state saved active
  by_cases within : lo.toNat ≤ point.toNat ∧ point.toNat < hi.toNat
  · exact within
  · obtain ⟨sizes, frame⟩ := unchanged
    have earlier : position < before.locations.entries.size := sizes ▸ valid
    have same := frame position valid
    have left : before.locations.entries[position].range.start ≤ point := by rw [← same.1]; exact start
    have right : point < before.locations.entries[position].range.stop := by rw [← same.1]; exact stop
    have row := same.2 point left right (by omega)
    rw [row] at saved
    exact scope point position earlier left right state saved active

/-- The watcher cap observes every older foreign node, so the exact same
release certificate can be reused for the chosen physical output holder. -/
theorem sharedReleaseFramesForeign
    (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (child root : UniIndex) (node : TreeNode)
    (found : tree.nodeAt child = some node) (hidden : node.isExposed = false)
    (tagFound : tree.indexOfTag tag = some child)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (lower upper : UInt64) (extent : MaterializedWithin tree child lower upper) (vacant : VacantRows tree)
    (frozen : Every (fun row => ∀ state, row.perms.get child = some state → state.permission = .Frozen) tree.locations)
    (reader : OwnedOn (fun row => LocationAccessRights tree row tags child .Read) lower upper tree.locations) :
    ∃ after, tree.releaseProtector tag tags = ⟨after,.Released⟩ ∧
      after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧
      RetainsOutside tree.locations after.locations lower.toNat upper.toNat ∧
      FramesRows (fun initial final =>
        ∀ watch data, tree.nodeAt watch = some data → ¬ Ancestor tree watch child →
          (tree.locationStateAt final watch).map LocationState.accessed =
            (tree.locationStateAt initial watch).map LocationState.accessed)
        tree.locations after.locations := by
  apply sharedReleaseFrames tree tags tag child root node found hidden tagFound coherent roots lower upper extent
    vacant frozen reader _ (fun _ _ _ _ _ => rfl)
  intro i valid state saved accessed watch data present foreign
  let row := tree.locations.entries[i]
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank,bounded, by
    intro index data found parent rel
    obtain ⟨up, atParent⟩ := coherent.parentPresent index data parent found rel
    exact ⟨up,atParent,decreases index data parent found rel⟩⟩
  have childData := forest_children tree coherent
  have children : GeneralBorrowGraph.ChildNodes tree := by
    intro index data saved child member
    obtain ⟨off, atChild, _⟩ := (childData index data saved).2.1 child member
    exact ⟨off,atChild⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data saved rootEdge
    simpa using (coherent.rootEdges index data saved).mp rootEdge
  obtain ⟨positive,start,stop⟩ := SharedRelease.materializedRowIntersects tree child lower upper coherent extent i valid state saved
  have graph := forest tree row.data tags coherent.indexFits depth childData
  have owned := normal_access_owned tree row.data tags child .Read depth node found coherent.indexFits
    (fun query absent => vacant query absent i valid) (reader i valid positive start stop)
  have callback := GeneralBorrowRangePreserves.single_root_location tree row.data tags child root .Read
    .SkipChildrenOfAccessed row.range graph owned depth children node found roots covered
  change (tree.locationStateAt
    (tree.performTreeAccessAt row.data (some child) .Read tags .SkipChildrenOfAccessed row.range).location watch).map
    LocationState.accessed = _
  rw [callback]
  exact normalKeepsAccessed tree row.data tags child watch .Read .SkipChildrenOfAccessed coherent node data found present foreign

theorem byteFromOutside {before after : BorrowTree} {point : UInt64} {tags : ProtectedTags} {writer : UniIndex}
    {lower upper : Nat} (nodes : before.nodes = after.nodes)
    (unchanged : RetainsOutside before.locations after.locations lower upper)
    (outside : point.toNat < lower ∨ upper ≤ point.toNat)
    (right : AtByte before point tags writer) : AtByte after point tags writer := by
  intro pos valid start stop
  obtain ⟨sizes, frame⟩ := unchanged
  have beforeValid : pos < before.locations.entries.size := sizes ▸ valid
  have same := frame pos valid
  have left : before.locations.entries[pos].range.start ≤ point := by rw [← same.1]; exact start
  have last : point < before.locations.entries[pos].range.stop := by rw [← same.1]; exact stop
  have row := same.2 point left last outside
  rw [row]
  exact CopyHolderRights.rights_frame nodes _ tags writer (right pos beforeValid left last)

theorem activeFromForeignRelease {before after : BorrowTree} {watch child : UniIndex}
    {lo hi : UInt64} {lower upper : Nat}
    (unchanged : RetainsOutside before.locations after.locations lower upper)
    (frames : FramesRows (fun initial final =>
      ∀ watch data, before.nodeAt watch = some data → ¬ Ancestor before watch child →
        (before.locationStateAt final watch).map LocationState.accessed =
          (before.locationStateAt initial watch).map LocationState.accessed)
      before.locations after.locations)
    (watchNode : TreeNode) (present : before.nodeAt watch = some watchNode)
    (foreign : ¬ Ancestor before watch child)
    (scope : AccessedWithin before watch lo hi) : AccessedWithin after watch lo hi := by
  intro point pos valid lower upper state saved active
  obtain ⟨sizes, shape⟩ := unchanged
  obtain ⟨sameSizes, seen⟩ := frames
  have it : pos < before.locations.entries.size := sizes ▸ valid
  have w := seen pos valid watch watchNode present foreign
  let initial := before.locations.entries[pos].data
  have newStored : before.locationStateAt after.locations.entries[pos].data watch = some state := by
    simp only [BorrowTree.locationStateAt, present, bind, Option.bind_some, pure, saved, Option.getD_some]
  change (before.locationStateAt after.locations.entries[pos].data watch).map LocationState.accessed =
    (before.locationStateAt initial watch).map LocationState.accessed at w
  rw [newStored] at w
  cases old : initial.perms.get watch with
  | none =>
    have oldState : before.locationStateAt initial watch = some watchNode.defaultLocationState := by
      simp only [BorrowTree.locationStateAt, present, bind, Option.bind_some, pure, old, Option.getD_none]
    rw [oldState] at w
    exact False.elim (Bool.noConfusion (active.symm.trans (Option.some.inj w)))
  | some oldValue =>
    have oldState : before.locationStateAt initial watch = some oldValue := by
      simp only [BorrowTree.locationStateAt, present, bind, Option.bind_some, pure, old, Option.getD_some]
    rw [oldState] at w
    have same := (shape pos valid).1
    exact scope point pos it (by rw [← same]; exact lower) (by rw [← same]; exact upper)
      oldValue old ((Option.some.inj w).symm.trans active)

theorem SharedWatchTransfer.afterRelease {original attached released : BorrowTree} {parent child : UniIndex}
    {lower upper : UInt64} (kept : SharedWatchTransfer original attached parent child lower upper)
    (shape : released = {attached with locations := released.locations})
    (outside : RetainsOutside attached.locations released.locations lower.toNat upper.toNat)
    (foreignRows : FramesRows (fun initial final =>
      ∀ watch data, attached.nodeAt watch = some data → ¬ Ancestor attached watch child →
        (attached.locationStateAt final watch).map LocationState.accessed =
          (attached.locationStateAt initial watch).map LocationState.accessed)
      attached.locations released.locations) :
    SharedWatchTransfer original released parent child lower upper := by
  have sameNodes : attached.nodes = released.nodes := (congrArg BorrowTree.nodes shape).symm
  constructor
  · intro key index found
    rw [shape]
    exact kept.key key index found
  · intro index data found
    obtain ⟨next, present, tag, ancestor, visible⟩ := kept.node index data found
    exact ⟨next,by rw [shape]; exact present,tag,ancestor,visible⟩
  · intro old watch present
    exact (kept.ancestry old watch present).trans (ancestryFrame sameNodes)
  · intro watch present foreign path
    exact kept.recipientForeign watch present foreign ((ancestryFrame sameNodes).mpr path)
  · intro watch writer lo hi point mask existsWatch existsWriter foreign pointOutside active rights
    obtain ⟨old,stored⟩ := existsWatch
    have existsWatch : ∃ node, original.nodeAt watch = some node := ⟨old,stored⟩
    obtain ⟨current,present,_,_,_⟩ := kept.node watch old stored
    obtain ⟨activeNow, rightNow⟩ := kept.kept watch writer lo hi point mask existsWatch existsWriter foreign pointOutside active rights
    exact ⟨activeFromForeignRelease outside foreignRows current present (kept.recipientForeign watch existsWatch foreign) activeNow,
      byteFromOutside sameNodes outside pointOutside rightNow⟩

#print axioms sharedReleaseFrames
#print axioms activeFromOutside
#print axioms sharedReleaseFramesForeign
#print axioms byteFromOutside
#print axioms activeFromForeignRelease
#print axioms SharedWatchTransfer.afterRelease

end DuplicatePrefix.NonemptyReturnWatch

import duplicate_prefix.ExclusiveCopyRanges
import duplicate_prefix.SharedHolderRead
import duplicate_prefix.RetagReleaseFootprint
import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.NonemptyReturnWatch

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification Miri.Verification.RangeModifyLaw
set_option maxRecDepth 65536
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins
open GeneralBorrowProjection GeneralBorrowEvents GeneralBorrowExposure GeneralBorrowPresence
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

/-- A release visits only location states that were marked accessed. A
foreign access can create an inactive stored state outside this window. -/
def AccessedWithin (tree : BorrowTree) (watch : UniIndex) (lower upper : UInt64) : Prop :=
  EachByte tree.locations fun point row =>
    ∀ state, row.perms.get watch = some state → state.accessed = true →
      lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat

private theorem recordedAccessed (state recorded : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (result : state.recordNewAccess kind related = .Recorded recorded) :
    recorded.accessed = state.accessed := by
  unfold LocationState.recordNewAccess at result
  split at result
  · injection result with same
    subst recorded
    rfl
  · contradiction

private theorem foreignAccessed (state : LocationState) (kind : AccessKind) (held : Bool) :
    (state.performAccess kind .ForeignAccess held).resultingState.accessed = state.accessed := by
  unfold LocationState.performAccess
  split
  · rfl
  · rfl
  · split
    · rfl
    · dsimp only
      split
      · simp [LocationState.AccessResult.resultingState, AccessRelatedness.isForeign]
      · split <;> simp [LocationState.AccessResult.resultingState, AccessRelatedness.isForeign]

private theorem updatedWatch (tree : NormalTreeState) (watch : Nat) (kind : AccessKind)
    (event : TraversalEvent) (old recorded : LocationState)
    (before : tree.stateAt event.node = some old)
    (record : old.recordNewAccess kind event.relatedness = .Recorded recorded)
    (within : event.node < tree.locationStates.size)
    (foreign : event.node = watch → event.relatedness = .ForeignAccess) :
    let next := (recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node)).resultingState
    (({tree with locationStates := tree.locationStates.set event.node (some next) within} : NormalTreeState).stateAt watch).map LocationState.accessed =
      (tree.stateAt watch).map LocationState.accessed := by
  dsimp only
  by_cases same : event.node = watch
  · have mode := foreign same
    subst watch
    rw [before]
    have access := foreignAccessed recorded kind (tree.protectedNodes.contains event.node)
    have recordedBit := recordedAccessed old recorded kind event.relatedness record
    simp only [NormalTreeState.stateAt, Array.getElem?_set, within, ↓reduceIte, Option.map_some, mode]
    exact congrArg some (access.trans recordedBit)
  · rw [stateAt_update_other _ _ _ _ within (Ne.symm same)]

/-- The watched node's accessed bit survives a foreign visit, including
partial execution with an error. -/
theorem eventsPreserveAccessed (events : List TraversalEvent) (tree : NormalTreeState)
    (root watch : Nat) (kind : AccessKind)
    (foreign : ∀ event ∈ events, event.node = watch → event.relatedness = .ForeignAccess) :
    ((tree.processEvents root kind events).tree.stateAt watch).map LocationState.accessed =
      (tree.stateAt watch).map LocationState.accessed := by
  induction events generalizing tree with
  | nil => rfl
  | cons event rest ih =>
    have tail : ∀ next ∈ rest, next.node = watch → next.relatedness = .ForeignAccess :=
      fun next mem => foreign next (.tail _ mem)
    unfold NormalTreeState.processEvents
    cases present : tree.stateAt event.node with
    | none => simp [present]
    | some old =>
      cases record : old.recordNewAccess kind event.relatedness with
      | DebugAssertion => simp [present,record]
      | Recorded recorded =>
        simp only [present, record]
        by_cases within : event.node < tree.locationStates.size
        · let outcome := recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node)
          let next : NormalTreeState := {tree with locationStates := tree.locationStates.set event.node (some outcome.resultingState) within}
          have unchanged := updatedWatch tree watch kind event old recorded present record within
            (foreign event (by simp))
          have later := (ih next tail).trans unchanged
          cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
            simp only [NormalTreeState.setState, within, ↓reduceDIte]
          · simpa only [next, outcome, access] using later
          all_goals simpa only [access] using unchanged
        · simp [NormalTreeState.setState, within]

/-- The actual normal-access result, after permission-map writeback, retains
the watched node's accessed bit whenever the node is foreign to the actor. -/
theorem normalKeepsAccessed
    (tree : BorrowTree) (row : LocationTree) (tags : ProtectedTags)
    (actor watch : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (coherent : CoherentForest tree) (actorNode watchNode : TreeNode)
    (actorAt : tree.nodeAt actor = some actorNode) (watchAt : tree.nodeAt watch = some watchNode)
    (foreign : ¬ Ancestor tree watch actor) :
    let next := (tree.performNormalAccessAt row actor kind tags mode).location
    (tree.locationStateAt next watch).map LocationState.accessed =
      (tree.locationStateAt row watch).map LocationState.accessed := by
  obtain ⟨rank,bounded,decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank,bounded,by
    intro index data present parent edge
    obtain ⟨older, olderAt⟩ := coherent.parentPresent index data parent present edge
    exact ⟨older,olderAt,decreases index data parent present edge⟩⟩
  let normal := source_normal_projection tree row tags
  let schedule := normal.topology.traverse actor.toNat mode (sourceNormalSkipped normal kind)
  let next := (tree.performNormalAccessAt row actor kind tags mode).location
  have childData : ∀ index data, tree.nodeAt index = some data →
      data.children.toList.Nodup ∧
        (∀ child ∈ data.children.toList, ∃ childData, tree.nodeAt child = some childData ∧ childData.parent = some index) ∧
        (∀ child childData, tree.nodeAt child = some childData →
          childData.parent = some index → child ∈ data.children.toList) := by
    intro index data present
    simpa using coherent.childEdges index data present
  have topology := forest tree row tags coherent.indexFits depth childData
  obtain ⟨valid, _⟩ := array_of_node tree actor actorNode actorAt
  have sourceValid : actor.toNat < normal.topology.nodes.size := by
    rw [show normal.topology.nodes.size = tree.nodes.data.size from projection_size tree row tags]
    exact valid
  have visited := GeneralBorrowTraversal.traversal_data normal.topology topology actor.toNat
    sourceValid mode (sourceNormalSkipped normal kind)
  have notMember : watch.toNat ∉ normal.topology.ancestorPath actor.toNat :=
    fun member => foreign ((ancestor_iff tree row tags depth watch actor actorNode actorAt).mp member)
  have visitsForeign : ∀ event ∈ schedule.2, event.node = watch.toNat → event.relatedness = .ForeignAccess := by
    intro event member hit
    rw [(visited.2 event member).2]
    simp [GeneralBorrowAnchor.relation, hit, notMember]
  change (tree.locationStateAt next watch).map LocationState.accessed = _
  rw [← projection_location_state tree next tags watch watchNode watchAt,
    ← projection_location_state tree row tags watch watchNode watchAt]
  rw [GeneralBorrowRangePreserves.normal_projection tree row tags actor kind mode coherent.indexFits]
  have actualSkip : normal.shouldSkipForeignNode kind = (sourceNormalSkipped normal kind).contains := by
    funext index
    unfold NormalTreeState.shouldSkipForeignNode
    apply Bool.eq_iff_iff.mpr
    by_cases valid : index < normal.topology.nodes.size
    · simp [sourceNormalSkipped, List.mem_filter, List.mem_range, valid] <;> rfl
    · simp [sourceNormalSkipped, List.mem_filter, List.mem_range, valid] <;> rfl
  change ((normal.performAccess actor.toNat kind mode).tree.stateAt watch.toNat).map LocationState.accessed = _
  unfold NormalTreeState.performAccess
  rw [actualSkip]
  exact eventsPreserveAccessed schedule.2 normal schedule.1 watch.toNat kind visitsForeign

theorem accessedScopeOfMaterialized {tree : BorrowTree} {watch : UniIndex} {lo hi : UInt64}
    (scope : RetagReleaseFootprint.MaterializedWithin tree watch lo hi) :
    AccessedWithin tree watch lo hi := by
  intro point position valid start stop state stored _
  exact scope point position valid start stop state stored

/-- A checked range access preserves any pointwise fact at bytes it never
visits. At visited bytes, a foreign watcher keeps its exact accessed bit. -/
theorem rangeKeepsWatch
    (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag) (actor watch root : UniIndex)
    (kind : AccessKind) (offset length : Size)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (actorNode watchNode : TreeNode)
    (actorAt : tree.nodeAt actor = some actorNode) (watchAt : tree.nodeAt watch = some watchNode)
    (found : tree.indexOfTag tag = some actor)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (authorized : TreeRangeAccess.SlotsAuthorized tree (tree.locations.iterMut offset length)
      (some actor) kind tags .VisitChildrenOfAccessed)
    (lo hi : UInt64)
    (onActor : ¬ Ancestor tree watch actor ∨
      (lo.toNat ≤ offset.bytes.toNat ∧ (offset.bytes + length.bytes).toNat ≤ hi.toNat))
    (scope : AccessedWithin tree watch lo hi)
    (outside : UInt64 → LocationTree → Prop)
    (original : EachByte tree.locations fun point row =>
      (point.toNat < offset.bytes.toNat ∨ (offset.bytes + length.bytes).toNat ≤ point.toNat) →
      outside point row) :
    let run := tree.performBorrowAccessRange (.concrete tag) offset length kind tags .VisitChildrenOfAccessed
    run.status = .Completed ∧ run.tree = {tree with locations := run.tree.locations} ∧
      run.tree.locations.WellFormed ∧ run.tree.locations.size = tree.locations.size ∧
      AccessedWithin run.tree watch lo hi ∧
      EachByte run.tree.locations (fun point row =>
        (point.toNat < offset.bytes.toNat ∨ (offset.bytes + length.bytes).toNat ≤ point.toNat) →
        outside point row) := by
  let property (point : UInt64) (row : LocationTree) :=
    (∀ saved, row.perms.get watch = some saved → saved.accessed = true →
      lo.toNat ≤ point.toNat ∧ point.toNat < hi.toNat) ∧
    ((point.toNat < offset.bytes.toNat ∨ (offset.bytes + length.bytes).toNat ≤ point.toNat) →
      outside point row)
  have ready : EachByte tree.locations property := by
    intro point position valid starts stops
    exact ⟨scope point position valid starts stops, original point position valid starts stops⟩
  have stable (segment : RangeMapSegment LocationTree) (point : UInt64)
      (starts : offset.bytes.toNat ≤ point.toNat) (stops : point.toNat < (offset.bytes + length.bytes).toNat)
      (_ : segment.range.start ≤ point) (_ : point < segment.range.stop)
      (prior : property point segment.data) :
      property point (tree.performTreeAccessAt segment.data (some actor) kind tags
        .VisitChildrenOfAccessed segment.range).location := by
    refine ⟨?_, fun outside => (outside.elim (fun h => by omega) (fun h => by omega) : False).elim⟩
    intro state stored active
    rcases onActor with foreign | containment
    · have access := normalKeepsAccessed tree segment.data tags actor watch kind .VisitChildrenOfAccessed
        coherent actorNode watchNode actorAt watchAt foreign
      rw [single_root_location tree segment.data tags actor root kind segment.range coherent actorNode actorAt roots] at stored
      let next := (tree.performNormalAccessAt segment.data actor kind tags .VisitChildrenOfAccessed).location
      change (tree.locationStateAt next watch).map LocationState.accessed =
        (tree.locationStateAt segment.data watch).map LocationState.accessed at access
      have after : tree.locationStateAt next watch = some state := by
        simp only [BorrowTree.locationStateAt, watchAt, bind, Option.bind_some, pure, Option.pure_def,
          show next.perms.get watch = some state from stored, Option.getD_some]
      rw [after] at access
      cases old : segment.data.perms.get watch with
      | none =>
        have initial : tree.locationStateAt segment.data watch = some watchNode.defaultLocationState := by
          simp only [BorrowTree.locationStateAt, watchAt, bind, Option.bind_some, pure, Option.pure_def, old, Option.getD_none]
        rw [initial] at access
        exact False.elim (Bool.noConfusion (active.symm.trans (Option.some.inj access)))
      | some oldState =>
        have initial : tree.locationStateAt segment.data watch = some oldState := by
          simp only [BorrowTree.locationStateAt, watchAt, bind, Option.bind_some, pure, Option.pure_def, old, Option.getD_some]
        rw [initial] at access
        exact prior.1 _ old ((Option.some.inj access).symm.trans active)
    · exact ⟨by omega,by omega⟩
  have ran := preserve_range_property_with_byte_frame tree tag actor tags kind .VisitChildrenOfAccessed
    offset length offset.bytes (offset.bytes+length.bytes) (fun _ => True) found coherent.ranges bounds
    (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ _ _ => True.intro) property ready stable authorized
  exact ⟨ran.1, ran.2.2.2.2.1, ran.2.2.1, ran.2.2.2.1,
    fun point position valid starts stops => (ran.2.2.2.2.2 point position valid starts stops).1,
    fun point position valid starts stops => (ran.2.2.2.2.2 point position valid starts stops).2⟩

#print axioms eventsPreserveAccessed
#print axioms normalKeepsAccessed
#print axioms rangeKeepsWatch
end DuplicatePrefix.NonemptyReturnWatch

import duplicate_prefix.SharedHolderAttach
import duplicate_prefix.NonemptyReturnWatch

namespace DuplicatePrefix.NonemptyReturnWatch

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open MutableSliceRights SourceDomain GeneralRangeMapOrigins RetagLocationFrame ArchiveForestProjection
open Miri.Verification.MutableRetagFootprint
open SharedRelease

set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Keep an older writer's rights at a byte outside a new child's footprint.
A dormant default foreign state works even while the new protector is live. -/
theorem attachKeepsOutsideByte {before after : BorrowTree} {parent child holder : UniIndex}
    {grant : UInt64 → LocationState → Prop}
    (attachment : Attachment before after parent child)
    (holderPresent : ∃ node, before.nodeAt holder = some node)
    (oldTags newTags : ProtectedTags) (point : UInt64) (location : LocationTree)
    (footprint : ByteFrameAt grant before.locations child point location)
    (owners : ∀ prior, ValueAt before.locations point prior → LocationRights before prior oldTags holder)
    (newAbsent : location.perms.get child = none)
    (freshNode : ∀ node, after.nodeAt child = some node →
      foreignCompatible node.defaultLocationState (newTags.contains node.tag))
    (preserved : ∀ index node, index ≠ child → after.nodeAt index = some node →
      ∃ prior, before.nodeAt index = some prior ∧ node.defaultInitialPermission = prior.defaultInitialPermission ∧
        newTags.contains node.tag = oldTags.contains prior.tag) :
    LocationRights after location newTags holder := by
  obtain ⟨holderNode, held⟩ := holderPresent
  have distinct : holder ≠ child := by
    intro same
    rw [same, attachment.fresh] at held
    contradiction
  obtain ⟨⟨initial, atByte, saved⟩, _⟩ := footprint
  have oldOwned := owners initial atByte
  intro index node present
  by_cases new : index = child
  · subst index
    refine ⟨node.defaultLocationState, ?_, fun path =>
      False.elim (((holder_ancestry attachment distinct).1 path).2 rfl), fun _ => freshNode node present⟩
    simp [BorrowTree.locationStateAt, present, newAbsent]
  · obtain ⟨oldNode, oldPresent, defaultSame, heldSame⟩ := preserved index node new present
    obtain ⟨oldState, prior, localRight, foreignRight⟩ := oldOwned index oldNode oldPresent
    let current := (location.perms.get index).getD node.defaultLocationState
    have oldEq : oldState = (initial.perms.get index).getD oldNode.defaultLocationState := by
      simpa only [BorrowTree.locationStateAt, oldPresent, bind, Option.bind_some, pure, Option.pure_def, Option.some.injEq]
        using prior.symm
    have sameFields := effective_permission initial location oldNode node index defaultSame (saved index new)
    have permission : current.permission = oldState.permission := by rw [oldEq]; exact sameFields.1
    have accessed : current.accessed = oldState.accessed := by rw [oldEq]; exact sameFields.2
    refine ⟨current, ?_, ?_, ?_⟩
    · simp [BorrowTree.locationStateAt, current, present]
    · intro above
      have oldPath := ((holder_ancestry attachment distinct).1 above).1
      rw [heldSame]
      apply (localOwns_iff current _).mpr
      apply (MutableReferenceRights.sifa_irrelevant oldState current permission accessed _ _).mpr
      exact (localOwns_iff oldState _).mp (localRight oldPath)
    · intro away
      have oldAway : ¬ Ancestor before index holder := fun above => away ((holder_ancestry attachment distinct).2 above)
      rw [heldSame]
      apply (foreignCompatible_iff current _).mpr
      apply (MutableReferenceRights.sifa_irrelevant oldState current permission accessed _ _).mpr
      exact (foreignCompatible_iff oldState _).mp (foreignRight oldAway)

/-- Attaching a child retains every older node's active extent, allowing
stored permission rows whose accessed bit is false outside that extent. -/
theorem attachKeepsActiveScope {before after : BorrowTree} {child watch : UniIndex}
    {grant : UInt64 → LocationState → Prop}
    (frame : FramedAt grant before.locations child after)
    (different : watch ≠ child) (lo hi : UInt64) (scope : AccessedWithin before watch lo hi) :
    AccessedWithin after watch lo hi := by
  intro point position bounded lower upper state stored active
  obtain ⟨⟨prior, located, unchanged⟩, _⟩ := frame.2.2 point position bounded lower upper
  have entry := unchanged watch different
  unfold storedPermission at entry
  rw [stored] at entry
  cases old : prior.perms.get watch with
  | none =>
    rw [old, Option.map_none] at entry
    contradiction
  | some oldState =>
    have oldActive : oldState.accessed = true := by
      rw [old] at entry
      simp only [Option.map_some] at entry
      have same : state.accessed = oldState.accessed := congrArg Prod.snd (Option.some.inj entry)
      exact same.symm.trans active
    obtain ⟨oldPosition, valid, starts, stops, same⟩ := located
    exact scope point oldPosition valid (UInt64.le_iff_toNat_le.mpr starts) (UInt64.lt_iff_toNat_lt.mpr stops)
      oldState (by rwa [same]) oldActive

/-- The concrete shared and frozen mutable child constructors retain an
older writer’s byte grant and active footprint outside the retag extent. -/
theorem childKeepsWatch
    (tree : BorrowTree) (offset length : Size) (tags priorTags : ProtectedTags)
    (parentTag tag : BorTag) (parent child watch writer : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState)
    (outside : Permission) (held : Bool) (validDefault : outside = .Frozen ∨ outside = .ReservedFrz false)
    (coherent : CoherentForest tree) (parentFound : tree.indexOfTag parentTag = some parent)
    (parentAt : tree.nodeAt parent = some parentNode) (fresh : tree.nodeAt child = none)
    (selected : tree.tagMapping.insert tag = .Inserted mapping child)
    (watchAt : ∃ data, tree.nodeAt watch = some data)
    (writerAt : ∃ data, tree.nodeAt writer = some data)
    (noAncestor : ¬ Ancestor tree watch parent)
    (stableTags : ∀ index data, tree.nodeAt index = some data → tags.contains data.tag = priorTags.contains data.tag)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ())
    {grant : UInt64 → LocationState → Prop}
    (shape : FramedAt grant tree.locations child (tree.newChild offset (.concrete parentTag) tag inside outside held).tree)
    (childExtent : RetagReleaseFootprint.MaterializedWithin (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
      child offset.bytes (offset.bytes + length.bytes))
    (lo hi : UInt64) (active : AccessedWithin tree watch lo hi)
    (observes : UInt64 → Prop)
    (outsideRights : RangeModifyLaw.EachByte tree.locations fun point row =>
      (point.toNat < offset.bytes.toNat ∨ (offset.bytes + length.bytes).toNat ≤ point.toNat) →
        observes point → LocationRights tree row priorTags writer) :
    let next := (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
    AccessedWithin next watch lo hi ∧ ¬ Ancestor next watch child ∧
      RangeModifyLaw.EachByte next.locations (fun point row =>
        (point.toNat < offset.bytes.toNat ∨ (offset.bytes + length.bytes).toNat ≤ point.toNat) →
        observes point → LocationRights next row tags writer) := by
  let next := (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
  have different : watch ≠ child := by
    obtain ⟨node, present⟩ := watchAt
    intro eq
    rw [eq, fresh] at present
    contradiction
  obtain ⟨attached, _⟩ := MutableSliceRetag.attachment tree offset parentTag tag parent child mapping
    inside outside held coherent selected parentFound parentNode parentAt fresh complete
  have saved := newChild_nodeMetadata tree offset parentTag tag parent child mapping inside outside held
    selected parentFound parentNode parentAt fresh complete
  have oldMetadata : ∀ index node, index ≠ child → next.nodeAt index = some node →
      ∃ previous, tree.nodeAt index = some previous ∧ node.defaultInitialPermission = previous.defaultInitialPermission ∧
        tags.contains node.tag = priorTags.contains previous.tag := by
    intro index node distinct found
    obtain ⟨previous, present, _⟩ := attached.newEdges index node distinct found
    have fields := saved index
    rw [ite_eq_right distinct] at fields
    change nodeMetadata next index = nodeMetadata tree index at fields
    unfold nodeMetadata at fields
    rw [found, present] at fields
    have identity := Option.some.inj fields
    have sameTag : node.tag = previous.tag := congrArg Prod.fst identity
    exact ⟨previous,present,congrArg (fun data => data.2.2) identity,
      by rw [sameTag]; exact stableTags index previous present⟩
  have newDefault : ∀ node, next.nodeAt child = some node →
      foreignCompatible node.defaultLocationState (tags.contains node.tag) := by
    intro node found
    have fields := saved child
    rw [ite_eq_left rfl] at fields
    change nodeMetadata next child = some (tag, some parent, outside) at fields
    unfold nodeMetadata at fields
    rw [found] at fields
    have initial : node.defaultInitialPermission = outside := congrArg (fun data => data.2.2) (Option.some.inj fields)
    unfold foreignCompatible TreeNode.defaultLocationState
    rw [initial]
    rcases validDefault with standalone | standalone <;> rw [standalone] <;> simp [LocationState.possible, Permission.isUnique]
  refine ⟨attachKeepsActiveScope shape different lo hi active, ?_, ?_⟩
  · intro path
    rcases (attached.ancestry).mp path with eq | old
    · exact different eq
    · exact noAncestor old
  · intro point position valid starts stops excluded watched
    let location := next.locations.entries[position].data
    have departure : location.perms.get child = none := by
      cases saved : location.perms.get child with
      | none => rfl
      | some state =>
        have inside := childExtent point position valid starts stops state saved
        exact False.elim (excluded.elim (fun h => by omega) (fun h => by omega))
    apply attachKeepsOutsideByte attached writerAt priorTags tags point location
      (shape.2.2 point position valid starts stops) _ departure newDefault oldMetadata
    intro previous prior
    obtain ⟨priorPos, priorBound, lower, upper, same⟩ := prior
    rw [← same]
    exact outsideRights point priorPos priorBound (UInt64.le_iff_toNat_le.mpr lower)
      (UInt64.lt_iff_toNat_lt.mpr upper) excluded watched

#print axioms attachKeepsOutsideByte
#print axioms attachKeepsActiveScope
#print axioms childKeepsWatch

end DuplicatePrefix.NonemptyReturnWatch

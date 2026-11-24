import duplicate_prefix.InheritedSharedRights

namespace DuplicatePrefix.SharedRelease

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open MutableSliceRights SourceDomain GeneralRangeMapOrigins RetagLocationFrame ArchiveForestProjection
open Miri.Verification.MutableRetagFootprint

/-- A holder already present before a fresh child attachment retains exactly
its old ancestry. In particular the new child is foreign to that holder. -/
theorem holder_ancestry {before after : BorrowTree} {parent child holder index : UniIndex}
    (attachment : Attachment before after parent child) (oldHolder : holder ≠ child) :
    (Ancestor after index holder → Ancestor before index holder ∧ index ≠ child) ∧
    (Ancestor before index holder → Ancestor after index holder) := by
  constructor
  · intro path
    induction path with
    | self => exact ⟨.self _, oldHolder⟩
    | parent _ node found edge ih =>
      obtain ⟨previous, distinct⟩ := ih oldHolder
      obtain ⟨prior, present, unchanged⟩ := attachment.newEdges _ node distinct found
      have retained := unchanged.trans edge
      exact ⟨.parent previous prior present retained,
        fun equal => attachment.noDangling _ prior present (equal ▸ retained)⟩
  · intro path
    induction path with
    | self => exact .self _
    | parent _ node found edge ih =>
      obtain ⟨next, present, unchanged⟩ := attachment.oldEdges _ node found
      exact .parent (ih oldHolder) next present (unchanged.trans edge)

/-- Attaching an unheld shared node preserves an existing mutable holder's
byte rights. The same proof describes the prospective rights under a map
with a just-created shared protector removed. -/
theorem retained_holder_byte {before after : BorrowTree} {parent child holder : UniIndex}
    (attachment : Attachment before after parent child)
    (holderPresent : ∃ node, before.nodeAt holder = some node)
    (oldTags newTags : ProtectedTags) (point : UInt64) (location : LocationTree)
    (footprint : ByteFrameWith (fun state => state.permission = .Frozen ∧ state.accessed = true)
      before.locations child point location)
    (owners : ∀ prior, ValueAt before.locations point prior → LocationRights before prior oldTags holder)
    (freshNode : ∀ node, after.nodeAt child = some node →
      node.defaultInitialPermission = .Frozen ∧ newTags.contains node.tag = false)
    (preserved : ∀ index node, index ≠ child → after.nodeAt index = some node →
      ∃ prior, before.nodeAt index = some prior ∧ node.defaultInitialPermission = prior.defaultInitialPermission ∧
        newTags.contains node.tag = oldTags.contains prior.tag) :
    LocationRights after location newTags holder := by
  obtain ⟨holderNode, held⟩ := holderPresent
  have distinct : holder ≠ child := by
    intro same
    rw [same, attachment.fresh] at held
    contradiction
  obtain ⟨⟨initial, atByte, saved⟩, newGrant⟩ := footprint
  have oldOwned := owners initial atByte
  intro index node present
  by_cases new : index = child
  · subst index
    have childFields := freshNode node present
    let current := (location.perms.get child).getD node.defaultLocationState
    refine ⟨current, ?_, fun path => False.elim (((holder_ancestry attachment distinct).1 path).2 rfl), ?_⟩
    · simp [BorrowTree.locationStateAt, current, present]
    · intro _
      refine ⟨?_, Or.inl childFields.2⟩
      unfold current
      cases materialized : location.perms.get child
      · simp [TreeNode.defaultLocationState, childFields.1, LocationState.possible, Permission.isUnique]
      · have frozen := (newGrant _ materialized).1
        simp [frozen, LocationState.possible, Permission.isUnique]
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

/-- The actual fresh shared child leaves every overlapping row available to
the old mutable holder under the supplied post-release protector map. -/
theorem retained_holder_after_shared_child
    (tree : BorrowTree) (offset : Size) (parentTag tag : BorTag) (parent child holder : UniIndex)
    (parentNode : TreeNode) (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState)
    (held : Bool) (coherent : CoherentForest tree)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (holderPresent : ∃ node, tree.nodeAt holder = some node)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).outcome = .ok ())
    (frame : FramedWith (fun state => state.permission = .Frozen ∧ state.accessed = true)
      tree.locations child (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree)
    (oldTags newTags : ProtectedTags) (freshUnheld : newTags.contains tag = false)
    (stable : ∀ index node, tree.nodeAt index = some node → newTags.contains node.tag = oldTags.contains node.tag)
    (lower upper : UInt64)
    (owned : OwnedOn (fun row => LocationRights tree row oldTags holder) lower upper tree.locations) :
    let next := (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree
    OwnedOn (fun row => LocationRights next row newTags holder) lower upper next.locations := by
  let next := (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).tree
  have attachment := (MutableSliceRetag.attachment tree offset parentTag tag parent child mapping inside
    .Frozen held coherent mapped parentFound parentNode present vacant complete).1
  have metadata := newChild_nodeMetadata tree offset parentTag tag parent child mapping inside .Frozen held
    mapped parentFound parentNode present vacant complete
  have newFields : ∀ node, next.nodeAt child = some node →
      node.defaultInitialPermission = .Frozen ∧ newTags.contains node.tag = false := by
    intro node found
    have childMetadata := metadata child
    rw [ite_eq_left (Eq.refl child)] at childMetadata
    change nodeMetadata next child = some (tag, some parent, .Frozen) at childMetadata
    unfold nodeMetadata at childMetadata
    rw [found] at childMetadata
    have fields := Option.some.inj childMetadata
    have tagEq : node.tag = tag := congrArg Prod.fst fields
    exact ⟨congrArg (fun row => row.2.2) fields, by simpa only [tagEq] using freshUnheld⟩
  have kept : ∀ index node, index ≠ child → next.nodeAt index = some node →
      ∃ old, tree.nodeAt index = some old ∧ node.defaultInitialPermission = old.defaultInitialPermission ∧
        newTags.contains node.tag = oldTags.contains old.tag := by
    intro index node different found
    obtain ⟨old, oldFound, _⟩ := attachment.newEdges index node different found
    have row := metadata index
    rw [ite_eq_right different] at row
    change nodeMetadata next index = nodeMetadata tree index at row
    unfold nodeMetadata at row
    rw [found, oldFound] at row
    have fields := Option.some.inj row
    have tagEq : node.tag = old.tag := congrArg Prod.fst fields
    exact ⟨old, oldFound, congrArg (fun row => row.2.2) fields, by simpa only [tagEq] using stable index old oldFound⟩
  change OwnedOn (fun row => LocationRights next row newTags holder) lower upper next.locations
  intro position valid positive starts ends
  have notEmpty : next.locations.entries.size ≠ 0 := by omega
  have table := frame.2.1
  change next.locations.WellFormed at table
  simp only [DedupRangeMap.WellFormed, notEmpty, ↓reduceDIte] at table
  let row := next.locations.entries[position]
  have proper : row.range.start.toNat < row.range.stop.toNat := UInt64.lt_iff_toNat_lt.mp (table.2.1 position valid)
  let point := if lower.toNat ≤ row.range.start.toNat then row.range.start else lower
  have lo : lower.toNat ≤ point.toNat := by unfold point; split <;> omega
  have hi : point.toNat < upper.toNat := by
    change row.range.start.toNat < upper.toNat at starts
    unfold point
    split <;> omega
  have rowLo : row.range.start.toNat ≤ point.toNat := by unfold point; split <;> omega
  have rowHi : point.toNat < row.range.stop.toNat := by
    change lower.toNat < row.range.stop.toNat at ends
    unfold point
    split <;> omega
  have rowFrame := frame.2.2 point position valid (UInt64.le_iff_toNat_le.mpr rowLo) (UInt64.lt_iff_toNat_lt.mpr rowHi)
  apply retained_holder_byte attachment holderPresent oldTags newTags point row.data rowFrame _ newFields kept
  intro prior located
  obtain ⟨oldPosition, oldBound, before, after, exact⟩ := located
  rw [← exact]
  exact owned oldPosition oldBound positive (by omega) (by omega)

#print axioms retained_holder_byte

end DuplicatePrefix.SharedRelease

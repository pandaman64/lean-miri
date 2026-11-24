import MutableSliceRetag
import duplicate_prefix.RetagLocationFrame

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open DuplicatePrefix.MutableSliceRights DuplicatePrefix.SourceDomain
open DuplicatePrefix.RetagLocationFrame DuplicatePrefix.GeneralRangeMapOrigins
open Miri.Verification.MutableRetagFootprint

private theorem effective_permission
    (before after : LocationTree) (oldNode newNode : TreeNode) (index : UniIndex)
    (defaultPermission : newNode.defaultInitialPermission = oldNode.defaultInitialPermission)
    (preserved : storedPermission after index = storedPermission before index) :
    let old := (before.perms.get index).getD oldNode.defaultLocationState
    let new := (after.perms.get index).getD newNode.defaultLocationState
    new.permission = old.permission ∧ new.accessed = old.accessed := by
  unfold storedPermission at preserved
  cases oldValue : before.perms.get index <;> cases newValue : after.perms.get index
  · simp [TreeNode.defaultLocationState, defaultPermission]
  · simp [oldValue, newValue] at preserved
  · simp [oldValue, newValue] at preserved
  · simp [oldValue, newValue] at preserved ⊢
    exact preserved

/-- The child updates the global protection map only in held mode. -/
def childProtections (tags : ProtectedTags) (fresh : BorTag) (held : Bool) : ProtectedTags :=
  if held then tags.insert fresh .StrongProtector else tags

private theorem preserves_old_protection (tags : ProtectedTags) (old fresh : BorTag) (held : Bool)
    (different : old ≠ fresh) :
    (childProtections tags fresh held).contains old = tags.contains old := by
  cases held
  · rfl
  · exact MutableReferenceRights.contains_insert_other tags fresh old .StrongProtector different

private theorem local_grant_of_held (state : LocationState) (held : Bool)
    (grant : MutableReferenceRights.Granted state .LocalAccess true) :
    MutableReferenceRights.Granted state .LocalAccess held := by
  cases held
  · rcases state with ⟨permission, accessed, sifa⟩
    cases permission
    case ReservedFrz conflict =>
      cases conflict <;> simp_all [MutableReferenceRights.Granted, MutableReferenceRights.LocalWrite]
    all_goals simp_all [MutableReferenceRights.Granted, MutableReferenceRights.LocalWrite]
  · exact grant

/-- The exact byte footprint of a new frozen child transports
the caller's effective permission through materialized rows and lazy defaults. -/
theorem inherit_frozen_byte_with_mode {before after : BorrowTree} {parent child : UniIndex}
    (attachment : Attachment before after parent child)
    (tags : ProtectedTags) (fresh : BorTag) (held : Bool) (point : UInt64) (location : LocationTree)
    (footprint : ByteFrame before.locations child point location)
    (owners : ∀ prior, ValueAt before.locations point prior → OwnsByte before prior tags parent)
    (freshNode : ∀ node, after.nodeAt child = some node →
      node.tag = fresh ∧ node.defaultInitialPermission = .ReservedFrz false)
    (preserved : ∀ index node, index ≠ child → after.nodeAt index = some node →
      ∃ prior, before.nodeAt index = some prior ∧ prior.tag = node.tag ∧ node.tag ≠ fresh ∧
        node.defaultInitialPermission = prior.defaultInitialPermission) :
    OwnsByte after location (childProtections tags fresh held) child := by
  obtain ⟨⟨initial, wasAtByte, frame⟩, childGrant⟩ := footprint
  have owned := owners initial wasAtByte
  intro index node present
  by_cases newChild : index = child
  · subst index
    have fields := freshNode node present
    let current := (location.perms.get child).getD node.defaultLocationState
    refine ⟨current, ?_, ?_, fun foreign => False.elim (foreign (.self _))⟩
    · simp [BorrowTree.locationStateAt, present, current]
    · intro _
      unfold current
      cases materialized : location.perms.get child
      · simp [MutableReferenceRights.Granted, MutableReferenceRights.LocalWrite,
          LocationState.possible, Permission.isUnique, TreeNode.defaultLocationState,
          fields.2]
      · exact local_grant_of_held _ _ (childGrant _ materialized)
  · obtain ⟨priorNode, priorPresent, sameTag, differentTag, sameDefault⟩ :=
      preserved index node newChild present
    obtain ⟨prior, priorValue, localOwn, foreignOwn⟩ := owned index priorNode priorPresent
    let current := (location.perms.get index).getD node.defaultLocationState
    have priorIs : prior = (initial.perms.get index).getD priorNode.defaultLocationState := by
      simpa only [BorrowTree.locationStateAt, priorPresent, bind, Option.bind_some, pure, Option.pure_def, Option.some.injEq]
        using priorValue.symm
    have pair := effective_permission initial location priorNode node index sameDefault (frame index newChild)
    have samePermission : current.permission = prior.permission := by rw [priorIs]; exact pair.1
    have sameAccess : current.accessed = prior.accessed := by rw [priorIs]; exact pair.2
    have protector := preserves_old_protection tags node.tag fresh held differentTag
    refine ⟨current, ?_, ?_, ?_⟩
    · simp [BorrowTree.locationStateAt, present, current]
    · intro lineage
      rw [protector, ← sameTag]
      apply (MutableReferenceRights.sifa_irrelevant prior current samePermission sameAccess _ _).mpr
      exact localOwn ((attachment.ancestry.mp lineage).resolve_left newChild)
    · intro unrelated
      rw [protector, ← sameTag]
      apply (MutableReferenceRights.sifa_irrelevant prior current samePermission sameAccess _ _).mpr
      exact foreignOwn (fun lineage => unrelated (attachment.ancestry.mpr (.inr lineage)))

theorem inherit_frozen_byte {before after : BorrowTree} {parent child : UniIndex}
    (attachment : Attachment before after parent child)
    (tags : ProtectedTags) (fresh : BorTag) (point : UInt64) (location : LocationTree)
    (footprint : ByteFrame before.locations child point location)
    (owners : ∀ prior, ValueAt before.locations point prior → OwnsByte before prior tags parent)
    (freshNode : ∀ node, after.nodeAt child = some node →
      node.tag = fresh ∧ node.defaultInitialPermission = .ReservedFrz false)
    (preserved : ∀ index node, index ≠ child → after.nodeAt index = some node →
      ∃ prior, before.nodeAt index = some prior ∧ prior.tag = node.tag ∧ node.tag ≠ fresh ∧
        node.defaultInitialPermission = prior.defaultInitialPermission) :
    OwnsByte after location (tags.insert fresh .StrongProtector) child :=
  inherit_frozen_byte_with_mode attachment tags fresh true point location footprint owners freshNode preserved

/-- The actual frozen child installation transfers all admitted raw byte
grants, independently of the source partition and prior caller history. -/
theorem installed_frozen_rights_with_mode (tree : BorrowTree) (offset : Size)
    (protections : ProtectedTags) (parentTag tag : BorTag)
    (parent child : UniIndex) (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState) (held : Bool)
    (coherent : CoherentForest tree)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (freshRows : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get child = none)
    (fit : ∀ segment ∈ inside.iterAll.toList, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      start.bytes.toNat + (segment.range.stop - segment.range.start).toNat ≤ tree.locations.size.bytes.toNat)
    (insideRights : ∀ segment ∈ inside.iterAll.toList, MutableReferenceRights.Granted segment.data .LocalAccess true)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).outcome = .ok ())
    (lower upper : UInt64)
    (owned : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      ∀ prior, ValueAt tree.locations point prior → OwnsByte tree prior protections parent) :
    let next := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
    next.locations.size = tree.locations.size ∧ next.locations.WellFormed ∧
      ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
        ∀ location, ValueAt next.locations point location →
          OwnsByte next location (childProtections protections tag held) child := by
  let next := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
  obtain ⟨attachment, _⟩ := DuplicatePrefix.MutableSliceRetag.attachment tree offset parentTag tag parent child
    mapping inside (.ReservedFrz false) held coherent mapped parentFound parentNode present vacant complete
  have framed := newChild_framed tree offset parentTag tag parent child mapping inside (.ReservedFrz false) held
    mapped parentFound parentNode present vacant coherent.ranges freshRows fit insideRights complete
  have entries := MutableRetagFootprint.newChild_nodeMetadata tree offset parentTag tag parent child
    mapping inside (.ReservedFrz false) held mapped parentFound parentNode present vacant complete
  refine ⟨framed.1, framed.2.1, ?_⟩
  intro point lowerBound upperBound location actual
  obtain ⟨pos, valid, lo, hi, atLocation⟩ := actual
  have atByte := framed.2.2 point pos valid (UInt64.le_iff_toNat_le.mpr lo) (UInt64.lt_iff_toNat_lt.mpr hi)
  rw [atLocation] at atByte
  apply inherit_frozen_byte_with_mode attachment protections tag held point location atByte
    (owned point lowerBound upperBound)
  · intro node found
    have equation := entries child
    change MutableRetagFootprint.nodeMetadata next child = _ at equation
    change next.nodeAt child = some node at found
    simp only [MutableRetagFootprint.nodeMetadata, found, Option.map_some] at equation
    have shape := Option.some.inj equation
    exact ⟨congrArg Prod.fst shape, congrArg (fun row => row.2.2) shape⟩
  · intro index node distinct found
    obtain ⟨prior, priorFound, _⟩ := attachment.newEdges index node distinct found
    have equation := entries index
    change MutableRetagFootprint.nodeMetadata next index = _ at equation
    change next.nodeAt index = some node at found
    simp only [MutableRetagFootprint.nodeMetadata, found, priorFound, Option.map_some, ite_eq_right distinct] at equation
    have fields := Option.some.inj equation
    exact ⟨prior, priorFound, (congrArg Prod.fst fields).symm,
      fun same => fresh index prior priorFound ((congrArg Prod.fst fields).symm.trans same),
      congrArg (fun row => row.2.2) fields⟩

theorem installed_frozen_rights (tree : BorrowTree) (offset : Size)
    (protections : ProtectedTags) (parentTag tag : BorTag)
    (parent child : UniIndex) (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState)
    (coherent : CoherentForest tree)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag)
    (freshRows : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get child = none)
    (fit : ∀ segment ∈ inside.iterAll.toList, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      start.bytes.toNat + (segment.range.stop - segment.range.start).toNat ≤ tree.locations.size.bytes.toNat)
    (insideRights : ∀ segment ∈ inside.iterAll.toList, MutableReferenceRights.Granted segment.data .LocalAccess true)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) true).outcome = .ok ())
    (lower upper : UInt64)
    (owned : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      ∀ prior, ValueAt tree.locations point prior → OwnsByte tree prior protections parent) :
    let next := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) true).tree
    next.locations.size = tree.locations.size ∧ next.locations.WellFormed ∧
      ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
        ∀ location, ValueAt next.locations point location →
          OwnsByte next location (protections.insert tag .StrongProtector) child :=
  installed_frozen_rights_with_mode tree offset protections parentTag tag parent child mapping inside true
    coherent mapped parentFound parentNode present vacant fresh freshRows fit insideRights complete lower upper owned

#print axioms inherit_frozen_byte
#print axioms installed_frozen_rights
end DuplicatePrefix.ArchiveForestProjection

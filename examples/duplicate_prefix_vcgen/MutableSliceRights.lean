import SourceDomain
import Miri.Verification.MutableReferenceRights

namespace DuplicatePrefix.MutableSliceRights

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open DuplicatePrefix.SourceDomain

theorem localOwns_iff (state : LocationState) (held : Bool) :
    localOwns state held ↔ MutableReferenceRights.Granted state .LocalAccess held := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission
  case ReservedFrz conflicted => cases conflicted <;>
    simp [localOwns, MutableReferenceRights.Granted, MutableReferenceRights.LocalWrite]
  all_goals simp [localOwns, MutableReferenceRights.Granted, MutableReferenceRights.LocalWrite]

theorem foreignCompatible_iff (state : LocationState) (held : Bool) :
    foreignCompatible state held ↔ MutableReferenceRights.Granted state .ForeignAccess held := by
  simp [foreignCompatible, MutableReferenceRights.Granted, MutableReferenceRights.ForeignWrite, or_assoc]

/-- Source-domain rights at an actual byte location feed the same predicate
that is preserved by the normal traversal for either access kind. -/
theorem grants_at {K U : Type} {before : MachineHooks.State K U} {length : UInt64}
    {storage : DuplicatePrefix.PreparedArguments.InitializedRegion before length} {tag : BorTag}
    (region : ExclusiveRegion before length storage tag)
    (distance : Nat) (within : distance < length.toNat)
    (segment : RangeMapSegment LocationTree) (member : segment ∈ storage.entry.allocation.extra.locations.entries)
    (start : segment.range.start.toNat ≤ storage.relativeStart.bytes.toNat + distance)
    (stop : storage.relativeStart.bytes.toNat + distance < segment.range.stop.toNat)
    (index : UniIndex) (node : TreeNode)
    (present : storage.entry.allocation.extra.nodeAt index = some node) :
    ∃ state, storage.entry.allocation.extra.locationStateAt segment.data index = some state ∧
      (Ancestor storage.entry.allocation.extra index region.source →
        MutableReferenceRights.Granted state .LocalAccess (region.tracker.global.protectedTags.contains node.tag)) ∧
      (¬ Ancestor storage.entry.allocation.extra index region.source →
        MutableReferenceRights.Granted state .ForeignAccess (region.tracker.global.protectedTags.contains node.tag)) := by
  obtain ⟨state, found, localRight, foreignRight⟩ :=
    region.exclusive distance within segment member start stop index node present
  exact ⟨state, found, fun ancestor => (localOwns_iff _ _).mp (localRight ancestor),
    fun foreign => (foreignCompatible_iff _ _).mp (foreignRight foreign)⟩

/-- Structural footprint of a concrete fresh-child attachment. Retag may
change child arrays and SIFA metadata on old nodes, while retaining their
parent edges. The old graph rules out dangling edges to the fresh index. -/
structure Attachment (old new : BorrowTree) (parent child : UniIndex) : Prop where
  fresh : old.nodeAt child = none
  parentPresent : ∃ node, old.nodeAt parent = some node
  childParent : ∃ node, new.nodeAt child = some node ∧ node.parent = some parent
  oldEdges : ∀ index node, old.nodeAt index = some node →
    ∃ next, new.nodeAt index = some next ∧ next.parent = node.parent
  newEdges : ∀ index node, index ≠ child → new.nodeAt index = some node →
    ∃ prev, old.nodeAt index = some prev ∧ prev.parent = node.parent
  noDangling : ∀ index node, old.nodeAt index = some node → node.parent ≠ some child

private theorem Attachment.oldPath {old new : BorrowTree} {parent child cursor source : UniIndex}
    (attachment : Attachment old new parent child)
    (path : Ancestor old cursor source) : Ancestor new cursor source := by
  induction path with
  | self => exact .self _
  | parent _ node found edge ih =>
    obtain ⟨next, present, unchanged⟩ := attachment.oldEdges _ node found
    exact .parent ih next present (unchanged.trans edge)

private theorem Attachment.recoverPath {old new : BorrowTree} {parent child cursor source : UniIndex}
    (attachment : Attachment old new parent child)
    (path : Ancestor new cursor source) (different : source ≠ child) :
    Ancestor old cursor source ∧ cursor ≠ child := by
  induction path with
  | self => exact ⟨.self _, different⟩
  | parent _ node found edge ih =>
    obtain ⟨priorPath, freshCursor⟩ := ih different
    obtain ⟨prior, present, unchanged⟩ := attachment.newEdges _ node freshCursor found
    have oldEdge := unchanged.trans edge
    exact ⟨.parent priorPath prior present oldEdge, fun equal =>
      attachment.noDangling _ prior present (equal ▸ oldEdge)⟩

private theorem Attachment.pathFromChild
    {old new : BorrowTree} {parent child cursor source : UniIndex}
    (attachment : Attachment old new parent child)
    (different : parent ≠ child)
    (childNode : TreeNode) (childPresent : new.nodeAt child = some childNode)
    (parentEdge : childNode.parent = some parent)
    (path : Ancestor new cursor source) :
    source = child → cursor = child ∨ Ancestor old cursor parent := by
  induction path with
  | self node => exact fun equal => Or.inl equal
  | parent _ node found edge ih =>
    intro root
    rcases ih root with fresh | above
    · rw [fresh, childPresent] at found
      cases found
      rw [parentEdge] at edge
      cases edge
      exact Or.inr (.self _)
    · have oldSource := attachment.oldPath above
      have longPath := Ancestor.parent oldSource node found edge
      exact Or.inr (attachment.recoverPath longPath different).1

private theorem appendPath {tree : BorrowTree} {index pivot origin : UniIndex}
    (upper : Ancestor tree index pivot) (lower : Ancestor tree pivot origin) :
    Ancestor tree index origin := by
  induction upper with
  | self => exact lower
  | parent _ node found edge ih => exact .parent (ih lower) node found edge

/-- An actual parent edge extension gives the child precisely the old
parent's ancestor chain, including its own new index. -/
theorem Attachment.ancestry {old new : BorrowTree} {parent child index : UniIndex}
    (attachment : Attachment old new parent child) :
    Ancestor new index child ↔ index = child ∨ Ancestor old index parent := by
  obtain ⟨parentNode, present⟩ := attachment.parentPresent
  have different : parent ≠ child := by
    intro same
    rw [same, attachment.fresh] at present
    contradiction
  obtain ⟨childNode, childPresent, parentEdge⟩ := attachment.childParent
  constructor
  · intro path
    exact attachment.pathFromChild different childNode childPresent parentEdge path rfl
  · intro path
    rcases path with same | above
    · subst index
      exact .self _
    · have first : Ancestor new parent child := .parent (.self _) childNode childPresent parentEdge
      exact appendPath (attachment.oldPath above) first

/-- Exclusive ownership at a byte, checked against the tag's actual
ancestry and live protectors. -/
def OwnsByte (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (source : UniIndex) : Prop :=
  ∀ index node, tree.nodeAt index = some node →
    ∃ state, tree.locationStateAt location index = some state ∧
      (Ancestor tree index source →
        MutableReferenceRights.Granted state .LocalAccess (tags.contains node.tag)) ∧
      (¬ Ancestor tree index source →
        MutableReferenceRights.Granted state .ForeignAccess (tags.contains node.tag))

/-- The freshly protected child inherits the caller's rights at a frozen
byte. The footprint links the real before and after nodes and permissions,
allowing retag to weaken SIFA and to extend child arrays. -/
theorem Attachment.frozenByte {old new : BorrowTree} {parent child : UniIndex}
    (attachment : Attachment old new parent child)
    (before after : LocationTree) (tags : ProtectedTags)
    (fresh : Miri.Memory.BorTag) (policy : RetagPolicy.NewPermission) (state : LocationState)
    (initial : RetagPolicy.initialLocationState policy true = .ok state)
    (contract : ∃ config, RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry config = some policy)
    (stored : new.locationStateAt after child = some state)
    (childTag : ∀ node, new.nodeAt child = some node → node.tag = fresh)
    (preserved : ∀ index node, index ≠ child → new.nodeAt index = some node →
      ∃ prev prior next, old.nodeAt index = some prev ∧
        prev.tag = node.tag ∧ node.tag ≠ fresh ∧
        old.locationStateAt before index = some prior ∧
        new.locationStateAt after index = some next ∧
        next.permission = prior.permission ∧ next.accessed = prior.accessed)
    (rights : OwnsByte old before tags parent) :
    OwnsByte new after (tags.insert fresh .StrongProtector) child := by
  intro index node found
  by_cases isChild : index = child
  · subst index
    obtain ⟨config, selected⟩ := contract
    obtain ⟨expected, init, created, _, installed, granted⟩ :=
      MutableReferenceRights.entry_grants config
    rw [selected] at created
    cases created
    rw [initial] at installed
    cases installed
    refine ⟨state, stored, ?_, fun denied => False.elim (denied (.self _))⟩
    intro _
    simpa [childTag node found, ProtectedTags.contains] using granted
  · obtain ⟨prev, prior, next, priorNode, tag, different, priorStored, nextStored, perm, accessed⟩ :=
      preserved index node isChild found
    obtain ⟨actual, actualStored, localRight, foreignRight⟩ := rights index prev priorNode
    rw [priorStored] at actualStored
    cases actualStored
    have protector := MutableReferenceRights.contains_insert_other tags fresh node.tag
      .StrongProtector different
    refine ⟨next, nextStored, ?_, ?_⟩
    · intro ancestor
      rw [protector, ← tag]
      apply (MutableReferenceRights.sifa_irrelevant prior next perm accessed _ _).mpr
      exact localRight ((attachment.ancestry.mp ancestor).resolve_left isChild)
    · intro foreign
      rw [protector, ← tag]
      apply (MutableReferenceRights.sifa_irrelevant prior next perm accessed _ _).mpr
      exact foreignRight (fun ancestor => foreign (attachment.ancestry.mpr (.inr ancestor)))

end DuplicatePrefix.MutableSliceRights

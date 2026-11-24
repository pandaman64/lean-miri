import duplicate_prefix.NormalAccessRights
import MutableSliceRetag
import duplicate_prefix.RetagLocationFrame

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open DuplicatePrefix.MutableSliceRights DuplicatePrefix.SourceDomain
open DuplicatePrefix.RetagLocationFrame DuplicatePrefix.GeneralRangeMapOrigins
open Miri.Verification.MutableRetagFootprint

theorem effective_permission
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

theorem inherit_shared_read {before after : BorrowTree} {parent child : UniIndex}
    (attachment : Attachment before after parent child)
    (tags : ProtectedTags) (fresh : BorTag) (point : UInt64) (location : LocationTree)
    (footprint : ByteFrameWith (fun state => state.permission = .Frozen ∧ state.accessed = true) before.locations child point location)
    (owners : ∀ prior, ValueAt before.locations point prior → LocationAccessRights before prior tags parent .Read)
    (freshNode : ∀ node, after.nodeAt child = some node →
      node.tag = fresh ∧ node.defaultInitialPermission = .Frozen)
    (preserved : ∀ index node, index ≠ child → after.nodeAt index = some node →
      ∃ prior, before.nodeAt index = some prior ∧ prior.tag = node.tag ∧
        node.defaultInitialPermission = prior.defaultInitialPermission) :
    LocationAccessRights after location tags child .Read := by
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
      · simp [GeneralBorrowPermissions.AccessOwned, GeneralBorrowPermissions.LocalReadable,
          LocationState.possible, Permission.isUnique, TreeNode.defaultLocationState, fields.2]
      · have frozen := (childGrant _ materialized).1
        simp [GeneralBorrowPermissions.AccessOwned, GeneralBorrowPermissions.LocalReadable,
          LocationState.possible, Permission.isUnique, frozen]
  · obtain ⟨priorNode, priorPresent, sameTag, sameDefault⟩ :=
      preserved index node newChild present
    obtain ⟨prior, priorValue, localOwn, foreignOwn⟩ := owned index priorNode priorPresent
    let current := (location.perms.get index).getD node.defaultLocationState
    have priorIs : prior = (initial.perms.get index).getD priorNode.defaultLocationState := by
      simpa only [BorrowTree.locationStateAt, priorPresent, bind, Option.bind_some, pure, Option.pure_def, Option.some.injEq]
        using priorValue.symm
    have pair := effective_permission initial location priorNode node index sameDefault (frame index newChild)
    have samePermission : current.permission = prior.permission := by rw [priorIs]; exact pair.1
    have sameAccess : current.accessed = prior.accessed := by rw [priorIs]; exact pair.2
    refine ⟨current, ?_, ?_, ?_⟩
    · simp [BorrowTree.locationStateAt, present, current]
    · intro lineage
      rw [← sameTag]
      have read := localOwn ((attachment.ancestry.mp lineage).resolve_left newChild)
      simp only [GeneralBorrowPermissions.AccessOwned, GeneralBorrowPermissions.LocalReadable,
        LocationState.possible, samePermission, sameAccess] at read ⊢
      exact read
    · intro unrelated
      rw [← sameTag]
      have can := foreignOwn (fun lineage => unrelated (attachment.ancestry.mpr (.inr lineage)))
      apply (foreignCompatible_iff current _).mpr
      apply (MutableReferenceRights.sifa_irrelevant prior current samePermission sameAccess _ _).mpr
      exact (foreignCompatible_iff prior _).mp can

#print axioms inherit_shared_read
end DuplicatePrefix.ArchiveForestProjection

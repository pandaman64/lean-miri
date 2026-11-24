import AccessedOnlyAuthorize
import duplicate_prefix.CopyHolderRelease

namespace DuplicatePrefix.PhysicalSlotActiveRelease

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open SourceDomain ArchiveForestProjection RetagReleaseRights RetagReleaseFootprint GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem parent_path {tree : BorrowTree} {child parent cursor current : UniIndex}
    (node : TreeNode) (found : tree.nodeAt child = some node) (edge : node.parent = some parent)
    (path : Ancestor tree cursor current) :
    current = child → cursor = child ∨ Ancestor tree cursor parent := by
  induction path with
  | self index => exact Or.inl
  | parent previous childNode childFound parentEdge ih =>
    intro same
    rcases ih same with direct | priorPath
    · rw [direct,found] at childFound
      cases childFound
      rw [edge] at parentEdge
      cases parentEdge
      exact Or.inr (.self _)
    · exact Or.inr (.parent priorPath childNode childFound parentEdge)

/-- Actual strong release of the Bool slot child gives the saved direct
parent write permission at the same byte after removing that child's tag. -/
theorem release (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (child parent root : UniIndex) (node : TreeNode)
    (found : tree.nodeAt child = some node) (sameTag : node.tag = tag)
    (edge : node.parent = some parent) (hidden : node.isExposed = false)
    (key : tree.indexOfTag tag = some child)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (lower upper : UInt64) (extent : ScopedPhysicalRelease.VisitsWithin tree child lower.toNat upper.toNat) (vacant : VacantRows tree)
    (rights : OwnedOn (fun row => LocationRights tree row tags child) lower upper tree.locations) :
    ∃ after, tree.releaseProtector tag tags = ⟨after,.Released⟩ ∧
      after = {tree with locations := after.locations} ∧
      CoherentForest after ∧ after.locations.size = tree.locations.size ∧
      OwnedOn (fun row => LocationRights after row (tags.remove tag) parent) lower upper after.locations := by
  have active := ScopedPhysicalRelease.activeRights tree tags child lower upper coherent extent vacant rights
  obtain ⟨after, shape, formed, size, retained, checked⟩ :=
    release_retains_owned tree tag child root tags key coherent roots node found hidden active lower upper rights
  have success := (ProtectorReleaseWP.releasePre_iff tag tags (· = after) (fun _ _ => False) tree).mp
    ((checked _ _).mpr rfl)
  have released : tree.releaseProtector tag tags = ⟨after,.Released⟩ := by
    cases outcome : tree.releaseProtector tag tags with
    | mk result status =>
      rw [outcome] at success
      cases status <;>
        first | exact False.elim success | exact congrArg (fun t => BorrowTree.ProtectorReleaseResult.mk t .Released) success
  have sameNode : after.nodeAt child = some node := by
    have frame := congrArg (fun chosen : BorrowTree => chosen.nodeAt child) shape
    exact frame.trans found
  have lineage : Ancestor after parent child := .parent (.self child) node sameNode edge
  have unheld : ∀ index data, after.nodeAt index = some data →
      Ancestor after index child → ¬ Ancestor after index parent → (tags.remove tag).contains data.tag = false := by
    intro index data present childPath noParent
    rcases parent_path node sameNode edge childPath rfl with direct | contradiction
    · subst index
      have exactNode := Option.some.inj (present.symm.trans sameNode)
      cases exactNode
      rw [sameTag]
      simp [ProtectedTags.contains,ProtectedTags.get,ProtectedTags.remove]
    · exact False.elim (noParent contradiction)
  refine ⟨after,released,shape,formed,size,?_⟩
  intro position valid positive lo hi
  exact return_to_ancestor after _ (tags.remove tag) child parent lineage unheld
    (retained position valid positive lo hi)

end DuplicatePrefix.PhysicalSlotActiveRelease

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PhysicalSlotActiveRelease.release) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved physical slot release dependency {dependency}"

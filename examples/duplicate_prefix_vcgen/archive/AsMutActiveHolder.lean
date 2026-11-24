import duplicate_prefix.ActiveReleaseWatch
import duplicate_prefix.AccessedCopyHolderRights

namespace DuplicatePrefix.AsMutHolderScope

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open SourceDomain RetagReleaseRights RetagReleaseFootprint ArchiveForestProjection
open GeneralRangeMapOrigins NonemptyReturnWatch RetagReleaseFootprint

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The helper's actual scoped release preserves the caller's active slice
footprint. Dormant rows outside the original holder's scope are permitted. -/
theorem finishActive (tree : BorrowTree) (mask : ProtectedTags) (rawTag : BorTag)
    (source holder root : UniIndex) (start length : Size)
    (key : tree.indexOfTag rawTag = some source)
    (stage : RawHolderScope.ReleaseStage tree mask source root start length)
    (holderNode : TreeNode) (holderStored : tree.nodeAt holder = some holderNode)
    (holderScope : AccessedWithin tree holder start.bytes (start.bytes+length.bytes))
    (path : BetweenTags tree (mask.remove rawTag) holder source) :
    let actual := tree.releaseProtector rawTag mask
    actual.status = .Released ∧ actual.tree = {tree with locations := actual.tree.locations} ∧
      CoherentForest actual.tree ∧ actual.tree.locations.size = tree.locations.size ∧
      BetweenTags actual.tree (mask.remove rawTag) holder source ∧
      AccessedCopyHolderRights.Footprint actual.tree (mask.remove rawTag) source holder
        start.bytes (start.bytes+length.bytes) := by
  obtain ⟨node, found, unexposed⟩ := stage.hidden
  let lo := start.bytes
  let hi := start.bytes+length.bytes
  have active := active_of_footprint tree mask source lo hi stage.coherent stage.materialized stage.vacant stage.ownership
  obtain ⟨after, frame, good, size, rawOwned, yes⟩ :=
    release_retains_owned tree rawTag source root mask key stage.coherent stage.roots node found unexposed
      active lo hi stage.ownership
  obtain ⟨kept, _, clean, checks⟩ :=
    ScopedReleaseMaterialization.release_preserves_scope tree mask rawTag source root source lo hi node found key
      unexposed stage.coherent stage.roots stage.materialized stage.vacant stage.ownership stage.materialized
  have same : kept = after := (checks (· = after) (fun _ _ => False)).mp ((yes _ _).mpr rfl)
  subst kept
  have result := (ProtectorReleaseWP.releasePre_iff rawTag mask (· = after) (fun _ _ => False) tree).mp
    ((yes _ _).mpr rfl)
  have done : tree.releaseProtector rawTag mask = ⟨after,.Released⟩ := by
    cases outcome : tree.releaseProtector rawTag mask with
    | mk selected status =>
      rw [outcome] at result
      cases status <;> first | exact False.elim result |
        exact congrArg (fun t => BorrowTree.ProtectorReleaseResult.mk t .Released) result
  have nodes : tree.nodes = after.nodes := (congrArg BorrowTree.nodes frame).symm
  have continuation := path.sameNodes nodes
  have holderOwn : OwnedOn (fun row => LocationRights after row (mask.remove rawTag) holder) lo hi after.locations := by
    intro pos valid positive start stop
    exact return_to_ancestor after _ (mask.remove rawTag) source holder continuation.1 continuation.2
      (rawOwned pos valid positive start stop)
  have watched := ActiveReleaseOutside.keepsWatch tree mask rawTag source root holder start length key stage
    holderNode holderStored lo hi (.inr ⟨Nat.le_refl _,Nat.le_refl _⟩) holderScope (fun _ _ => True)
    (fun _ _ _ _ _ _ => True.intro)
  dsimp only at watched ⊢
  rw [done] at watched ⊢
  exact ⟨rfl,frame,good,size,continuation,rawOwned,holderOwn,watched.2.2.1,clean⟩

end DuplicatePrefix.AsMutHolderScope

#print axioms DuplicatePrefix.AsMutHolderScope.finishActive

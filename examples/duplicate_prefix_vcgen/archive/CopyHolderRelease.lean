import duplicate_prefix.CopyHolderRights
import duplicate_prefix.RootActualPhysicalReturn

namespace DuplicatePrefix.CopyHolderRelease

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification
open SourceDomain RetagReleaseRights RetagReleaseFootprint

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

/-- The final caller's own protector can be released after the copy using its
preserved footprint; this proves the production release outcome from local
rights, tag identity, and graph coherence. -/
theorem release (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (source holder root : UniIndex) (lower upper : UInt64)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (node : TreeNode) (found : tree.nodeAt holder = some node) (unexposed : node.isExposed = false)
    (tagKnown : tree.indexOfTag tag = some holder)
    (copied : CopyHolderRights.Footprint tree tags source holder lower upper) :
    ∃ after, tree.releaseProtector tag tags = ⟨after,.Released⟩ := by
  have active := active_of_footprint tree tags holder lower upper coherent copied.materialized copied.vacant
    copied.holderRights
  obtain ⟨after, _, _, _, _, released⟩ := release_retains_owned tree tag holder root tags tagKnown
    coherent roots node found unexposed active lower upper copied.holderRights
  have exactResult := (ProtectorReleaseWP.releasePre_iff tag tags (· = after) (fun _ _ => False) tree).mp
    ((released _ _).mpr rfl)
  refine ⟨after, ?_⟩
  cases same : tree.releaseProtector tag tags with
  | mk result status =>
    have resolved := exactResult
    rw [same] at resolved
    cases status
    all_goals first | exact False.elim resolved | exact congrArg (fun t => BorrowTree.ProtectorReleaseResult.mk t .Released) resolved

/-- Package the actual proved release of the live slice allocation into the
generic stack-pop plan. Other allocations are discharged by the tail plan. -/
theorem plan_head (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tags : ProtectedTags) (tag : BorTag)
    (found : memory.live[id]? = some entry) (after : BorrowTree)
    (released : entry.allocation.extra.releaseProtector tag tags = ⟨after,.Released⟩)
    (remaining : List (AllocId × BorTag)) (final : MemoryState Provenance BorrowTree K)
    (tail : StackPopRelease.Plan tags remaining (StackPopRelease.commitTree memory id entry after) final) :
    StackPopRelease.Plan tags ((id,tag)::remaining) memory final :=
  StackPopRelease.Plan.live id tag entry after remaining memory final found released tail

end DuplicatePrefix.CopyHolderRelease

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyHolderRelease.release,
      ``DuplicatePrefix.CopyHolderRelease.plan_head] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved copy-holder release dependency {dependency}"

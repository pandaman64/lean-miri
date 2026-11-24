import duplicate_prefix.FrozenReborrowScope
import duplicate_prefix.ScopedReleaseMaterialization

namespace DuplicatePrefix.AsMutHolderScope

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open SourceDomain ArchiveForestProjection RetagReleaseRights RetagReleaseFootprint GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem ancestor_frame {before after : BorrowTree} (nodes : before.nodes = after.nodes)
    {index source : UniIndex} (path : Ancestor before index source) :
    Ancestor after index source := by
  induction path with
  | self => exact .self _
  | parent previous node found edge ih =>
    exact .parent ih node (by simpa only [BorrowTree.nodeAt, ← nodes] using found) edge

/-- Nodes strictly between the original holder and the final raw reference
are unprotected under the caller's eventual post-return mask. -/
def BetweenTags (tree : BorrowTree) (tags : ProtectedTags) (holder source : UniIndex) : Prop :=
  Ancestor tree holder source ∧
    ∀ index node, tree.nodeAt index = some node → Ancestor tree index source →
      ¬ Ancestor tree index holder → tags.contains node.tag = false

theorem BetweenTags.self (tree : BorrowTree) (tags : ProtectedTags) (holder : UniIndex) :
    BetweenTags tree tags holder holder :=
  ⟨.self holder, fun _ _ _ here away => False.elim (away here)⟩

theorem BetweenTags.sameNodes {before after : BorrowTree} {tags : ProtectedTags} {holder source : UniIndex}
    (nodes : before.nodes = after.nodes) (initial : BetweenTags before tags holder source) :
    BetweenTags after tags holder source := by
  refine ⟨ancestor_frame nodes initial.1, ?_⟩
  intro index node present child noHolder
  apply initial.2 index node _ (ancestor_frame nodes.symm child)
    (fun ofHolder => noHolder (ancestor_frame nodes ofHolder))
  simpa only [BorrowTree.nodeAt,nodes] using present

/-- Transport the holder path through a real retag's range read and fresh
child attachment. New tag absence refers to the post-release mask. -/
theorem BetweenTags.retag {before read after : BorrowTree}
    {tags : ProtectedTags} {holder parent child : UniIndex}
    (prior : BetweenTags before tags holder parent) (nodes : read.nodes = before.nodes)
    (attached : MutableSliceRights.Attachment read after parent child)
    (oldTags : ∀ index node, index ≠ child → after.nodeAt index = some node →
      ∃ previous, before.nodeAt index = some previous ∧ previous.tag = node.tag)
    (fresh : BorTag) (freshUnheld : tags.contains fresh = false)
    (newTag : ∀ node, after.nodeAt child = some node → node.tag = fresh) :
    BetweenTags after tags holder child := by
  have frame := prior.sameNodes nodes.symm
  refine FrozenReborrowScope.append_unheld_scope attached frame.1 ?_ fresh newTag tags freshUnheld frame.2
  intro index data different stored
  obtain ⟨previous, present, key⟩ := oldTags index data different stored
  exact ⟨previous, by simpa only [BorrowTree.nodeAt,nodes] using present, key⟩

/-- Releasing the nested mutable helper's protector retains the raw grant
and recovers the outer holder's proof-ready range footprint. -/
theorem release_to_raw (tree : BorrowTree) (tags : ProtectedTags) (rawTag : BorTag)
    (source holder root : UniIndex) (node : TreeNode)
    (found : tree.nodeAt source = some node) (key : tree.indexOfTag rawTag = some source)
    (unexposed : node.isExposed = false) (coherent : CoherentForest tree)
    (roots : tree.roots = #[root]) (lower upper : UInt64)
    (scope : MaterializedWithin tree source lower upper)
    (holderScope : MaterializedWithin tree holder lower upper)
    (vacant : VacantRows tree)
    (owners : OwnedOn (fun row => LocationRights tree row tags source) lower upper tree.locations)
    (paths : BetweenTags tree (tags.remove rawTag) holder source) :
    ∃ after, tree.releaseProtector rawTag tags = ⟨after,.Released⟩ ∧
      after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧
      BetweenTags after (tags.remove rawTag) holder source ∧
      CopyHolderRights.Footprint after (tags.remove rawTag) source holder lower upper := by
  have active := active_of_footprint tree tags source lower upper coherent scope vacant owners
  obtain ⟨after, frame, coherentAfter, size, rawOwned, yes⟩ :=
    release_retains_owned tree rawTag source root tags key coherent roots node found unexposed active lower upper owners
  obtain ⟨watched, kept, retainedVacant, watchExact⟩ :=
    ScopedReleaseMaterialization.release_preserves_scope tree tags rawTag source root holder lower upper node found key
      unexposed coherent roots scope vacant owners holderScope
  have identity : watched = after := (watchExact (· = after) (fun _ _ => False)).mp ((yes _ _).mpr rfl)
  subst watched
  have result := (ProtectorReleaseWP.releasePre_iff rawTag tags (· = after) (fun _ _ => False) tree).mp
    ((yes _ _).mpr rfl)
  have done : tree.releaseProtector rawTag tags = ⟨after,.Released⟩ := by
    cases matchResult : tree.releaseProtector rawTag tags with
    | mk selected status =>
      rw [matchResult] at result
      cases status <;> first | exact False.elim result |
        exact congrArg (fun t => BorrowTree.ProtectorReleaseResult.mk t .Released) result
  have nodes : tree.nodes = after.nodes := (congrArg BorrowTree.nodes frame).symm
  have continued := paths.sameNodes nodes
  have keptHolder : OwnedOn (fun row => LocationRights after row (tags.remove rawTag) holder)
      lower upper after.locations := by
    intro position valid positive start stop
    exact return_to_ancestor after _ (tags.remove rawTag) source holder continued.1 continued.2
      (rawOwned position valid positive start stop)
  exact ⟨after,done,frame,coherentAfter,size,continued,rawOwned,keptHolder,kept,retainedVacant⟩

end DuplicatePrefix.AsMutHolderScope

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.AsMutHolderScope.ancestor_frame,
      ``DuplicatePrefix.AsMutHolderScope.BetweenTags.retag,
      ``DuplicatePrefix.AsMutHolderScope.release_to_raw] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved as_mut holder dependency {dependency}"

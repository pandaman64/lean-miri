import duplicate_prefix.EmptySharedTree
import duplicate_prefix.SharedHolderAttach

namespace DuplicatePrefix.EmptySharedWriteFrame

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open SourceDomain ArchiveForestProjection Miri.Verification.MutableRetagFootprint
open RetagLocationFrame GeneralRangeMapOrigins BorrowTree.MutationVerification BorrowTree.ZeroProtection
set_option maxHeartbeats 2500000
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false

/-- A zero-width shared reborrow preserves any old writable interval in
the same allocation under a protection mask in which its new tag is unheld. -/
theorem retainsOwned
    (tree : BorrowTree) (offset : Size) (parentTag freshTag : BorTag)
    (parent child writer : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (held : Bool) (coherent : CoherentForest tree)
    (selected : tree.tagMapping.insert freshTag = .Inserted mapping child)
    (parentKey : tree.indexOfTag parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (writerPresent : ∃ node, tree.nodeAt writer = some node)
    (tags : ProtectedTags) (freshUnheld : tags.contains freshTag = false)
    (lo hi : UInt64)
    (owned : OwnedOn (fun row => LocationRights tree row tags writer) lo hi tree.locations)
    (complete : (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).outcome = .ok ())
    (frame : let next := (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree
      FramedAt (fun _ _ => False) tree.locations child next) :
    let next := (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree
    OwnedOn (fun row => LocationRights next row tags writer) lo hi next.locations := by
  let inside := DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState
  let next := (tree.newChild offset (.concrete parentTag) freshTag inside .Frozen held).tree
  have cast : FramedWith (fun state => state.permission = .Frozen ∧ state.accessed = true)
      tree.locations child next := by
    refine ⟨frame.1, frame.2.1, ?_⟩
    intro point position valid lo hi
    obtain ⟨before, unborn⟩ := frame.2.2 point position valid lo hi
    exact ⟨before, fun state present => False.elim (unborn state present)⟩
  exact SharedRelease.retained_holder_after_shared_child tree offset parentTag freshTag parent child writer
    parentNode mapping inside held coherent selected parentKey parentPresent vacant writerPresent complete cast
    tags tags freshUnheld (fun _ _ _ => rfl) lo hi owned

private theorem ancestorRangeShape (ranges : Array ByteRange) (start : UniIndex)
    (strongest : IdempotentForeignAccess) (fuel steps : Nat) (cursor : Option UniIndex)
    (tree : BorrowTree) (matched : tree.locations.entries.map (·.range) = ranges) :
    weakenAncestorPre start strongest (fun t => t.locations.entries.map (·.range) = ranges)
      (fun _ t => t.locations.entries.map (·.range) = ranges) fuel steps cursor tree := by
  induction fuel generalizing steps cursor tree with
  | zero => exact matched
  | succ fuel ih =>
    unfold weakenAncestorPre
    split
    · exact matched
    · cases cursor with
      | none => exact matched
      | some index =>
        cases found : tree.nodes.get index with
        | none => simpa only [found] using matched
        | some node =>
          simp only [found]
          have same : (weakened tree index node strongest).locations.entries.map (·.range) =
              tree.locations.entries.map (·.range) := by
            simp [weakened, DedupRangeMap.modifyAll, Array.map_map, Function.comp_def]
          have next := same.trans matched
          split
          · exact ih _ _ _ next
          · exact next

theorem childRangeShape
    (tree : BorrowTree) (offset : Size) (parentTag freshTag : BorTag)
    (parent child : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (held : Bool) (selected : tree.tagMapping.insert freshTag = .Inserted mapping child)
    (parentKey : tree.indexOfTag parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (complete : (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).outcome = .ok ()) :
    let next := (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree
    next.locations.entries.map (·.range) = tree.locations.entries.map (·.range) := by
  let inside := DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState
  let keep := fun (now : BorrowTree) => now.locations.entries.map (·.range) = tree.locations.entries.map (·.range)
  have distinct : parent ≠ child := by
    intro equal
    rw [equal, vacant] at parentPresent
    contradiction
  have tagLookup : tree.tagMapping.get parentTag = some parent := parentKey
  have found : tree.nodes.get parent = some parentNode := parentPresent
  have pre : BorrowTree.MutationVerification.insertChildPre tree offset (.concrete parentTag) freshTag
      inside .Frozen held keep (fun _ => keep) := by
    let attached := initialChildAttached tree freshTag mapping child parent parentNode .Frozen .Read
    have children : childSegmentsPre offset child (some parent) held keep (fun _ => keep)
        inside.iterAll.toList attached .Read := by
      have empty : inside.iterAll.toList = [] := rfl
      rw [empty]
      simp only [childSegmentsPre, finishChildPre, weakenAncestorsPre]
      split
      · rfl
      · exact ancestorRangeShape _ parent .Read _ _ _ attached rfl
    unfold BorrowTree.MutationVerification.insertChildPre
    simp only [selected, tagLookup, Option.map_some,
      show Permission.Frozen.isInitial = true from rfl, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, show Permission.Frozen.isUnique = false from rfl,
      show Permission.Frozen.strongestIdempotentForeignAccess held = .Access .Read from rfl,
      BorrowTree.MutationVerification.finishInsertedChildPre,
      Sparse.get_other _ _ _ _ distinct, found]
    exact children
  have valid := (BorrowTree.MutationVerification.insertChildPre_iff tree offset (.concrete parentTag)
    freshTag inside .Frozen held keep (fun _ => keep)).mp pre
  have completed : (tree.newChild offset (.concrete parentTag) freshTag inside .Frozen held).outcome = .ok () := complete
  change keep (tree.newChild offset (.concrete parentTag) freshTag inside .Frozen held).tree
  unfold BorrowTree.MutationVerification.childResultPre at valid
  rw [completed] at valid
  exact valid

/-- What two zero-width retags retain for an existing return slot. -/
structure Transfer (before after : BorrowTree) (fresh : List BorTag) : Prop where
  coherent : CoherentForest after
  roots : after.roots = before.roots
  size : after.locations.size = before.locations.size
  geometry : after.locations.entries.map (·.range) = before.locations.entries.map (·.range)
  keys : ∀ key, key ∉ fresh → after.indexOfTag key = before.indexOfTag key
  nodes : ∀ index data, before.nodeAt index = some data →
    ∃ now, after.nodeAt index = some now ∧ now.tag = data.tag ∧
      now.parent = data.parent ∧ now.isExposed = data.isExposed
  owns : ∀ tags, (∀ tag ∈ fresh, tags.contains tag = false) →
    ∀ index, (∃ data, before.nodeAt index = some data) → ∀ lo hi,
      OwnedOn (fun row => LocationRights before row tags index) lo hi before.locations →
      OwnedOn (fun row => LocationRights after row tags index) lo hi after.locations
  extent : ∀ index, (∃ data, before.nodeAt index = some data) → ∀ lo hi,
    RetagReleaseFootprint.MaterializedWithin before index lo hi →
    RetagReleaseFootprint.MaterializedWithin after index lo hi

theorem Transfer.trans {a b c : BorrowTree} {first second : List BorTag}
    (left : Transfer a b first) (right : Transfer b c second) :
    Transfer a c (first ++ second) := by
  refine ⟨right.coherent, right.roots.trans left.roots, right.size.trans left.size, right.geometry.trans left.geometry, ?_, ?_, ?_, ?_⟩
  · intro key untouched
    exact (right.keys key fun h => untouched (List.mem_append_right _ h)).trans
      (left.keys key fun h => untouched (List.mem_append_left _ h))
  · intro index old previous
    obtain ⟨next, nextAt, tag, parent, exposure⟩ := left.nodes index old previous
    obtain ⟨final, finalAt, newTag, newParent, newExposure⟩ := right.nodes index next nextAt
    exact ⟨final, finalAt, newTag.trans tag, newParent.trans parent, newExposure.trans exposure⟩
  · intro tags unheld index present lo hi owned
    obtain ⟨old, previous⟩ := present
    obtain ⟨new, found, _⟩ := left.nodes index old previous
    exact right.owns tags (fun tag h => unheld tag (List.mem_append_right _ h)) index ⟨new, found⟩ lo hi
      (left.owns tags (fun tag h => unheld tag (List.mem_append_left _ h)) index ⟨old, previous⟩ lo hi owned)
  · intro index present lo hi extent
    obtain ⟨old, previous⟩ := present
    obtain ⟨new, found, _⟩ := left.nodes index old previous
    exact right.extent index ⟨new, found⟩ lo hi (left.extent index ⟨old, previous⟩ lo hi extent)

theorem transferOfChild
    (tree : BorrowTree) (offset : Size) (parentTag freshTag : BorTag)
    (parent child : UniIndex) (parentNode : TreeNode) (mapping : UniKeyMap BorTag)
    (held : Bool) (coherent : CoherentForest tree)
    (selected : tree.tagMapping.insert freshTag = .Inserted mapping child)
    (parentKey : tree.indexOfTag parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (complete : (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).outcome = .ok ())
    (frame : let next := (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree
      FramedAt (fun _ _ => False) tree.locations child next)
    (coherentAfter : CoherentForest (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree)
    (sameRoots : (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree.roots = tree.roots) :
    Transfer tree (tree.newChild offset (.concrete parentTag) freshTag
      (DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState) .Frozen held).tree [freshTag] := by
  let inside := DedupRangeMap.new Size.ZERO RetagSharedChild.sharedState
  let next := (tree.newChild offset (.concrete parentTag) freshTag inside .Frozen held).tree
  have different (index : UniIndex) (old : TreeNode) (atIndex : tree.nodeAt index = some old) : index ≠ child := by
    intro matchIndex
    rw [matchIndex, vacant] at atIndex
    contradiction
  refine ⟨coherentAfter, sameRoots, frame.1,
    childRangeShape tree offset parentTag freshTag parent child parentNode mapping held selected parentKey parentPresent vacant complete, ?_, ?_, ?_, ?_⟩
  · intro key notFresh
    exact newChild_old_key tree offset (.concrete parentTag) freshTag key inside .Frozen held mapping child
      (by simpa using notFresh) selected
  · intro index old previous
    have notNew := different index old previous
    have metadata := newChild_nodeMetadata tree offset parentTag freshTag parent child mapping inside .Frozen held
      selected parentKey parentNode parentPresent vacant complete index
    rw [ite_eq_right notNew] at metadata
    have exposure := newChild_older_exposure tree offset parentTag freshTag parent child index mapping inside
      .Frozen held .Read rfl rfl rfl selected parentKey parentNode parentPresent vacant notNew complete
    change nodeMetadata next index = nodeMetadata tree index at metadata
    unfold nodeMetadata at metadata
    rw [previous] at metadata exposure
    cases atIndex : next.nodeAt index with
    | none => rw [atIndex] at metadata; contradiction
    | some now =>
      rw [atIndex] at metadata
      change (next.nodeAt index).map TreeNode.isExposed = _ at exposure
      rw [atIndex] at exposure
      exact ⟨now,rfl,congrArg Prod.fst (Option.some.inj metadata),
        congrArg (fun record => record.2.1) (Option.some.inj metadata),Option.some.inj exposure⟩
  · intro tags unheld watcher present lo hi owned
    exact retainsOwned tree offset parentTag freshTag parent child watcher parentNode mapping held coherent
      selected parentKey parentPresent vacant present tags (unheld freshTag (by simp)) lo hi owned complete frame
  · intro index present lo hi extent
    obtain ⟨old, atIndex⟩ := present
    exact SharedRelease.retained_materialization_after_attach (grant := fun _ => False)
      frame (different index old atIndex) lo hi extent

#print axioms childRangeShape
#print axioms retainsOwned
#print axioms Transfer.trans
#print axioms transferOfChild

end DuplicatePrefix.EmptySharedWriteFrame

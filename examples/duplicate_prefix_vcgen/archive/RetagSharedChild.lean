import duplicate_prefix.RetagLocationFrame
import Miri.TreeBorrows.RetagPolicy

namespace DuplicatePrefix.RetagSharedChild

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.BorrowTree Miri.TreeBorrows.BorrowTree.ZeroProtection
open Miri.TreeBorrows.BorrowTree.MutationVerification
open DuplicatePrefix.RetagRangeFrame DuplicatePrefix.RetagLocationFrame

def sharedState : Tree.LocationState := ⟨.Frozen, true, .Read⟩

theorem selected_size (offset : Size) (range : ByteRange) (capacity : Size)
    (ordered : range.start ≤ range.stop)
    (fits : offset.bytes.toNat + range.stop.toNat ≤ capacity.bytes.toNat) :
    ∃ start, Size.add (Size.ofBytes range.start) offset = .ok start ∧
      start.bytes.toNat + (range.stop - range.start).toNat ≤ capacity.bytes.toNat := by
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  have nooverflow : range.start.toNat + offset.bytes.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (by omega) capacity.bytes.toNat_lt
  have sum : (range.start + offset.bytes).toNat = range.start.toNat + offset.bytes.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt nooverflow]
  have ordinary : ¬ range.start + offset.bytes < range.start := by
    intro impossible
    have less := UInt64.lt_iff_toNat_lt.mp impossible
    omega
  refine ⟨Size.ofBytes (range.start + offset.bytes), ?_, ?_⟩
  · simp [Size.add, Size.ofBytes, ordinary]
  · simp only [Size.ofBytes, sum, UInt64.toNat_sub_of_le _ _ ordered]
    omega

private theorem segments_safe (offset : Size) (child parent : UniIndex) (held : Bool)
    (segments : List (RangeMapSegment Tree.LocationState)) (current : BorrowTree)
    (minimum : IdempotentForeignAccess)
    (span : ∀ segment ∈ segments, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ current.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ segments, segment.data = sharedState)
    (well : current.locations.WellFormed)
    (graph : ParentDepth current.nodes)
    (parentLive : ∃ node, current.nodes.get parent = some node)
    (rank : graph.depth parent < current.nodes.size) :
    childSegmentsPre offset child (some parent) held (fun _ => True) (fun _ _ => False)
      segments current minimum := by
  induction segments generalizing current minimum with
  | nil =>
    simp only [childSegmentsPre, finishChildPre]
    obtain ⟨node, found⟩ := parentLive
    have completed := ZeroProtection.succeeds current graph parent node found rank minimum
    rw [weakenAncestorsPre_iff]
    dsimp only
    rw [completed]
    trivial
  | cons segment rest ih =>
    obtain ⟨ordered, fits⟩ := span segment List.mem_cons_self
    obtain ⟨start, checked, bounds⟩ := selected_size offset segment.range current.locations.size ordered fits
    let length := Size.ofBytes (segment.range.stop - segment.range.start)
    let modify : ByteRange → LocationTree → LocationTree :=
      fun _ row => {row with perms := row.perms.insert child segment.data}
    have updated := modify_of_bounded current.locations start length modify (fun _ _ => True)
      well bounds (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    have recursive : ∀ sifa, childSegmentsPre offset child (some parent) held
        (fun _ => True) (fun _ _ => False) rest
        {current with locations := (current.locations.modifyRange start length modify).state} sifa := by
      intro sifa
      apply ih ({current with locations := (current.locations.modifyRange start length modify).state}) sifa ?_ (fun part mem => frozen part (.tail _ mem)) updated.2.1 graph parentLive rank
      intro part mem
      have here := span part (.tail _ mem)
      simpa only [updated.2.2.1] using here
    have material := frozen segment List.mem_cons_self
    simp only [childSegmentsPre, childSegmentPre, material, sharedState, Permission.isInitial,
      Permission.strongestIdempotentForeignAccess, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, bne_self_eq_false, checked]
    simp only [modify, length, material, sharedState] at updated recursive
    rw [updated.1]
    exact recursive _

private theorem segments_in_attachedTree (offset : Size) (child parent : UniIndex) (held : Bool)
    (inside : DedupRangeMap Tree.LocationState) (tree : BorrowTree)
    (mapping : UniKeyMap BorTag) (nodes : UniValMap TreeNode)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, segment.data = sharedState)
    (well : tree.locations.WellFormed)
    (graph : ParentDepth nodes) (parentLive : ∃ node, nodes.get parent = some node)
    (rank : graph.depth parent < nodes.size) :
    childSegmentsPre offset child (some parent) held (fun _ => True) (fun _ _ => False) inside.iterAll.toList
      {tree with tagMapping := mapping, nodes := nodes} .Read := by
  exact segments_safe offset child parent held inside.iterAll.toList
    {tree with tagMapping := mapping, nodes := nodes} .Read span frozen well graph parentLive rank

private theorem constructor_pre (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent child : UniIndex) (mapping : UniKeyMap BorTag)
    (inside : DedupRangeMap Tree.LocationState) (parentNode : TreeNode) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (next : BorrowTree → Prop) (failure : BorrowTree.ChildInsertError → BorrowTree → Prop)
    (tail : let node : TreeNode := {
        tag, parent := some parent, children := #[], defaultInitialPermission := .Frozen,
        defaultInitialSifa := .Read, isExposed := false }
      childSegmentsPre offset child (some parent) held next failure inside.iterAll.toList
        {tree with tagMapping := mapping, nodes := Append.attachedNodes tree.nodes child parent parentNode node}
        (.Read)) :
    insertChildPre tree offset (.concrete parentTag) tag inside .Frozen held next failure := by
  have distinct := Reuse.parent_not_vacant tree.nodes child parent parentNode vacant present
  have parentLookup : tree.tagMapping.get parentTag = some parent := parentFound
  have found : tree.nodes.get parent = some parentNode := present
  have defaultSifa : Permission.strongestIdempotentForeignAccess .Frozen held =
      .Access .Read := rfl
  unfold insertChildPre
  simp only [mapped, parentLookup, Option.map_some, Permission.isInitial, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Permission.isUnique, defaultSifa, finishInsertedChildPre,
    Sparse.get_other _ _ _ _ distinct, found]
  exact tail

private theorem completed_from_pre (result : BorrowTree.ChildInsertResult)
    (post : childResultPre (fun _ => True) (fun _ _ => False) result) :
    result.outcome = .ok () := by
  obtain ⟨tree, outcome⟩ := result
  cases outcome with
  | error error => contradiction
  | ok value =>
    cases value
    rfl

set_option maxHeartbeats 1200000 in
/-- Actual concrete shared child construction succeeds for bounded shared
segments and an acyclic allocator-selected vacant node. This includes both
the append and reusable-slot branches and all actual segmented writes. -/
theorem newChild_shared_completes (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent child : UniIndex)
    (mapping : UniKeyMap BorTag) (inside : DedupRangeMap Tree.LocationState) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none) (validSlot : child.toNat ≤ tree.nodes.size)
    (well : tree.locations.WellFormed)
    (graph : ParentDepth tree.nodes) (rank : graph.depth parent < tree.nodes.size)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, segment.data = sharedState) :
    (tree.newChild offset (.concrete parentTag) tag inside .Frozen held).outcome = .ok () := by
  let added : TreeNode := {
    tag, parent := some parent, children := #[], defaultInitialPermission := .Frozen,
    defaultInitialSifa := .Read, isExposed := false }
  have distinct : parent ≠ child := Reuse.parent_not_vacant tree.nodes child parent parentNode vacant present
  have lookup : (tree.nodes.insert child added).get parent = some parentNode :=
    (Sparse.get_other tree.nodes child parent added distinct).trans present
  let attached := Append.attachedNodes tree.nodes child parent parentNode added
  have attachParent : ∃ node, attached.get parent = some node := by
    let updated := {parentNode with children := parentNode.children.push child}
    exact ⟨updated, insert_existing_get_same _ parent parentNode updated lookup⟩
  have height : ∃ certificate : ParentDepth attached, certificate.depth parent < attached.size := by
    by_cases reuse : child.toNat < tree.nodes.size
    · exact ⟨Reuse.attached_depth _ graph child parent parentNode added reuse vacant present rfl rank,
        Reuse.attached_parent_strict _ graph child parent parentNode added reuse vacant present rfl rank⟩
    · have endSlot : child.toNat = tree.nodes.data.size := by
        change child.toNat = tree.nodes.size
        omega
      exact ⟨Append.attached_depth _ graph child parent parentNode added endSlot present rfl,
        Append.attached_parent_strict _ graph child parent parentNode added endSlot present rfl⟩
  obtain ⟨certificate, parentRank⟩ := height
  have tail := segments_in_attachedTree offset child parent held inside tree mapping attached
    span frozen well certificate attachParent parentRank
  have provePre := constructor_pre tree offset parentTag tag parent child mapping inside
    parentNode held mapped parentFound present vacant (fun _ => True) (fun _ _ => False) tail
  have post := (insertChildPre_iff tree offset (.concrete parentTag) tag inside
    .Frozen held (fun _ => True) (fun _ _ => False)).mp provePre
  exact completed_from_pre _ post

#print axioms newChild_shared_completes
end DuplicatePrefix.RetagSharedChild

import Miri.Verification.TreeReadWriteWP

/-!
Initial-state permission conditions from a structural tree witness.
-/

namespace Miri.Verification.TreeVisitWP

open Miri.TreeBorrows Miri.TreeBorrows.Tree

/-- A normal access completes exactly when its initially scheduled events are
permitted. Consistent parent and child addresses discharge schedule uniqueness
for any access kind and pruning predicate. -/
theorem normal_complete_of_addressed_iff (tree : NormalTreeState) (shape : tree.topology.Addressed)
    (start : Nat) (kind : AccessKind) (mode : ChildrenVisitMode) :
    (tree.performAccess start kind mode).status = .Completed ↔
      ∀ event ∈ (tree.topology.traverseWithSkip start mode (tree.shouldSkipForeignNode kind)).2,
        EventAllowed tree kind event :=
  normal_complete_iff tree start kind mode
    (TraversalTree.traverseWithSkip_nodup shape start mode (tree.shouldSkipForeignNode kind))

/-- For one normal location, both access schedules inherit uniqueness from
the same topology, even though the write's pruning depends on the read. -/
theorem normal_read_write_pre_of_addressed_iff (tree : NormalTreeState)
    (shape : tree.topology.Addressed) (reader writer : Nat) (readMode writeMode : ChildrenVisitMode) :
    tree.accessPre reader .Read readMode (fun read => read.status = .Completed ∧
      read.tree.accessPre writer .Write writeMode (fun write => write.status = .Completed)) ↔
    EventsReadWriteAllowed tree (tree.topology.traverseWithSkip reader readMode
      (tree.shouldSkipForeignNode .Read)).2
      (writeScheduleAfterRead tree (tree.topology.traverseWithSkip reader readMode
        (tree.shouldSkipForeignNode .Read)).2 writer writeMode).2 :=
  normal_read_write_pre_iff tree reader writer readMode writeMode
    (TraversalTree.traverseWithSkip_nodup shape reader readMode (tree.shouldSkipForeignNode .Read))
    (TraversalTree.traverseWithSkip_nodup shape writer writeMode _)

private def projectNode (node : TreeNode) : TraversalNode :=
  ⟨node.parent.map UniIndex.toNat, node.children.toList.map UniIndex.toNat⟩

private theorem projected_nodeAt (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (position : Nat) :
    (tree.normalView location tags).topology.nodeAt position =
      ((tree.nodes.data[position]?.join).map projectNode).getD ⟨none, []⟩ := by
  change ((tree.nodes.data.map (fun entry => match entry with
    | none => (⟨none, []⟩ : TraversalNode)
    | some node => projectNode node))[position]?).getD ⟨none, []⟩ = _
  rw [Array.getElem?_map]
  cases tree.nodes.data[position]? with
  | none => rfl
  | some entry => cases entry <;> rfl

private theorem projected_present (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    (tree.normalView location tags).topology.nodeAt index.toNat = projectNode node := by
  rw [projected_nodeAt]
  change (tree.nodes.data[index.toNat]?.join.map projectNode).getD ⟨none, []⟩ = _
  have source : tree.nodes.data[index.toNat]?.join = some node := by
    unfold UniValMap.get at present
    cases lookup : tree.nodes.data[index.toNat]? with
    | none => simp [lookup] at present
    | some entry => simpa [lookup] using present
  rw [source]
  rfl

private theorem representable_position (position : Nat) (fits : position < 4294967296) :
    ∃ index : UniIndex, UniIndex.ofNat? position = some index ∧ index.toNat = position := by
  refine ⟨⟨UInt32.ofNat position⟩, ?_, ?_⟩
  · simp [UniIndex.ofNat?, show position ≤ 4294967295 by omega]
  · simp [UniIndex.toNat, UInt32.toNat_ofNat', Nat.mod_eq_of_lt fits]

private theorem index_roundTrip (index : UniIndex) : UniIndex.ofNat? index.toNat = some index := by
  obtain ⟨round, represented, same⟩ := representable_position index.toNat index.idx.toNat_lt
  rw [BorrowTree.ZeroProtection.index_injective round index same] at represented
  exact represented

private theorem projected_cases (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (position : Nat) :
    (tree.normalView location tags).topology.nodeAt position = ⟨none, []⟩ ∨
      ∃ index node, UniIndex.ofNat? position = some index ∧ index.toNat = position ∧
        tree.nodes.get index = some node ∧
        (tree.normalView location tags).topology.nodeAt position = projectNode node := by
  cases slot : tree.nodes.data[position]? with
  | none => exact .inl (by simp [projected_nodeAt, slot])
  | some entry =>
    cases entry with
    | none => exact .inl (by simp [projected_nodeAt, slot])
    | some node =>
      have occupied := (Array.getElem?_eq_some_iff.mp slot).1
      obtain ⟨index, represented, same⟩ := representable_position position (by omega)
      exact .inr ⟨index, node, represented, same, by simp [UniValMap.get, same, slot],
        by simp [projected_nodeAt, slot]⟩

/-- The existing source-node parent-depth certificate and child-list
coherence discharge uniqueness for the projected normal visitor. -/
def normalView_addressed_of_parentDepth (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes)
    (children : ∀ index node, tree.nodes.get index = some node →
      node.children.toList.Nodup ∧
        ∀ child ∈ node.children.toList, ∃ childNode,
          tree.nodes.get child = some childNode ∧ childNode.parent = some index) :
    (tree.normalView location tags).topology.Addressed := by
  let rank := fun position => ((UniIndex.ofNat? position).map depth.depth).getD 0
  apply TraversalTree.Addressed.ofParentDepth _ rank
  · intro parent
    rcases projected_cases tree location tags fits parent with empty | ⟨index, node, _, _, present, view⟩
    · simp [empty]
    · rw [view]
      simp only [projectNode, List.Nodup, List.pairwise_map]
      exact (children index node present).1.imp
        (fun distinct same => distinct (BorrowTree.ZeroProtection.index_injective _ _ same))
  · intro parent child edge
    rcases projected_cases tree location tags fits parent with empty | ⟨index, node, _, same, present, view⟩
    · simp [empty] at edge
    · rw [view] at edge
      obtain ⟨childIndex, member, rfl⟩ := List.mem_map.mp edge
      obtain ⟨childNode, childPresent, pointsTo⟩ := (children index node present).2 childIndex member
      simp [projected_present tree location tags childIndex childNode childPresent,
        projectNode, pointsTo, same]
  · intro parent child edge
    rcases projected_cases tree location tags fits child with empty | ⟨index, node, repr, _, present, view⟩
    · simp [empty] at edge
    · rw [view] at edge
      cases pointsTo : node.parent with
      | none => simp [projectNode, pointsTo] at edge
      | some parentIndex =>
        simp only [projectNode, pointsTo, Option.map_some, Option.some.injEq] at edge
        subst parent
        obtain ⟨_, _, smaller⟩ := depth.parent index node present parentIndex pointsTo
        simpa [rank, repr, index_roundTrip] using smaller

/-- The normal visitor topology of a fresh allocation is the single root,
independently of permission state and protectors. -/
def new_normalView_addressed (tag : Miri.Memory.BorTag) (size : Miri.ABI.Size)
    (location : LocationTree) (tags : ProtectedTags) :
    ((BorrowTree.new tag size).normalView location tags).topology.Addressed := by
  have singleton : ((BorrowTree.new tag size).normalView location tags).topology =
      (⟨#[⟨none, []⟩]⟩ : TraversalTree) := by cbv
  rw [singleton]
  apply TraversalTree.Addressed.ofParentDepth _ (fun _ => 0)
  · intro parent
    cases parent <;> simp [TraversalTree.nodeAt]
  · intro parent child edge
    cases parent <;> simp [TraversalTree.nodeAt] at edge
  · intro parent child link
    cases child <;> simp [TraversalTree.nodeAt] at link

/-- A concrete normal-location visit uses the same initial event checks under
the structural condition on its projected topology. -/
theorem concrete_normal_complete_of_addressed_iff (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (start : UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode) (shape : (tree.normalView location tags).topology.Addressed) :
    (tree.performNormalAccessAt location start kind tags mode).access.status = .Completed ↔
      let view := tree.normalView location tags
      ∀ event ∈ (view.topology.traverseWithSkip start.toNat mode (view.shouldSkipForeignNode kind)).2,
        EventAllowed view kind event := by
  rw [normal_access_result]
  exact normal_complete_of_addressed_iff (tree.normalView location tags) shape start.toNat kind mode

end Miri.Verification.TreeVisitWP

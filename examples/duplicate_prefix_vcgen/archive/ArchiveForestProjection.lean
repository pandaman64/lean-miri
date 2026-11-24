import SourceDomain
import duplicate_prefix.GeneralBorrowExposedScopedNormal
import duplicate_prefix.GeneralBorrowFreshReuseProtection

namespace DuplicatePrefix.ArchiveForestProjection

set_option backward.isDefEq.respectTransparency false

open Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure BorrowRangeAccess
open GeneralBorrowPresence SourceDomain

private abbrev projected (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags) :=
  (source_normal_projection tree location protectors).topology

theorem projection_size (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags) :
    (projected tree location protectors).nodes.size = tree.nodes.data.size := by
  unfold projected
  unfold_general_projection
  unfold_general_topology
  simp

theorem projection_slot
    (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (position : Nat) (valid : position < (projected tree location protectors).nodes.size) :
    (projected tree location protectors).nodes[position] =
      match tree.nodes.data[position]? with
      | some (some node) => ⟨node.parent.map UniIndex.toNat, node.children.toList.map UniIndex.toNat⟩
      | _ => ⟨none, []⟩ := by
  have inData := valid
  rw [projection_size] at inData
  rw [Array.getElem?_eq_getElem inData]
  unfold projected
  unfold_general_projection
  unfold_general_topology
  dsimp only
  rw [Array.getElem_map]
  cases tree.nodes.data[position] <;> rfl

theorem projection_view
    (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (valid : position < (projected tree location protectors).nodes.size) :
    (projected tree location protectors).nodes[position] = ⟨none, []⟩ ∨
    ∃ index node, index.toNat = position ∧ tree.nodeAt index = some node ∧
      (projected tree location protectors).nodes[position] =
        ⟨node.parent.map UniIndex.toNat, node.children.toList.map UniIndex.toNat⟩ := by
  have inData := valid
  rw [projection_size] at inData
  rw [projection_slot]
  rcases slot : tree.nodes.data[position]? with _ | _ | node
  · exact Or.inl rfl
  · exact Or.inl rfl
  · obtain ⟨index, _, same⟩ := index_nat position (by omega)
    refine Or.inr ⟨index, node, same, ?_, rfl⟩
    unfold BorrowTree.nodeAt UniValMap.get
    simp [same, slot]

theorem projected_node
    (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    ∃ valid : index.toNat < (projected tree location protectors).nodes.size,
      (projected tree location protectors).nodes[index.toNat] =
        ⟨node.parent.map UniIndex.toNat, node.children.toList.map UniIndex.toNat⟩ := by
  obtain ⟨valid, _⟩ := array_of_node tree index node present
  have inProjection : index.toNat < (projected tree location protectors).nodes.size := by
    rwa [projection_size]
  refine ⟨inProjection, ?_⟩
  have projected := projection_topology_node tree location protectors index.toNat index node rfl present
  simpa only [Array.getElem?_eq_getElem inProjection, Option.getD_some] using projected

/-- Source graph coherence implies the exact ranked forest of the current normal visitor. -/
def forest (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : ∀ index node, tree.nodeAt index = some node →
      node.children.toList.Nodup ∧
        (∀ child ∈ node.children.toList, ∃ childNode,
          tree.nodeAt child = some childNode ∧ childNode.parent = some index) ∧
        (∀ child childNode, tree.nodeAt child = some childNode →
          childNode.parent = some index → child ∈ node.children.toList)) :
    GeneralBorrowForest.Forest (projected tree location protectors) := by
  let rank := fun position => ((UniIndex.ofNat? position).map depth.depth).getD 0
  refine ⟨rank, ?_, ?_, ?_, ?_⟩
  · intro position valid parent edge
    rcases projection_view tree location protectors fits position valid with vacant | ⟨index, node, positionEq, present, projection⟩
    · simp [vacant] at edge
    · rw [projection] at edge
      cases actual : node.parent with
      | none => simp [actual] at edge
      | some parentIndex =>
        simp only [actual, Option.map_some, Option.some.injEq] at edge
        obtain ⟨parentNode, parentPresent, decreases⟩ := depth.parent index node present parentIndex actual
        have found := (projected_node tree location protectors parentIndex parentNode parentPresent).1
        subst parent
        refine ⟨found, ?_⟩
        rw [← positionEq]
        simpa [rank, index_self] using decreases
  · intro position valid
    rcases projection_view tree location protectors fits position valid with vacant | ⟨index, node, _, present, projection⟩
    · simp [vacant]
    · rw [projection]
      simp only [List.Nodup, List.pairwise_map]
      apply (children index node present).1.imp
      intro first second different same
      apply different
      exact Option.some.inj ((index_self first).symm.trans ((congrArg UniIndex.ofNat? same).trans (index_self second)))
  · intro position valid child member
    rcases projection_view tree location protectors fits position valid with vacant | ⟨index, node, positionEq, present, projection⟩
    · simp [vacant] at member
    · rw [projection] at member
      obtain ⟨childIndex, belongs, rfl⟩ := List.mem_map.mp member
      obtain ⟨childNode, childPresent, childParent⟩ := (children index node present).2.1 childIndex belongs
      obtain ⟨bounded, projectedChild⟩ := projected_node tree location protectors childIndex childNode childPresent
      exact ⟨bounded, by simp [projectedChild, childParent, positionEq]⟩
  · intro position valid parent edge
    rcases projection_view tree location protectors fits position valid with vacant | ⟨index, node, positionEq, present, projection⟩
    · simp [vacant] at edge
    · rw [projection] at edge
      cases actual : node.parent with
      | none => simp [actual] at edge
      | some parentIndex =>
        simp only [actual, Option.map_some, Option.some.injEq] at edge
        obtain ⟨parentNode, parentPresent, _⟩ := depth.parent index node present parentIndex actual
        obtain ⟨bounded, projectedParent⟩ := projected_node tree location protectors parentIndex parentNode parentPresent
        subst parent
        refine ⟨bounded, ?_⟩
        rw [projectedParent]
        exact List.mem_map.mpr ⟨index, (children parentIndex parentNode parentPresent).2.2 index node present actual, positionEq⟩

private theorem index_injective {first second : UniIndex}
    (same : first.toNat = second.toNat) : first = second := by
  exact Option.some.inj ((index_self first).symm.trans ((congrArg UniIndex.ofNat? same).trans (index_self second)))

private theorem split_ancestor {tree : BorrowTree} {root current : UniIndex}
    (path : Ancestor tree root current) : root = current ∨
    ∃ parent node, tree.nodeAt current = some node ∧ node.parent = some parent ∧
      Ancestor tree root parent := by
  induction path with
  | self => exact .inl rfl
  | @parent current child parent path node found edge ih =>
    rcases ih with rfl | ⟨prior, data, priorFound, priorEdge, tail⟩
    · exact .inr ⟨parent, node, found, edge, .self _⟩
    · exact .inr ⟨prior, data, priorFound, priorEdge, .parent tail node found edge⟩

private theorem descend_ancestor {tree : BorrowTree} {root parent child : UniIndex}
    (path : Ancestor tree root parent) (node : TreeNode)
    (found : tree.nodeAt child = some node) (edge : node.parent = some parent) :
    Ancestor tree root child := by
  induction path with
  | self => exact .parent (.self _) node found edge
  | parent _ prior priorFound priorEdge ih => exact .parent (ih edge) prior priorFound priorEdge

private theorem pointed_path
    (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (depth : ParentDepth tree.nodes) (query : UniIndex) (fuel : Nat)
    (current : UniIndex) (node : TreeNode) (present : tree.nodeAt current = some node)
    (bound : depth.depth current ≤ fuel) :
    query.toNat ∈ sourceAncestorPath (projected tree location protectors) fuel current.toNat ↔
      Ancestor tree query current := by
  induction fuel generalizing current node with
  | zero =>
    rw [ancestor_zero, List.mem_singleton]
    constructor
    · intro same
      cases index_injective same
      exact .self _
    · intro path
      rcases split_ancestor path with rfl | ⟨parent, currentNode, currentPresent, edge, _⟩
      · rfl
      · cases Option.some.inj (currentPresent.symm.trans present)
        obtain ⟨_, _, decreases⟩ := depth.parent current node currentPresent parent edge
        omega
  | succ fuel ih =>
    rw [ancestor_succ]
    have row := projection_topology_node tree location protectors current.toNat current node rfl present
    change (query.toNat ∈ match ((projected tree location protectors).nodes[current.toNat]?.getD ⟨none, []⟩).parent with
      | none => [current.toNat]
      | some parent => current.toNat :: sourceAncestorPath (projected tree location protectors) fuel parent) ↔ _
    rw [row]
    cases actualParent : node.parent with
    | none =>
      simp only [Option.map_none, List.mem_singleton]
      constructor
      · intro same
        cases index_injective same
        exact .self _
      · intro path
        rcases split_ancestor path with rfl | ⟨parent, currentNode, currentPresent, edge, _⟩
        · rfl
        · cases Option.some.inj (currentPresent.symm.trans present)
          rw [edge] at actualParent
          cases actualParent
    | some prior =>
      obtain ⟨priorNode, priorPresent, decreases⟩ := depth.parent current node present prior actualParent
      simp only [Option.map_some, List.mem_cons]
      rw [ih prior priorNode priorPresent (by omega)]
      constructor
      · rintro (same | tail)
        · cases index_injective same
          exact .self _
        · exact descend_ancestor tail node present actualParent
      · intro path
        rcases split_ancestor path with rfl | ⟨parentIndex, currentNode, currentPresent, edge, tail⟩
        · exact .inl rfl
        · cases Option.some.inj (currentPresent.symm.trans present)
          cases Option.some.inj (edge.symm.trans actualParent)
          exact .inr tail

theorem ancestor_iff (tree : BorrowTree) (location : LocationTree) (protectors : ProtectedTags)
    (depth : ParentDepth tree.nodes) (query current : UniIndex) (node : TreeNode)
    (present : tree.nodeAt current = some node) :
    query.toNat ∈ (projected tree location protectors).ancestorPath current.toNat ↔
      Ancestor tree query current := by
  apply pointed_path tree location protectors depth query _ _ node present
  rw [projection_size]
  exact depth.bounded current node present

private theorem projected_held (tree : BorrowTree) (location : LocationTree)
    (protectors : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) :
    (source_normal_projection tree location protectors).protectedNodes.contains index.toNat =
      protectors.contains node.tag := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, GeneralBorrowFreshReuseProtection.protected_iff]
  constructor
  · rintro ⟨found, lookup, held⟩
    cases Option.some.inj (lookup.symm.trans present)
    exact held
  · intro held
    exact ⟨node, present, held⟩

/-- A coherent current caller forest and per-location ownership imply completion
of the canonical normal visitor, including its actual writeback and SIFA cache. -/
theorem normal_access (tree : BorrowTree) (location : LocationTree)
    (protectors : ProtectedTags) (source : UniIndex) (kind : AccessKind)
    (mode : ChildrenVisitMode) (coherent : CoherentForest tree) (sourceNode : TreeNode)
    (sourcePresent : tree.nodeAt source = some sourceNode)
    (rights : ∀ index node, tree.nodeAt index = some node →
      ∃ state, tree.locationStateAt location index = some state ∧
        (Ancestor tree index source → localOwns state (protectors.contains node.tag)) ∧
        (¬ Ancestor tree index source → foreignCompatible state (protectors.contains node.tag))) :
    (tree.performNormalAccessAt location source kind protectors mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location source kind protectors mode).outcome = .ok () := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index node present parent edge
    obtain ⟨parentNode, found⟩ := coherent.parentPresent index node parent present edge
    exact ⟨parentNode, found, decreases index node parent present edge⟩⟩
  have childData : ∀ index node, tree.nodeAt index = some node →
      node.children.toList.Nodup ∧
        (∀ child ∈ node.children.toList, ∃ childNode,
          tree.nodeAt child = some childNode ∧ childNode.parent = some index) ∧
        (∀ child childNode, tree.nodeAt child = some childNode →
          childNode.parent = some index → child ∈ node.children.toList) := by
    intro index node present
    simpa using coherent.childEdges index node present
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro index node present child member
    obtain ⟨childNode, found, _⟩ := (childData index node present).2.1 child member
    exact ⟨childNode, found⟩
  let projection := source_normal_projection tree location protectors
  let component : GeneralBorrowExposedScopedNormal.Component projection.topology source.toNat :=
    ⟨GeneralBorrowGraph.Present tree, ⟨source, sourceNode, rfl, sourcePresent⟩,
      GeneralBorrowGraph.parents_closed tree location protectors depth,
      GeneralBorrowGraph.children_closed tree location protectors childNodes⟩
  apply GeneralBorrowExposedScopedNormal.access tree location protectors source kind mode
    (forest tree location protectors coherent.indexFits depth childData) component
    _ depth childNodes sourceNode sourcePresent
  intro position member _
  change GeneralBorrowGraph.Present tree position at member
  obtain ⟨index, node, rfl, lookup⟩ := member
  obtain ⟨state, stateKnown, localOwn, foreignOwn⟩ := rights index node lookup
  refine ⟨state, ?_, ?_⟩
  · simpa only [projection, projection_location_state tree location protectors index node lookup] using stateKnown
  · change GeneralBorrowPermissions.AccessOwned state kind
      (GeneralBorrowAnchor.relation projection source.toNat index.toNat)
      (projection.protectedNodes.contains index.toNat)
    rw [projected_held tree location protectors index node lookup]
    unfold GeneralBorrowAnchor.relation
    have related := ancestor_iff tree location protectors depth index source sourceNode sourcePresent
    by_cases lineage : Ancestor tree index source
    · rw [ite_eq_left (related.mpr lineage)]
      have owns := localOwn lineage
      cases kind
      · refine ⟨owns.1, ?_⟩
        intro disabled
        simp [localOwns, disabled] at owns
      · exact owns
    · rw [ite_eq_right (fun member => lineage (related.mp member))]
      have owns := foreignOwn lineage
      cases kind <;> exact owns

#print axioms normal_access
#print axioms forest
#print axioms ancestor_iff
end DuplicatePrefix.ArchiveForestProjection

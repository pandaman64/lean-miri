import duplicate_prefix.RetagKeyFrame
import SourceDomain

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowTree BorrowTree.ZeroProtection BorrowTree.MutationVerification Miri.Verification.MutableRetagFootprint
open SourceDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 500000

def graphRow (tree : BorrowTree) (index : UniIndex) : Option (Option UniIndex × Array UniIndex) :=
  (tree.nodeAt index).map fun node => (node.parent, node.children)

def graphView (tree : BorrowTree) : Array UniIndex × Nat × (UniIndex → Option (Option UniIndex × Array UniIndex)) :=
  ⟨tree.roots, tree.nodes.size, graphRow tree⟩

theorem weakened_graph (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess) (found : tree.nodeAt index = some node) :
    graphView (weakened tree index node strongest) = graphView tree := by
  unfold graphView
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact insert_existing_size tree.nodes index node _ found
  · funext query
    unfold graphRow BorrowTree.nodeAt weakened
    dsimp only
    by_cases equal : query = index
    · subst query
      rw [Sparse.get_same, show tree.nodes.get index = some node from found]
      rfl
    · rw [Sparse.get_other _ _ _ _ equal]

def initialChildNode (tag : BorTag) (parent : UniIndex) (outside : Permission) (defaultSifa : IdempotentForeignAccess) : TreeNode :=
  { tag, parent := some parent, children := #[], defaultInitialPermission := outside,
    defaultInitialSifa := defaultSifa, isExposed := false }

def initialChildAttached (tree : BorrowTree) (tag : BorTag) (mapping : UniKeyMap BorTag)
    (child parent : UniIndex) (parentNode : TreeNode) (outside : Permission) (defaultSifa : IdempotentForeignAccess) : BorrowTree :=
  { tree with
    tagMapping := mapping
    nodes := Append.attachedNodes tree.nodes child parent parentNode (initialChildNode tag parent outside defaultSifa) }

/-- Both concrete child mutation stages retain the newly attached graph even
when they update materialized permissions and weaken ancestor SIFA. -/
theorem newChild_graph_initial
    (tree : BorrowTree) (offset : Size) (parentTag tag : BorTag)
    (parent child : UniIndex) (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState)
    (outside : Permission) (held : Bool) (defaultSifa : IdempotentForeignAccess)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (sifa : outside.strongestIdempotentForeignAccess held = .Access defaultSifa)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ()) :
    graphView (tree.newChild offset (.concrete parentTag) tag inside outside held).tree =
      graphView (initialChildAttached tree tag mapping child parent parentNode outside defaultSifa) := by
  let expected := graphView (initialChildAttached tree tag mapping child parent parentNode outside defaultSifa)
  let keep := fun now => graphView now = expected
  have distinct : parent ≠ child := Reuse.parent_not_vacant tree.nodes child parent parentNode vacant present
  have tagLookup : tree.tagMapping.get parentTag = some parent := parentFound
  have pre : insertChildPre tree offset (.concrete parentTag) tag inside outside held
      keep (fun _ => keep) := by
    let attached := initialChildAttached tree tag mapping child parent parentNode outside defaultSifa
    have children : childSegmentsPre offset child (some parent) held keep (fun _ => keep)
        inside.iterAll.toList attached defaultSifa := by
      apply childSegmentsFrame keep (fun _ _ h => h)
        (fun current index node strongest found h => (weakened_graph current index node strongest found).trans h)
      rfl
    have found : tree.nodes.get parent = some parentNode := present
    unfold insertChildPre
    simp only [mapped, tagLookup, Option.map_some, initial, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, nonunique, sifa, finishInsertedChildPre,
      Sparse.get_other _ _ _ _ distinct, found]
    exact children
  have valid := (insertChildPre_iff tree offset (.concrete parentTag) tag inside
    outside held keep (fun _ => keep)).mp pre
  simpa only [childResultPre, complete] using valid

/-- The two actual node-table writes of a concrete attachment alter only
the selected child and the parent's children array. -/
private theorem attached_node_lookup (nodes : UniValMap TreeNode) (parent child query : UniIndex)
    (parentNode childNode : TreeNode) (different : parent ≠ child) :
    (Append.attachedNodes nodes child parent parentNode childNode).get query =
      if query = child then some childNode
      else if query = parent then some {parentNode with children := parentNode.children.push child}
      else nodes.get query := by
  let inserted := nodes.insert child childNode
  let revised := {parentNode with children := parentNode.children.push child}
  change (inserted.insert parent revised).get query = _
  by_cases fresh : query = child
  · subst query
    have out := Sparse.get_other inserted parent child revised (Ne.symm different)
    simpa only [ite_eq_left rfl, ↓reduceIte] using out.trans (Sparse.get_same nodes child childNode)
  · by_cases parentSlot : query = parent
    · subst query
      simpa only [ite_eq_right different, ite_eq_left rfl, ↓reduceIte] using Sparse.get_same inserted parent revised
    · have later := Sparse.get_other inserted parent query revised parentSlot
      have prior := Sparse.get_other nodes child query childNode fresh
      simpa only [ite_eq_right fresh, ite_eq_right parentSlot] using later.trans prior

private theorem paired_nodes (before after : BorrowTree)
    (row : ∀ index, graphRow before index = graphRow after index)
    (index : UniIndex) (node : TreeNode) (found : before.nodeAt index = some node) :
    ∃ seen, after.nodeAt index = some seen ∧ seen.parent = node.parent ∧ seen.children = node.children := by
  have actual := row index
  unfold graphRow at actual
  cases lookup : after.nodeAt index with
  | none => simp [found, lookup] at actual
  | some seen =>
    rw [found, lookup] at actual
    have pair := Option.some.inj actual
    exact ⟨seen, rfl, (congrArg Prod.fst pair).symm, (congrArg Prod.snd pair).symm⟩

private theorem transfer_forest (before after : BorrowTree)
    (shape : graphView before = graphView after) (original : CoherentForest before)
    (well : after.locations.WellFormed) : CoherentForest after := by
  have roots : before.roots = after.roots := congrArg Prod.fst shape
  have sizes : before.nodes.data.size = after.nodes.data.size := congrArg (fun graph => graph.2.1) shape
  have row : ∀ index, graphRow before index = graphRow after index :=
    fun index => congrArg (fun graph => graph.2.2 index) shape
  have paired := paired_nodes before after row
  have reversed := paired_nodes after before (fun index => (row index).symm)
  refine ⟨well, sizes ▸ original.indexFits, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← roots]
    exact original.rootsDistinct
  · intro root member
    rw [← roots] at member
    obtain ⟨node, present⟩ := original.rootsPresent root member
    obtain ⟨seen, found, _, _⟩ := paired root node present
    exact ⟨seen, found⟩
  · obtain ⟨rank, bounded, decreases⟩ := original.parentDepth
    refine ⟨rank, ?_, ?_⟩
    · intro index node found
      obtain ⟨prior, present, _, _⟩ := reversed index node found
      have sizeEq : before.nodes.size = after.nodes.size := sizes
      rw [← sizeEq]
      exact bounded index prior present
    · intro index node parent found edge
      obtain ⟨prior, present, same, _⟩ := reversed index node found
      exact decreases index prior parent present (same.trans edge)
  · intro index node found
    obtain ⟨prior, present, parent, _⟩ := reversed index node found
    rw [← parent, ← roots]
    exact original.rootEdges index prior present
  · intro index node found
    obtain ⟨prior, present, _, children⟩ := reversed index node found
    obtain ⟨unique, forward, backward⟩ := original.childEdges index prior present
    rw [← children]
    refine ⟨unique, ?_, ?_⟩
    · intro child member
      obtain ⟨oldChild, raw, edge⟩ := forward child member
      obtain ⟨newChild, computed, parent, _⟩ := paired child oldChild raw
      exact ⟨newChild, computed, parent.trans edge⟩
    · intro child data located edge
      obtain ⟨oldChild, raw, parent, _⟩ := reversed child data located
      exact backward child oldChild raw (parent.trans edge)
  · intro index node parent found edge
    obtain ⟨prior, present, parentEq, _⟩ := reversed index node found
    obtain ⟨oldParent, raw⟩ := original.parentPresent index prior parent present (parentEq.trans edge)
    obtain ⟨newParent, computed, _, _⟩ := paired parent oldParent raw
    exact ⟨newParent, computed⟩

private theorem attached_observations_forest
    (tree next : BorrowTree) (tag : BorTag) (parent child : UniIndex) (outside : Permission) (defaultSifa : IdempotentForeignAccess)
    (coherent : CoherentForest tree) (sameRoots : next.roots = tree.roots)
    (ranges : next.locations.WellFormed) (indexFit : next.nodes.data.size ≤ 2 ^ 32)
    (ranked : ParentDepth next.nodes) (different : parent ≠ child)
    (vacant : tree.nodeAt child = none)
    (installed : next.nodeAt child = some (initialChildNode tag parent outside defaultSifa))
    (retained : ∀ index old, tree.nodeAt index = some old →
      next.nodeAt index = some { old with children :=
        if index = parent then old.children.push child else old.children })
    (original : ∀ index data, index ≠ child → next.nodeAt index = some data →
      ∃ old, tree.nodeAt index = some old ∧ data.parent = old.parent ∧ data.children =
        (if index = parent then old.children.push child else old.children)) :
    CoherentForest next := by
  let node := initialChildNode tag parent outside defaultSifa
  let extendChildren := fun i (old : TreeNode) =>
    if i = parent then old.children.push child else old.children
  have oldChild : ∀ index old, tree.nodeAt index = some old → ∀ childIndex ∈ old.children, childIndex ≠ child := by
    intro index old stored childIndex member same
    subst childIndex
    obtain ⟨previous, found, _⟩ := (coherent.childEdges index old stored).2.1 child member
    rw [vacant] at found
    contradiction
  refine ⟨ranges, indexFit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sameRoots]
    exact coherent.rootsDistinct
  · intro index member
    rw [sameRoots] at member
    obtain ⟨old, found⟩ := coherent.rootsPresent index member
    exact ⟨_, retained index old found⟩
  · exact ⟨ranked.depth, ranked.bounded, fun index data prior found edge => (ranked.parent index data found prior edge).choose_spec.2⟩
  · intro index data found
    by_cases new : index = child
    · subst index
      have same := Option.some.inj (found.symm.trans installed)
      subst data
      constructor
      · intro impossible
        cases impossible
      · intro lands
        rw [sameRoots] at lands
        obtain ⟨_, seen⟩ := coherent.rootsPresent child lands
        rw [vacant] at seen
        contradiction
    · obtain ⟨old, located, parentEq, _⟩ := original index data new found
      rw [parentEq, sameRoots]
      exact coherent.rootEdges index old located
  · intro index data found
    by_cases new : index = child
    · subst index
      have same := Option.some.inj (found.symm.trans installed)
      subst data
      refine ⟨by simp [initialChildNode], ?_, ?_⟩
      · intro _ member
        simp [initialChildNode] at member
      · intro query queryNode known edge
        by_cases isChild : query = child
        · subst query
          have same := Option.some.inj (known.symm.trans installed)
          subst queryNode
          exact False.elim (different (Option.some.inj edge))
        · obtain ⟨old, located, parentEq, _⟩ := original query queryNode isChild known
          obtain ⟨_, parentKnown⟩ := coherent.parentPresent query old child located (parentEq.symm.trans edge)
          rw [vacant] at parentKnown
          contradiction
    · obtain ⟨old, located, _, children⟩ := original index data new found
      have previous := coherent.childEdges index old located
      rw [children]
      refine ⟨?_, ?_, ?_⟩
      · by_cases isParent : index = parent
        · simp only [ite_eq_left isParent, Array.toList_push, List.nodup_append]
          refine ⟨previous.1, by simp, ?_⟩
          intro query member inserted proposed
          have same : inserted = child := List.mem_singleton.mp proposed
          subst inserted
          exact oldChild index old located query (by simpa using member)
        · simpa only [extendChildren, ite_eq_right isParent] using previous.1
      · intro query member
        by_cases same : query = child
        · subst query
          have isParent : index = parent := by
            by_cases position : index = parent
            · exact position
            · have oldMember : child ∈ old.children := by
                simpa only [extendChildren, ite_eq_right position] using member
              exact False.elim (oldChild index old located child oldMember rfl)
          exact ⟨node, installed, congrArg some isParent.symm⟩
        · have oldMember : query ∈ old.children := by
            by_cases isParent : index = parent
            · simpa [extendChildren, isParent, same] using member
            · simpa [isParent] using member
          obtain ⟨prior, known, edge⟩ := previous.2.1 query oldMember
          exact ⟨_, retained query prior known, edge⟩
      · intro query queryNode known edge
        by_cases same : query = child
        · subst query
          have equal := Option.some.inj (known.symm.trans installed)
          subst queryNode
          have isParent : index = parent := (Option.some.inj edge).symm
          simp [isParent]
        · obtain ⟨prior, recorded, parentEq, _⟩ := original query queryNode same known
          have oldMember := previous.2.2 query prior recorded (parentEq.symm.trans edge)
          by_cases isParent : index = parent <;> simp [isParent, oldMember]
  · intro index data previous found edge
    obtain ⟨parent, known, _⟩ := ranked.parent index data found previous edge
    exact ⟨parent, known⟩


private theorem attach_rows
    (tree next : BorrowTree) (parent child : UniIndex) (parentNode node : TreeNode)
    (present : tree.nodeAt parent = some parentNode) (vacant : tree.nodeAt child = none)
    (slots : ∀ query : UniIndex, next.nodeAt query = if query = child then some node
      else if query = parent then some {parentNode with children := parentNode.children.push child}
      else tree.nodeAt query) :
    (∀ index old, tree.nodeAt index = some old →
      next.nodeAt index = some { old with children :=
        if index = parent then old.children.push child else old.children }) ∧
    (∀ index data, index ≠ child → next.nodeAt index = some data →
      ∃ old, tree.nodeAt index = some old ∧ data.parent = old.parent ∧ data.children =
        (if index = parent then old.children.push child else old.children)) := by
  let extendChildren := fun i (old : TreeNode) =>
    if i = parent then old.children.push child else old.children
  have retained : ∀ index old, tree.nodeAt index = some old →
      next.nodeAt index = some { old with children := extendChildren index old } := by
    intro index old known
    have oldSlot : index ≠ child := by
      intro same
      rw [same, vacant] at known
      contradiction
    by_cases same : index = parent
    · have equal : old = parentNode := Option.some.inj (known.symm.trans (by simpa only [same] using present))
      subst old
      have lookup := slots index
      rw [ite_eq_right oldSlot, ite_eq_left same] at lookup
      simpa only [extendChildren, ite_eq_left same, ↓reduceIte] using lookup
    · have lookup := slots index
      rw [ite_eq_right oldSlot, ite_eq_right same] at lookup
      simpa only [extendChildren, ite_eq_right same] using lookup.trans known
  have original : ∀ index data, index ≠ child → next.nodeAt index = some data →
      ∃ old, tree.nodeAt index = some old ∧ data.parent = old.parent ∧ data.children = extendChildren index old := by
    intro index data oldSlot found
    cases known : tree.nodeAt index with
    | none =>
      have notParent : index ≠ parent := by
        intro same
        rw [same, present] at known
        contradiction
      have lookup := slots index
      rw [ite_eq_right oldSlot, ite_eq_right notParent, known] at lookup
      exact False.elim (Option.some_ne_none data (found.symm.trans lookup))
    | some old =>
      have same := Option.some.inj ((retained index old known).symm.trans found)
      exact ⟨old, rfl, (congrArg TreeNode.parent same).symm, (congrArg TreeNode.children same).symm⟩
  exact ⟨retained, original⟩

private theorem attached_rank
    (nodes : UniValMap TreeNode) (parent child : UniIndex) (parentNode node : TreeNode)
    (depth : ParentDepth nodes)
    (rank : depth.depth parent < nodes.size) (parentEdge : node.parent = some parent)
    (present : nodes.get parent = some parentNode) (vacant : nodes.get child = none)
    (validSlot : child.toNat ≤ nodes.size) (indexFit : nodes.data.size ≤ 2 ^ 32) :
    let attached := Append.attachedNodes nodes child parent parentNode node
    Nonempty (ParentDepth attached) ∧ attached.data.size ≤ 2 ^ 32 := by
  let attached := Append.attachedNodes nodes child parent parentNode node
  have different := Reuse.parent_not_vacant nodes child parent parentNode vacant present
  let inserted := nodes.insert child node
  let revised := {parentNode with children := parentNode.children.push child}
  have earlier : inserted.get parent = some parentNode :=
    (Sparse.get_other nodes child parent node different).trans present
  have sizeSame : attached.data.size = inserted.data.size :=
    insert_existing_size inserted parent parentNode revised earlier
  by_cases reuse : child.toNat < nodes.size
  · have same : inserted.data.size = nodes.data.size := Reuse.bounded_size nodes child node reuse
    exact ⟨⟨Reuse.attached_depth nodes depth child parent parentNode node reuse vacant present
      parentEdge rank⟩, (sizeSame.trans same).symm ▸ indexFit⟩
  · have append : child.toNat = nodes.data.size := by
      change child.toNat = nodes.size
      omega
    have sizeStep : inserted.data.size = nodes.data.size + 1 :=
      Append.append_size nodes child node append
    have fit : child.toNat < 2 ^ 32 := child.idx.toNat_lt
    have bound : nodes.data.size + 1 ≤ 2 ^ 32 := by omega
    exact ⟨⟨Append.attached_depth nodes depth child parent parentNode node append present parentEdge⟩,
      (sizeSame.trans sizeStep).symm ▸ bound⟩

private theorem attached_forest
    (tree : BorrowTree) (tag : BorTag) (mapping : UniKeyMap BorTag)
    (parent child : UniIndex) (parentNode : TreeNode) (outside : Permission) (defaultSifa : IdempotentForeignAccess)
    (coherent : CoherentForest tree) (depth : ParentDepth tree.nodes)
    (rank : depth.depth parent < tree.nodes.size)
    (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none) (validSlot : child.toNat ≤ tree.nodes.size) :
    CoherentForest (initialChildAttached tree tag mapping child parent parentNode outside defaultSifa) := by
  let node := initialChildNode tag parent outside defaultSifa
  generalize substituted : initialChildAttached tree tag mapping child parent parentNode outside defaultSifa = next
  have nodes : next.nodes = Append.attachedNodes tree.nodes child parent parentNode node := by
    simp only [← substituted, initialChildAttached, node]
  have sameRoots : next.roots = tree.roots := by
    simp only [← substituted, initialChildAttached]
  have ranges : next.locations.WellFormed := by
    simpa only [← substituted, initialChildAttached] using coherent.ranges
  have different : parent ≠ child := Reuse.parent_not_vacant tree.nodes child parent parentNode vacant present
  have slots (query : UniIndex) :
      next.nodeAt query = if query = child then some node
      else if query = parent then some {parentNode with children := parentNode.children.push child}
      else tree.nodeAt query := by
    unfold BorrowTree.nodeAt
    rw [nodes]
    exact attached_node_lookup tree.nodes parent child query parentNode node different
  have installed : next.nodeAt child = some node := by
    simpa only [ite_eq_left rfl, ↓reduceIte] using slots child
  have rows := attach_rows tree next parent child parentNode node present vacant slots
  have depthFits : Nonempty (ParentDepth next.nodes) ∧ next.nodes.data.size ≤ 2 ^ 32 := by
    rw [nodes]
    exact attached_rank tree.nodes parent child parentNode node depth rank rfl present vacant validSlot
      coherent.indexFits
  obtain ⟨⟨ranked⟩, indexFit⟩ := depthFits
  exact attached_observations_forest tree next tag parent child outside defaultSifa coherent sameRoots ranges
    indexFit ranked different vacant installed rows.1 rows.2

/-- A completed concrete child insertion preserves the forest and its roots.
The allocator supplies a vacant in-bounds child slot and the pre-existing
rank certificate supplies a terminating path to the selected parent. -/
theorem initial_child_coherent
    (tree : BorrowTree) (offset : Size) (parentTag tag : BorTag)
    (parent child : UniIndex) (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState)
    (outside : Permission) (held : Bool) (defaultSifa : IdempotentForeignAccess)
    (initial : outside.isInitial = true) (nonunique : outside.isUnique = false)
    (sifa : outside.strongestIdempotentForeignAccess held = .Access defaultSifa)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none) (slot : child.toNat ≤ tree.nodes.size)
    (coherent : CoherentForest tree) (rankTree : ParentDepth tree.nodes)
    (rank : rankTree.depth parent < tree.nodes.size)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ())
    (well : (tree.newChild offset (.concrete parentTag) tag inside outside held).tree.locations.WellFormed) :
    let after := (tree.newChild offset (.concrete parentTag) tag inside outside held).tree
    CoherentForest after ∧ after.roots = tree.roots := by
  have graph := newChild_graph_initial tree offset parentTag tag parent child mapping inside
    outside held defaultSifa initial nonunique sifa mapped parentFound parentNode present vacant complete
  have pure := attached_forest tree tag mapping parent child parentNode outside defaultSifa
    coherent rankTree rank present vacant slot
  exact ⟨transfer_forest _ _ graph.symm pure well, congrArg Prod.fst graph⟩

theorem frozen_child_coherent_with_mode
    (tree : BorrowTree) (offset : Size) (parentTag tag : BorTag)
    (parent child : UniIndex) (mapping : UniKeyMap BorTag) (inside : DedupRangeMap LocationState) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none) (slot : child.toNat ≤ tree.nodes.size)
    (coherent : CoherentForest tree) (rankTree : ParentDepth tree.nodes)
    (rank : rankTree.depth parent < tree.nodes.size)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).outcome = .ok ())
    (well : (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree.locations.WellFormed) :
    let after := (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).tree
    CoherentForest after ∧ after.roots = tree.roots :=
  initial_child_coherent tree offset parentTag tag parent child mapping inside (.ReservedFrz false) held
    (if held then .None else .Read) rfl rfl (by cases held <;> rfl)
    mapped parentFound parentNode present vacant slot coherent rankTree rank complete well

end DuplicatePrefix.ArchiveForestProjection

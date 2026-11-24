import Miri.TreeBorrows.LocationState

/-!
Finite tree-visitor schedule from pinned Miri
tree_borrows/tree_visitor.rs. This models the normal-tree visitation order
and the precise local/foreign relation used at each node. A tree is assumed to
be a valid finite rooted tree, as it is at Miri's visitor call sites.
Allocation ranges, wildcard subtrees, exposed caches, and diagnostics are
outside this traversal schedule.
-/

namespace Miri.TreeBorrows

namespace Tree

/-- Whether to visit the accessed node's direct children. -/
inductive ChildrenVisitMode where
  | VisitChildrenOfAccessed
  | SkipChildrenOfAccessed
  deriving DecidableEq, Repr, Inhabited

/-- Ordered parent/child links used by Miri's normal tree visitor. -/
structure TraversalNode where
  parent : Option Nat
  children : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- A finite tree indexed by its node positions. -/
structure TraversalTree where
  nodes : Array TraversalNode
  deriving DecidableEq, Repr, Inhabited

/-- One node visit and the access relation passed to the location transition. -/
structure TraversalEvent where
  node : Nat
  relatedness : AccessRelatedness
  deriving DecidableEq, Repr

namespace TraversalTree

/-- Look up a traversal node, with an isolated empty node for a missing index. -/
def nodeAt (tree : TraversalTree) (index : Nat) : TraversalNode :=
  tree.nodes[index]?.getD ⟨none, []⟩

/-- The start node followed by its successive parents, through the root. -/
private def ancestorPathAux (tree : TraversalTree) : Nat → Nat → List Nat
  | 0, current => [current]
  | fuel + 1, current =>
      match (nodeAt tree current).parent with
      | none => [current]
      | some parent => current :: ancestorPathAux tree fuel parent

def ancestorPath (tree : TraversalTree) (start : Nat) : List Nat :=
  ancestorPathAux tree tree.nodes.size start

private theorem ancestorPathAux_head (tree : TraversalTree) (fuel : Nat)
    (current : Nat) :
    (ancestorPathAux tree fuel current).head? = some current := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases h : (nodeAt tree current).parent <;> simp [ancestorPathAux, h]

theorem ancestorPath_head (tree : TraversalTree) (start : Nat) :
    (ancestorPath tree start).head? = some start := by
  exact ancestorPathAux_head tree tree.nodes.size start

/-- Initial foreign roots are pushed in the same order as the source visitor:
first the accessed node's children in reverse order, then sibling subtrees
of each successive parent. -/
private def initialForeignRoots (tree : TraversalTree)
    (path : List Nat) (mode : ChildrenVisitMode) : List Nat :=
  go path none true
where
  go (remaining : List Nat) (previous : Option Nat) (isStart : Bool) : List Nat :=
    match remaining with
    | [] => []
    | current :: rest =>
        let shouldVisitChildren := !isStart || mode == .VisitChildrenOfAccessed
        let siblings :=
          if shouldVisitChildren then
            ((nodeAt tree current).children.reverse).filter
              (fun child => previous != some child)
          else []
        siblings ++ go rest (some current) false

/-- Bottom-up foreign subtree events. The finite fuel corresponds to the
height bound of a valid rooted tree; a skipped node prunes itself and all
descendants, matching the source SkipSelfAndChildren result. -/
private def foreignPostorder (tree : TraversalTree) (shouldSkip : Nat → Bool) :
    Nat → Nat → List TraversalEvent
  | 0, _ => []
  | fuel + 1, index =>
      if shouldSkip index then []
      else
        let children := (nodeAt tree index).children.reverse
        children.flatMap (foreignPostorder tree shouldSkip fuel) ++
          [⟨index, .ForeignAccess⟩]

/-- Schedule the start and its ancestors first, then visit deferred subtrees
bottom-up. Query the foreign-only skip predicate at each reached subtree root. -/
def traverseWithSkip (tree : TraversalTree) (start : Nat)
    (mode : ChildrenVisitMode) (shouldSkip : Nat → Bool) :
    Nat × List TraversalEvent :=
  let path := ancestorPath tree start
  let root := path.getLast!
  let localEvents := path.map (fun index => ⟨index, .LocalAccess⟩)
  let foreignRoots := initialForeignRoots tree path mode
  let foreignEvents :=
    foreignRoots.flatMap (foreignPostorder tree shouldSkip tree.nodes.size)
  (root, localEvents ++ foreignEvents)

/-- A foreign branch starts at an allowed child of the accessed node, or a
child of a higher ancestor other than the child leading back to the access. -/
inductive ForeignBranch (tree : TraversalTree) (mode : ChildrenVisitMode) :
    List Nat → Option Nat → Bool → Nat → Prop where
  | here {current rest previous isStart branch}
      (enter : !isStart || mode == .VisitChildrenOfAccessed)
      (child : branch ∈ (nodeAt tree current).children) (offPath : previous ≠ some branch) :
      ForeignBranch tree mode (current :: rest) previous isStart branch
  | above {current rest previous isStart branch}
      (higher : ForeignBranch tree mode rest (some current) false branch) :
      ForeignBranch tree mode (current :: rest) previous isStart branch

/-- A path through a foreign subtree which stays inside the traversal depth
bound and passes the pruning check at every node, including both ends. -/
inductive UnprunedPath (tree : TraversalTree) (skip : Nat → Bool) : Nat → Nat → Nat → Prop where
  | here {fuel node} (enter : skip node = false) : UnprunedPath tree skip (fuel + 1) node node
  | child {fuel node next target} (enter : skip node = false)
      (edge : next ∈ (nodeAt tree node).children)
      (reaches : UnprunedPath tree skip fuel next target) :
      UnprunedPath tree skip (fuel + 1) node target

private theorem foreignRoots_iff (tree : TraversalTree) (mode : ChildrenVisitMode)
    (path : List Nat) (previous : Option Nat) (isStart : Bool) (branch : Nat) :
    branch ∈ initialForeignRoots.go tree mode path previous isStart ↔
      ForeignBranch tree mode path previous isStart branch := by
  induction path generalizing previous isStart with
  | nil =>
    simp only [initialForeignRoots.go, List.not_mem_nil, false_iff]
    intro impossible
    cases impossible
  | cons current rest ih =>
    rw [initialForeignRoots.go, List.mem_append, ih]
    constructor
    · rintro (chosen | higher)
      · by_cases enter : (!isStart || mode == .VisitChildrenOfAccessed) = true
        · simp [enter, bne_iff_ne] at chosen
          exact .here enter chosen.1 chosen.2
        · simp [enter] at chosen
      · exact .above higher
    · intro chosen
      cases chosen with
      | here enter child offPath => exact Or.inl (by simp [enter, bne_iff_ne, child, offPath])
      | above higher => exact Or.inr higher

private theorem foreignPostorder_iff (tree : TraversalTree) (skip : Nat → Bool)
    (fuel start target : Nat) :
    (⟨target, .ForeignAccess⟩ : TraversalEvent) ∈ tree.foreignPostorder skip fuel start ↔
      UnprunedPath tree skip fuel start target := by
  induction fuel generalizing start with
  | zero =>
    simp only [foreignPostorder, List.not_mem_nil, false_iff]
    intro impossible
    cases impossible
  | succ fuel ih =>
    constructor
    · intro visit
      cases enter : skip start with
      | true => simp [foreignPostorder, enter] at visit
      | false =>
        simp only [foreignPostorder, enter, Bool.false_eq_true, ↓reduceIte, List.mem_append,
          List.mem_flatMap, List.mem_reverse, List.mem_singleton] at visit
        rcases visit with ⟨next, edge, reaches⟩ | same
        · exact .child enter edge ((ih next).mp reaches)
        · cases same
          exact .here enter
    · intro reaches
      cases reaches with
      | here enter => simp [foreignPostorder, enter]
      | child enter edge reaches =>
        simp only [foreignPostorder, enter, Bool.false_eq_true, ↓reduceIte, List.mem_append,
          List.mem_flatMap, List.mem_reverse, List.mem_singleton]
        exact Or.inl ⟨_, edge, (ih _).mpr reaches⟩

private theorem foreignPostorder_no_local (tree : TraversalTree) (skip : Nat → Bool)
    (fuel root target : Nat) :
    (⟨target, .LocalAccess⟩ : TraversalEvent) ∉ tree.foreignPostorder skip fuel root := by
  intro reaches
  induction fuel generalizing root with
  | zero => simp [foreignPostorder] at reaches
  | succ fuel ih =>
    by_cases enter : skip root = true
    · simp [foreignPostorder, enter] at reaches
    · simp only [foreignPostorder, enter, ↓reduceIte, List.mem_append, List.mem_flatMap,
        List.mem_singleton, TraversalEvent.mk.injEq, reduceCtorEq, and_false, or_false] at reaches
      obtain ⟨child, _, reaches⟩ := reaches
      exact ih child reaches

/-- Local selection depends only on the accessed node's ancestor path. -/
@[simp] theorem local_visit_iff (tree : TraversalTree) (start target : Nat)
    (mode : ChildrenVisitMode) (skip : Nat → Bool) :
    (⟨target, .LocalAccess⟩ : TraversalEvent) ∈ (tree.traverseWithSkip start mode skip).2 ↔
      target ∈ tree.ancestorPath start := by
  simp [traverseWithSkip, foreignPostorder_no_local]

/-- Foreign selection follows an eligible branch from the ancestor path and
requires an unpruned child chain to the target. -/
@[simp] theorem foreign_visit_iff (tree : TraversalTree) (start target : Nat)
    (mode : ChildrenVisitMode) (skip : Nat → Bool) :
    (⟨target, .ForeignAccess⟩ : TraversalEvent) ∈ (tree.traverseWithSkip start mode skip).2 ↔
      ∃ branch, ForeignBranch tree mode (tree.ancestorPath start) none true branch ∧
        UnprunedPath tree skip tree.nodes.size branch target := by
  simp [traverseWithSkip, initialForeignRoots, foreignRoots_iff, foreignPostorder_iff]

private theorem foreignPostorder_notSkipped (tree : TraversalTree) (skip : Nat → Bool)
    (fuel index : Nat) (event : TraversalEvent)
    (visited : event ∈ tree.foreignPostorder skip fuel index) : skip event.node = false := by
  induction fuel generalizing index with
  | zero => simp [foreignPostorder] at visited
  | succ fuel ih =>
    by_cases omitted : skip index = true
    · simp [foreignPostorder, omitted] at visited
    · have notSkipped := Bool.eq_false_iff.mpr omitted
      simp only [foreignPostorder, notSkipped, Bool.false_eq_true, ↓reduceIte, List.mem_append,
        List.mem_flatMap, List.mem_singleton] at visited
      rcases visited with ⟨child, _, reaches⟩ | atIndex
      · exact ih child reaches
      · subst event
        exact notSkipped

/-- Every generated foreign event passed the traversal's initial pruning
test. Local events bypass that test. -/
theorem traverseWithSkip_foreign_notSkipped (tree : TraversalTree)
    (start : Nat) (mode : ChildrenVisitMode) (skip : Nat → Bool) (event : TraversalEvent)
    (visited : event ∈ (tree.traverseWithSkip start mode skip).2)
    (foreign : event.relatedness = .ForeignAccess) :
    skip event.node = false := by
  simp only [traverseWithSkip, List.mem_append, List.mem_map, List.mem_flatMap] at visited
  rcases visited with ⟨localNode, _, equal⟩ | ⟨root, _, reaches⟩
  · subst event
    cases foreign
  · exact foreignPostorder_notSkipped tree skip _ root event reaches

/-- Schedule a normal access with an explicit set of foreign nodes to skip. -/
def traverse (tree : TraversalTree) (start : Nat)
    (mode : ChildrenVisitMode) (skipNodes : List Nat) :
    Nat × List TraversalEvent :=
  tree.traverseWithSkip start mode skipNodes.contains

/-- The source visitor always propagates at the accessed node first. -/
theorem traverse_starts_at_accessed_node (tree : TraversalTree) (start : Nat)
    (mode : ChildrenVisitMode) (skipNodes : List Nat) :
    (traverse tree start mode skipNodes).2.head? =
      some ⟨start, .LocalAccess⟩ := by
  simp [traverse, traverseWithSkip, ancestorPath_head]

private def flatMapPre {A B : Type} (step : A → (List B → Prop) → Prop) :
    List A → (List B → Prop) → Prop
  | [], finish => finish []
  | head :: tail, finish => step head (fun first =>
      flatMapPre step tail (fun rest => finish (first ++ rest)))

private theorem flatMapPre_iff {A B : Type} (run : A → List B)
    (step : A → (List B → Prop) → Prop)
    (exactStep : ∀ value finish, step value finish ↔ finish (run value))
    (items : List A) (finish : List B → Prop) :
    flatMapPre step items finish ↔ finish (items.flatMap run) := by
  induction items generalizing finish with
  | nil => rfl
  | cons head tail ih =>
    rw [flatMapPre, exactStep, ih]
    rfl

private def foreignPostorderPre (tree : TraversalTree) (shouldSkip : Nat → Bool) :
    Nat → Nat → (List TraversalEvent → Prop) → Prop
  | 0, _, finish => finish []
  | fuel + 1, index, finish =>
    if shouldSkip index then finish []
    else
      flatMapPre (foreignPostorderPre tree shouldSkip fuel) (nodeAt tree index).children.reverse
        (fun children => finish (children ++ [⟨index, .ForeignAccess⟩]))

private theorem foreignPostorderPre_iff (tree : TraversalTree) (shouldSkip : Nat → Bool)
    (fuel index : Nat) (finish : List TraversalEvent → Prop) :
    foreignPostorderPre tree shouldSkip fuel index finish ↔
      finish (foreignPostorder tree shouldSkip fuel index) := by
  induction fuel generalizing index finish with
  | zero => rfl
  | succ fuel ih =>
    simp only [foreignPostorderPre, foreignPostorder]
    cases skip : shouldSkip index with
    | true => rfl
    | false =>
      simpa only [skip, Bool.false_eq_true, ↓reduceIte] using
        (flatMapPre_iff (foreignPostorder tree shouldSkip fuel)
          (foreignPostorderPre tree shouldSkip fuel) ih (nodeAt tree index).children.reverse
          (fun children => finish (children ++ [⟨index, .ForeignAccess⟩])))

/-- Pull back through the exact normal visit schedule. The skip predicate is
consulted only for each reached foreign subtree, before visiting its children. -/
def traverseWithSkipPre (tree : TraversalTree) (start : Nat) (mode : ChildrenVisitMode)
    (shouldSkip : Nat → Bool) (finish : Nat → List TraversalEvent → Prop) : Prop :=
  let path := ancestorPath tree start
  let localEvents := path.map (fun index => ⟨index, .LocalAccess⟩)
  flatMapPre (foreignPostorderPre tree shouldSkip tree.nodes.size)
    (initialForeignRoots tree path mode)
    (fun foreignEvents => finish path.getLast! (localEvents ++ foreignEvents))

theorem traverseWithSkipPre_iff (tree : TraversalTree) (start : Nat) (mode : ChildrenVisitMode)
    (shouldSkip : Nat → Bool) (finish : Nat → List TraversalEvent → Prop) :
    traverseWithSkipPre tree start mode shouldSkip finish ↔
      let visit := tree.traverseWithSkip start mode shouldSkip
      finish visit.1 visit.2 := by
  unfold traverseWithSkipPre traverseWithSkip
  exact flatMapPre_iff _ _ (foreignPostorderPre_iff tree shouldSkip tree.nodes.size) _ _

set_option autoImplicit false in
/-- Addresses of linked nodes extend their parent's address by the child's index.
Consistent links and duplicate-free child lists suffice for unique visits. -/
structure Addressed (tree : TraversalTree) where
  address : Nat → List Nat
  childrenOnce : ∀ parent, (tree.nodeAt parent).children.Nodup
  childAddress : ∀ {parent child}, child ∈ (tree.nodeAt parent).children →
    address child = address parent ++ [child]
  parentAddress : ∀ {parent child}, (tree.nodeAt child).parent = some parent →
    address child = address parent ++ [child]

private theorem separate_children {path target : List Nat} {left right : Nat}
    (h₁ : path ++ [left] <+: target) (h₂ : path ++ [right] <+: target) : left = right := by
  rcases List.prefix_or_prefix_of_prefix h₁ h₂ with h | h
  · simpa using List.prefix_append_right_inj path |>.mp h
  · symm
    simpa using List.prefix_append_right_inj path |>.mp h

private theorem parent_outside_child {path target : List Nat} {child : Nat}
    (strict : path ++ [child] <+: target) : ¬ target <+: path := by
  intro other
  have longer := strict.length_le
  have shorter := other.length_le
  simp at longer
  omega

private theorem postorder_under {tree : TraversalTree} (shape : tree.Addressed)
    (skip : Nat → Bool) (fuel : Nat) {root node : Nat}
    (mem : node ∈ (tree.foreignPostorder skip fuel root).map (·.node)) :
    shape.address root <+: shape.address node := by
  induction fuel generalizing root with
  | zero => simp [foreignPostorder] at mem
  | succ fuel ih =>
    cases omitted : skip root
    · simp [foreignPostorder, omitted, List.map_flatMap] at mem
      rcases mem with ⟨child, edge, below⟩ | rfl
      · exact (by rw [shape.childAddress edge]; exact List.prefix_append _ _
          : shape.address root <+: shape.address child).trans (ih (List.mem_map.mpr below))
      · exact List.prefix_rfl
    · simp [foreignPostorder, omitted] at mem

private theorem children_postorder_once {tree : TraversalTree} (shape : tree.Addressed)
    (skip : Nat → Bool) (fuel parent : Nat) (children : List Nat)
    (edges : ∀ child ∈ children, child ∈ (tree.nodeAt parent).children)
    (once : children.Nodup)
    (each : ∀ child, ((tree.foreignPostorder skip fuel child).map (·.node)).Nodup) :
    (children.flatMap (fun child => (tree.foreignPostorder skip fuel child).map (·.node))).Nodup := by
  refine List.pairwise_flatMap.mpr ⟨fun child _ => each child, ?_⟩
  refine once.imp_of_mem ?_
  intro left right leftMember rightMember distinct node inLeft other inRight same
  subst other
  apply distinct
  have leftBelow := postorder_under shape skip fuel inLeft
  have rightBelow := postorder_under shape skip fuel inRight
  rw [shape.childAddress (edges left leftMember)] at leftBelow
  rw [shape.childAddress (edges right rightMember)] at rightBelow
  exact separate_children leftBelow rightBelow

private theorem postorder_once {tree : TraversalTree} (shape : tree.Addressed)
    (skip : Nat → Bool) (fuel root : Nat) :
    ((tree.foreignPostorder skip fuel root).map (·.node)).Nodup := by
  induction fuel generalizing root with
  | zero => simp [foreignPostorder]
  | succ fuel ih =>
    cases omitted : skip root
    · simp only [foreignPostorder, omitted, Bool.false_eq_true, ↓reduceIte, List.map_append,
        List.map_flatMap, List.map_cons, List.map_nil, List.nodup_append]
      refine ⟨children_postorder_once shape skip fuel root _ (by simp)
        (by rw [List.Nodup, List.pairwise_reverse]; exact (shape.childrenOnce root).imp Ne.symm) ih, by simp, ?_⟩
      simp only [List.mem_flatMap, List.mem_reverse, List.mem_singleton, forall_eq]
      rintro node ⟨child, edge, member⟩ rfl
      have below := postorder_under shape skip fuel member
      rw [shape.childAddress edge] at below
      exact parent_outside_child below List.prefix_rfl
    · simp [foreignPostorder, omitted]

private theorem path_schedule_once {tree : TraversalTree} (shape : tree.Addressed)
    (mode : ChildrenVisitMode) (skip : Nat → Bool) (fuel : Nat)
    (path : List Nat) (current : Nat) (previous : Option Nat) (isStart : Bool)
    (previousAddress : ∀ p, previous = some p → shape.address p = shape.address current ++ [p])
    (higherOnce :
      (path ++ ((initialForeignRoots.go tree mode path (some current) false).flatMap
        (tree.foreignPostorder skip fuel)).map (·.node)).Nodup)
    (higherOutside : ∀ node ∈ path ++ ((initialForeignRoots.go tree mode path (some current)
        false).flatMap (tree.foreignPostorder skip fuel)).map (·.node),
      ¬ shape.address current <+: shape.address node) :
    let nodes := (current :: path) ++ ((initialForeignRoots.go tree mode (current :: path)
      previous isStart).flatMap (tree.foreignPostorder skip fuel)).map (·.node)
    nodes.Nodup ∧ ∀ p, previous = some p → ∀ node ∈ nodes,
      ¬ shape.address p <+: shape.address node := by
  let children := if !isStart || mode == .VisitChildrenOfAccessed then
    (tree.nodeAt current).children.reverse.filter (fun child => previous != some child)
    else []
  let visits := children.flatMap (fun child => (tree.foreignPostorder skip fuel child).map (·.node))
  let higher := ((initialForeignRoots.go tree mode path (some current) false).flatMap
    (tree.foreignPostorder skip fuel)).map (·.node)
  have reorder : ((current :: path) ++ ((initialForeignRoots.go tree mode (current :: path)
      previous isStart).flatMap (tree.foreignPostorder skip fuel)).map (·.node)).Perm
      ((current :: visits) ++ (path ++ higher)) := by
    simp only [initialForeignRoots.go, List.flatMap_append, List.map_append, List.cons_append]
    change (current :: (path ++
      ((children.flatMap (tree.foreignPostorder skip fuel)).map TraversalEvent.node ++ higher))).Perm
      (current :: (visits ++ (path ++ higher)))
    rw [List.map_flatMap]
    simpa only [List.append_assoc] using
      (((List.perm_append_comm : (path ++ visits).Perm (visits ++ path)).append_right higher).cons current)
  have edgeAndOff : ∀ child ∈ children,
      child ∈ (tree.nodeAt current).children ∧ previous ≠ some child := by
    intro child member
    by_cases enter : (!isStart || mode == .VisitChildrenOfAccessed) = true
    · simpa [children, enter, bne_iff_ne] using member
    · simp [children, enter] at member
  have underChild : ∀ node ∈ visits, ∃ child ∈ children,
      shape.address current ++ [child] <+: shape.address node := by
    intro node member
    obtain ⟨child, edge, below⟩ := List.mem_flatMap.mp member
    exact ⟨child, edge, shape.childAddress (edgeAndOff child edge).1 ▸
      postorder_under shape skip fuel below⟩
  have underCurrent : ∀ node ∈ current :: visits, shape.address current <+: shape.address node := by
    intro node member
    rcases List.mem_cons.mp member with rfl | below
    · exact List.prefix_rfl
    · obtain ⟨child, _, descendant⟩ := underChild node below
      exact (List.prefix_append _ _).trans descendant
  refine ⟨reorder.nodup_iff.mpr ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨List.nodup_cons.mpr ⟨?_, ?_⟩, higherOnce, ?_⟩
    · intro member
      obtain ⟨_, _, descendant⟩ := underChild current member
      exact parent_outside_child descendant List.prefix_rfl
    · refine children_postorder_once shape skip fuel current children (fun child edge =>
        (edgeAndOff child edge).1) ?_ (postorder_once shape skip fuel)
      by_cases enter : (!isStart || mode == .VisitChildrenOfAccessed) = true
      · simp only [children, enter, ↓reduceIte]
        apply List.Pairwise.filter
        rw [List.pairwise_reverse]
        exact (shape.childrenOnce current).imp Ne.symm
      · simp [children, enter]
    · rintro node member _ above rfl
      exact higherOutside node above (underCurrent node member)
  · intro p linked node member reaches
    have extend := previousAddress p linked
    rcases List.mem_append.mp (reorder.mem_iff.mp member) with here | above
    · rcases List.mem_cons.mp here with rfl | below
      · rw [extend] at reaches
        exact parent_outside_child reaches List.prefix_rfl
      · obtain ⟨child, edge, descendant⟩ := underChild node below
        rw [extend] at reaches
        have same := separate_children reaches descendant
        exact (edgeAndOff child edge).2 (linked.trans (congrArg some same))
    · exact higherOutside node above ((by rw [extend]; exact List.prefix_append _ _
        : shape.address current <+: shape.address p).trans reaches)

/-- Consistent parent and child addresses yield a duplicate-free schedule for
every pruning predicate and child-visit mode. -/
theorem traverseWithSkip_nodup {tree : TraversalTree} (shape : tree.Addressed)
    (start : Nat) (mode : ChildrenVisitMode) (skip : Nat → Bool) :
    ((tree.traverseWithSkip start mode skip).2.map (·.node)).Nodup := by
  have go (depth current : Nat) (previous : Option Nat) (isStart : Bool)
      (linked : ∀ p, previous = some p → shape.address p = shape.address current ++ [p]) :
      let path := ancestorPathAux tree depth current
      let nodes := path ++ ((initialForeignRoots.go tree mode path previous isStart).flatMap
        (tree.foreignPostorder skip tree.nodes.size)).map (·.node)
      nodes.Nodup ∧ ∀ p, previous = some p → ∀ node ∈ nodes,
        ¬ shape.address p <+: shape.address node := by
    induction depth generalizing current previous isStart with
    | zero =>
      exact path_schedule_once shape mode skip _ [] current previous isStart linked
        (by simp [initialForeignRoots.go]) (by simp [initialForeignRoots.go])
    | succ depth ih =>
      cases parent : (tree.nodeAt current).parent with
      | none =>
        simp only [ancestorPathAux, parent]
        exact path_schedule_once shape mode skip _ [] current previous isStart linked
          (by simp [initialForeignRoots.go]) (by simp [initialForeignRoots.go])
      | some up =>
        simp only [ancestorPathAux, parent]
        obtain ⟨once, outside⟩ := ih up (some current) false (fun p same => by
          cases same
          exact shape.parentAddress parent)
        exact path_schedule_once shape mode skip _ _ current previous isStart linked once
          (outside current rfl)
  simpa [traverseWithSkip, List.map_map, Function.comp_def, initialForeignRoots, ancestorPath]
    using (go tree.nodes.size start none true (by simp)).1

/-- A depth witness and consistent child back-links give traversal addresses. -/
def Addressed.ofParentDepth (tree : TraversalTree) (depth : Nat → Nat)
    (childrenOnce : ∀ parent, (tree.nodeAt parent).children.Nodup)
    (childParent : ∀ {parent child}, child ∈ (tree.nodeAt parent).children →
      (tree.nodeAt child).parent = some parent)
    (parentDepth : ∀ {parent child}, (tree.nodeAt child).parent = some parent →
      depth parent < depth child) : tree.Addressed := by
  let addressStep (child : Nat) (up : ∀ parent, depth parent < depth child → List Nat) :=
    match link : (tree.nodeAt child).parent with
    | none => [child]
    | some parent => up parent (parentDepth link) ++ [child]
  let address := (measure depth).wf.fix addressStep
  have linked {parent child : Nat} (link : (tree.nodeAt child).parent = some parent) :
      address child = address parent ++ [child] := by
    conv => lhs; unfold address; rw [WellFounded.fix_eq]
    dsimp [addressStep]
    split
    · rename_i absent
      simp [link] at absent
    · rename_i other linked
      have same : parent = other := Option.some.inj (link.symm.trans linked)
      subst other
      rfl
  exact ⟨address, childrenOnce, fun edge => linked (childParent edge), linked⟩

private theorem ancestorPathAux_stable (tree : TraversalTree) (fuel node : Nat)
    (rooted : (tree.nodeAt (ancestorPathAux tree fuel node).getLast!).parent = none) :
    ancestorPathAux tree (fuel + 1) node = ancestorPathAux tree fuel node := by
  induction fuel generalizing node with
  | zero =>
    have endOfPath : (tree.nodeAt node).parent = none := by simpa [ancestorPathAux] using rooted
    simp [ancestorPathAux, endOfPath]
  | succ fuel ih =>
    cases link : (tree.nodeAt node).parent with
    | none => simp [ancestorPathAux, link]
    | some parent =>
      have nonempty : ancestorPathAux tree fuel parent ≠ [] := by
        intro empty
        have head := ancestorPathAux_head tree fuel parent
        simp [empty] at head
      simp only [ancestorPathAux, link] at rooted ⊢
      have endOfPath :
          (node :: ancestorPathAux tree fuel parent).getLast! =
            (ancestorPathAux tree fuel parent).getLast! := by
        cases path : ancestorPathAux tree fuel parent with
        | nil => exact (nonempty path).elim
        | cons => simp
      rw [endOfPath] at rooted
      exact congrArg (node :: ·) (ih parent rooted)

/-- The bounded ancestor path gives canonical addresses when every parent
chain reaches a root within the traversal bound. -/
def Addressed.ofRooted (tree : TraversalTree)
    (childrenOnce : ∀ parent, (tree.nodeAt parent).children.Nodup)
    (childParent : ∀ {parent child}, child ∈ (tree.nodeAt parent).children →
      (tree.nodeAt child).parent = some parent)
    (rooted : ∀ node, (tree.nodeAt (tree.ancestorPath node).getLast!).parent = none) :
    tree.Addressed := by
  let address (node : Nat) := (tree.ancestorPath node).reverse
  have addressExtends {parent child : Nat} (link : (tree.nodeAt child).parent = some parent) :
      address child = address parent ++ [child] := by
    have extend : ancestorPathAux tree (tree.nodes.size + 1) child =
        child :: ancestorPathAux tree tree.nodes.size parent := by
      simp [ancestorPathAux, link]
    have stable := ancestorPathAux_stable tree tree.nodes.size child (rooted child)
    simp only [address, ancestorPath, ← stable, extend, List.reverse_cons]
  exact ⟨address, childrenOnce, fun edge => addressExtends (childParent edge), addressExtends⟩

end TraversalTree

end Tree

end Miri.TreeBorrows

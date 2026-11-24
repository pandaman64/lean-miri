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

end TraversalTree

end Tree

end Miri.TreeBorrows

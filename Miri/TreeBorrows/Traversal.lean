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

private def nodeAt (tree : TraversalTree) (index : Nat) : TraversalNode :=
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

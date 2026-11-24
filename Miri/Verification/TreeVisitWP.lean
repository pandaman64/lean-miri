import Miri.TreeBorrows.TreeState

/-!
Pointwise conditions for the normal concrete-provenance visitor. They describe
which nodes are scheduled and which events a completed access propagates.
-/
namespace Miri.Verification.TreeVisitWP

open Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree

/-- A completed execution propagates every scheduled event, in order. -/
theorem completed_events (tree : NormalTreeState) (root : Nat) (kind : AccessKind)
    (events : List TraversalEvent)
    (complete : (tree.processEvents root kind events).status = .Completed) :
    (tree.processEvents root kind events).visited = events := by
  induction events generalizing tree with
  | nil => rfl
  | cons event rest ih =>
    cases current : tree.stateAt event.node with
    | none => simp [NormalTreeState.processEvents, current] at complete
    | some old =>
      cases record : old.recordNewAccess kind event.relatedness with
      | DebugAssertion => simp [NormalTreeState.processEvents, current, record] at complete
      | Recorded recorded =>
        generalize resultEq : recorded.performAccess kind event.relatedness
          (tree.protectedNodes.contains event.node) = result
        cases update : tree.setState event.node result.resultingState with
        | none =>
          simp only [NormalTreeState.processEvents, current, record, resultEq, update] at complete
          contradiction
        | some next =>
          cases result <;>
            simp only [NormalTreeState.processEvents, current, record, resultEq, update] at complete ⊢
          all_goals first | contradiction | exact congrArg (event :: ·) (ih next complete)

/-- The trace of a completed normal access is its topology and prune schedule. -/
theorem completed_visits (tree : NormalTreeState) (start : Nat) (kind : AccessKind)
    (mode : ChildrenVisitMode) (complete : (tree.performAccess start kind mode).status = .Completed) :
    (tree.performAccess start kind mode).visited =
      (tree.topology.traverseWithSkip start mode (tree.shouldSkipForeignNode kind)).2 :=
  completed_events tree _ kind _ complete

/-- The initial facts for a permitted normal event: the location exists, the
skip assertion accepts the event, and its permission transition succeeds. -/
def EventAllowed (tree : NormalTreeState) (kind : AccessKind) (event : TraversalEvent) : Prop :=
  ∃ old recorded next transition,
    tree.stateAt event.node = some old ∧
    old.recordNewAccess kind event.relatedness = .Recorded recorded ∧
    recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) =
      .Success next transition

private theorem setState_exists (tree : NormalTreeState) (node : Nat) (old next : LocationState)
    (found : tree.stateAt node = some old) : ∃ after, tree.setState node next = some after := by
  have within : node < tree.locationStates.size := by
    by_cases within : node < tree.locationStates.size
    · exact within
    · simp [NormalTreeState.stateAt, Array.getElem?_eq_none (Nat.le_of_not_lt within)] at found
  simp [NormalTreeState.setState, within]

private theorem eventAllowed_setState_iff (tree after : NormalTreeState) (node : Nat)
    (next : LocationState) (kind : AccessKind) (event : TraversalEvent)
    (set : tree.setState node next = some after) (distinct : node ≠ event.node) :
    EventAllowed after kind event ↔ EventAllowed tree kind event := by
  unfold NormalTreeState.setState at set
  split at set
  next within =>
    injection set with replaced
    subst after
    simp [EventAllowed, NormalTreeState.stateAt, Array.getElem?_set_ne within distinct]
  next => contradiction

/-- A completed event-list head contributes one successful location update. -/
theorem completed_cons_iff (tree : NormalTreeState) (root : Nat) (kind : AccessKind)
    (event : TraversalEvent) (rest : List TraversalEvent) :
    (tree.processEvents root kind (event :: rest)).status = .Completed ↔
      ∃ old recorded next transition after,
        tree.stateAt event.node = some old ∧
        old.recordNewAccess kind event.relatedness = .Recorded recorded ∧
        recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) =
          .Success next transition ∧ tree.setState event.node next = some after ∧
        (after.processEvents root kind rest).status = .Completed := by
  simp only [NormalTreeState.processEvents]
  generalize tree.stateAt event.node = current
  cases current with
  | none => simp
  | some old =>
    simp only [Option.some.injEq, exists_and_left, exists_eq_left']
    generalize old.recordNewAccess kind event.relatedness = record
    cases record with
    | DebugAssertion => simp
    | Recorded recorded =>
      simp only [LocationState.RecordAccessResult.Recorded.injEq, exists_eq_left']
      generalize recorded.performAccess kind event.relatedness
        (tree.protectedNodes.contains event.node) = result
      cases result with
      | Success next transition =>
        cases update : tree.setState event.node next <;>
          simp [LocationState.AccessResult.resultingState, update]
      | _ =>
        simp only [LocationState.AccessResult.resultingState]
        split <;> simp

/-- If each node is scheduled at most once, completion is exactly the
conjunction of per-node conditions on the initial location. -/
theorem events_complete_iff (tree : NormalTreeState) (root : Nat) (kind : AccessKind)
    (events : List TraversalEvent) (once : (events.map (·.node)).Nodup) :
    (tree.processEvents root kind events).status = .Completed ↔
      ∀ event ∈ events, EventAllowed tree kind event := by
  induction events generalizing tree with
  | nil => simp [NormalTreeState.processEvents]
  | cons event rest ih =>
    simp only [List.map_cons, List.nodup_cons] at once
    rw [completed_cons_iff, List.forall_mem_cons]
    have separate : ∀ future ∈ rest, event.node ≠ (future : TraversalEvent).node := by
      intro future mem equal
      exact once.1 (equal ▸ List.mem_map_of_mem mem)
    constructor
    · rintro ⟨old, recorded, next, transition, after, found, recordedEq, success, set, complete⟩
      refine ⟨⟨old, recorded, next, transition, found, recordedEq, success⟩, ?_⟩
      intro future mem
      exact (eventAllowed_setState_iff tree after event.node next kind future set (separate future mem)).mp
        ((ih after once.2).mp complete future mem)
    · rintro ⟨⟨old, recorded, next, transition, found, recordedEq, success⟩, allowed⟩
      obtain ⟨after, set⟩ := setState_exists tree event.node old next found
      refine ⟨old, recorded, next, transition, after, found, recordedEq, success, set,
        (ih after once.2).mpr ?_⟩
      intro future mem
      exact (eventAllowed_setState_iff tree after event.node next kind future set (separate future mem)).mpr
        (allowed future mem)

/-- Exact initial-state completion condition for a normal access on any
schedule which visits each node at most once. -/
theorem normal_complete_iff (tree : NormalTreeState) (start : Nat) (kind : AccessKind)
    (mode : ChildrenVisitMode)
    (once : ((tree.topology.traverseWithSkip start mode
      (tree.shouldSkipForeignNode kind)).2.map (·.node)).Nodup) :
    (tree.performAccess start kind mode).status = .Completed ↔
      ∀ event ∈ (tree.topology.traverseWithSkip start mode (tree.shouldSkipForeignNode kind)).2,
        EventAllowed tree kind event :=
  events_complete_iff tree _ kind _ once

/-- A resolved concrete tag's scheduled relationship to a second resolved tag.
The location is the snapshot before the access. -/
def TagVisit (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (source target : BorTag) (kind : AccessKind) (mode : ChildrenVisitMode)
    (relationship : AccessRelatedness) : Prop :=
  match tree.indexOfTag source, tree.indexOfTag target with
  | some start, some node =>
    let view := tree.normalView location tags
    (⟨node.toNat, relationship⟩ : TraversalEvent) ∈
      (view.topology.traverseWithSkip start.toNat mode (view.shouldSkipForeignNode kind)).2
  | _, _ => False

/-- With both tag names resolved, the local condition is ancestry, independent
of permissions, protectors, access kind and pruning. -/
theorem tag_local_iff (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (source target : BorTag) (kind : AccessKind) (mode : ChildrenVisitMode) (start node : UniIndex)
    (sourceAt : tree.indexOfTag source = some start) (targetAt : tree.indexOfTag target = some node) :
    TagVisit tree location tags source target kind mode .LocalAccess ↔
      node.toNat ∈ (tree.normalView location tags).topology.ancestorPath start.toNat := by
  simp [TagVisit, sourceAt, targetAt]

/-- Read-induced permission and SIFA updates leave ancestry-based local
selection unchanged for a later access in the same borrow tree. -/
theorem tag_local_snapshot_iff (tree : BorrowTree) (before after : LocationTree)
    (readTags writeTags : ProtectedTags) (source target : BorTag)
    (readMode writeMode : ChildrenVisitMode) :
    TagVisit tree after writeTags source target .Write writeMode .LocalAccess ↔
      TagVisit tree before readTags source target .Read readMode .LocalAccess := by
  unfold TagVisit
  split <;> simp only [TraversalTree.local_visit_iff] <;> rfl

/-- With both tag names resolved, foreign selection follows an eligible
branch and requires every node on the branch-to-target path to permit descent. -/
theorem tag_foreign_iff (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (source target : BorTag) (kind : AccessKind) (mode : ChildrenVisitMode) (start node : UniIndex)
    (sourceAt : tree.indexOfTag source = some start) (targetAt : tree.indexOfTag target = some node) :
    TagVisit tree location tags source target kind mode .ForeignAccess ↔
      let view := tree.normalView location tags
      ∃ branch, view.topology.ForeignBranch mode (view.topology.ancestorPath start.toNat) none true branch ∧
        view.topology.UnprunedPath (view.shouldSkipForeignNode kind) view.topology.nodes.size branch node.toNat := by
  simp [TagVisit, sourceAt, targetAt]

/-- Writing back states and updating the exposed cache retains the normal
visitor's result in the concrete location access. -/
theorem normal_access_result (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (start : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt location start kind tags mode).access =
      (tree.normalView location tags).performAccess start.toNat kind mode := by
  rfl

/-- The scheduled relationship is observed in the successful normal component's
trace. This does not require either tag to have been exposed. -/
theorem tag_visit_iff_completed_normal (tree : BorrowTree) (location : LocationTree)
    (tags : ProtectedTags) (source target : BorTag) (kind : AccessKind) (mode : ChildrenVisitMode)
    (relation : AccessRelatedness) (start node : UniIndex)
    (sourceAt : tree.indexOfTag source = some start) (targetAt : tree.indexOfTag target = some node)
    (complete : (tree.performNormalAccessAt location start kind tags mode).access.status = .Completed) :
    TagVisit tree location tags source target kind mode relation ↔
      (⟨node.toNat, relation⟩ : TraversalEvent) ∈
        (tree.performNormalAccessAt location start kind tags mode).access.visited := by
  rw [normal_access_result] at complete ⊢
  simp only [TagVisit, sourceAt, targetAt, completed_visits _ _ _ _ complete]

end Miri.Verification.TreeVisitWP

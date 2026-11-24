import Miri.Verification.TreeVisitWP

namespace Miri.Verification.TreeVisitWP

open Miri.TreeBorrows Miri.TreeBorrows.Tree

private def eventStateAt (tree : NormalTreeState) (kind : AccessKind)
    (node : Nat) (event : TraversalEvent) : Option LocationState := do
  let old ← tree.stateAt node
  match old.recordNewAccess kind event.relatedness with
  | .DebugAssertion => none
  | .Recorded recorded =>
    match recorded.performAccess kind event.relatedness (tree.protectedNodes.contains node) with
    | .Success next _ => some next
    | _ => none

/-- The state of a node after a successful schedule with no repeated nodes
can be computed directly from its initial state and its one scheduled event. -/
def stateAfterEventsAt (tree : NormalTreeState) (kind : AccessKind)
    (events : List TraversalEvent) (node : Nat) : Option LocationState :=
  match events.find? (fun event => event.node == node) with
  | none => tree.stateAt node
  | some event => eventStateAt tree kind node event

private theorem setState_facts (tree after : NormalTreeState) (node : Nat)
    (next : LocationState) (set : tree.setState node next = some after) :
    after.topology = tree.topology ∧ after.protectedNodes = tree.protectedNodes ∧
      after.stateAt node = some next ∧
      ∀ other, node ≠ other → after.stateAt other = tree.stateAt other := by
  unfold NormalTreeState.setState at set
  split at set
  next within =>
    injection set with replaced
    subst after
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp [NormalTreeState.stateAt]
    · intro other distinct
      simp [NormalTreeState.stateAt, Array.getElem?_set_ne within distinct]
  next => contradiction

/-- A completed schedule leaves the protector list unchanged and updates each
location according to the event for its node, if present. -/
theorem completed_events_states (tree : NormalTreeState) (root : Nat) (kind : AccessKind)
    (events : List TraversalEvent) (once : (events.map (·.node)).Nodup)
    (complete : (tree.processEvents root kind events).status = .Completed) :
    let after := (tree.processEvents root kind events).tree
    after.topology = tree.topology ∧ after.protectedNodes = tree.protectedNodes ∧
      ∀ node, after.stateAt node = stateAfterEventsAt tree kind events node := by
  induction events generalizing tree with
  | nil => exact ⟨rfl, rfl, fun _ => rfl⟩
  | cons event rest ih =>
    simp only [List.map_cons, List.nodup_cons] at once
    obtain ⟨old, recorded, next, transition, intermediate, found, record, success, set, finished⟩ :=
      (completed_cons_iff tree root kind event rest).mp complete
    obtain ⟨topology, sameProtectors, updated, unchanged⟩ := setState_facts tree intermediate event.node next set
    obtain ⟨finalTopology, finalProtected, finalState⟩ := ih intermediate once.2 finished
    simp only [NormalTreeState.processEvents, found, record, success,
      LocationState.AccessResult.resultingState, set]
    refine ⟨finalTopology.trans topology, finalProtected.trans sameProtectors, fun node => ?_⟩
    rw [finalState]
    by_cases same : event.node = node
    · have omitted : rest.find? (fun event => event.node == node) = none := by
        apply List.find?_eq_none.mpr
        intro other member equal
        exact once.1 (show event.node ∈ rest.map (·.node) from
          List.mem_map.mpr ⟨other, member, (beq_iff_eq.mp equal).trans same.symm⟩)
      subst node
      simp only [stateAfterEventsAt, omitted, List.find?_cons, beq_self_eq_true, eventStateAt,
        updated, found, bind, Option.bind, record, success]
    · have distinct : (event.node == node) = false := by simp [same]
      simp only [stateAfterEventsAt, List.find?_cons, distinct]
      cases rest.find? (fun event => event.node == node) <;>
        simp [eventStateAt, unchanged node same, sameProtectors]

/-- Per-node conditions on the initial location for read and write schedules
that each visit a node at most once. -/
def EventsReadWriteAllowed (tree : NormalTreeState) (reads writes : List TraversalEvent) : Prop :=
  (∀ event ∈ reads, EventAllowed tree .Read event) ∧
    ∀ event ∈ writes, ∃ old recorded next transition,
      stateAfterEventsAt tree .Read reads event.node = some old ∧
      old.recordNewAccess .Write event.relatedness = .Recorded recorded ∧
      recorded.performAccess .Write event.relatedness (tree.protectedNodes.contains event.node) =
        .Success next transition

/-- Exact success condition for two fixed normal schedules. The write check
uses a node's initial state or the result of its one read transition. Each
scheduled event also checks the interpreter's SIFA record assertion. -/
theorem events_read_write_pre_iff (tree : NormalTreeState) (readRoot writeRoot : Nat)
    (reads writes : List TraversalEvent) (readOnce : (reads.map (·.node)).Nodup)
    (writeOnce : (writes.map (·.node)).Nodup) :
    tree.eventsPre readRoot .Read (fun read => read.status = .Completed ∧
      read.tree.eventsPre writeRoot .Write (fun write => write.status = .Completed) writes) reads ↔
      EventsReadWriteAllowed tree reads writes := by
  rw [NormalTreeState.eventsPre_iff]
  constructor
  · rintro ⟨completed, writePre⟩
    obtain ⟨_, sameProtectors, updated⟩ := completed_events_states tree readRoot .Read reads readOnce completed
    rw [NormalTreeState.eventsPre_iff, events_complete_iff _ _ _ _ writeOnce] at writePre
    exact ⟨(events_complete_iff tree readRoot .Read reads readOnce).mp completed,
      fun event mem => by simpa only [EventAllowed, sameProtectors, updated] using writePre event mem⟩
  · rintro ⟨readPre, writePre⟩
    have completed := (events_complete_iff tree readRoot .Read reads readOnce).mpr readPre
    obtain ⟨_, sameProtectors, updated⟩ := completed_events_states tree readRoot .Read reads readOnce completed
    refine ⟨completed, ?_⟩
    rw [NormalTreeState.eventsPre_iff, events_complete_iff _ _ _ _ writeOnce]
    intro event mem
    simpa only [EventAllowed, sameProtectors, updated] using writePre event mem

/-- Reconstruct the write schedule from the initial tree and the selected
read events, including how successful reads change foreign pruning. -/
def writeScheduleAfterRead (tree : NormalTreeState) (reads : List TraversalEvent)
    (writer : Nat) (mode : ChildrenVisitMode) : Nat × List TraversalEvent :=
  tree.topology.traverseWithSkip writer mode fun node =>
    if node < tree.topology.nodes.size then
      match stateAfterEventsAt tree .Read reads node with
      | none => false
      | some state => state.skipIfKnownNoop .Write .ForeignAccess == .SkipSelfAndChildren
    else false

/-- The normal tree visitor's read-then-write WP is checked on the initial
location. The writer's foreign schedule accounts for the read-induced change
in SIFA without needing the intermediate tree. -/
theorem normal_read_write_pre_iff (tree : NormalTreeState) (reader writer : Nat)
    (readMode writeMode : ChildrenVisitMode)
    (readOnce : ((tree.topology.traverseWithSkip reader readMode
      (tree.shouldSkipForeignNode .Read)).2.map (·.node)).Nodup)
    (writeOnce : ((writeScheduleAfterRead tree (tree.topology.traverseWithSkip reader readMode
      (tree.shouldSkipForeignNode .Read)).2 writer writeMode).2.map (·.node)).Nodup) :
    tree.accessPre reader .Read readMode (fun read => read.status = .Completed ∧
      read.tree.accessPre writer .Write writeMode (fun write => write.status = .Completed)) ↔
    EventsReadWriteAllowed tree (tree.topology.traverseWithSkip reader readMode
      (tree.shouldSkipForeignNode .Read)).2
      (writeScheduleAfterRead tree (tree.topology.traverseWithSkip reader readMode
        (tree.shouldSkipForeignNode .Read)).2 writer writeMode).2 := by
  let reads := tree.topology.traverseWithSkip reader readMode (tree.shouldSkipForeignNode .Read)
  let writes := writeScheduleAfterRead tree reads.2 writer writeMode
  have writeSchedule
      (complete : (tree.processEvents reads.1 .Read reads.2).status = .Completed) :
      let after := (tree.processEvents reads.1 .Read reads.2).tree
      after.topology.traverseWithSkip writer writeMode (after.shouldSkipForeignNode .Write) = writes := by
    obtain ⟨topology, _, updated⟩ := completed_events_states tree reads.1 .Read reads.2 readOnce complete
    dsimp only
    unfold writes writeScheduleAfterRead
    congr 1
    funext node
    simp only [NormalTreeState.shouldSkipForeignNode, topology, updated]
    rfl
  rw [← events_read_write_pre_iff tree reads.1 writes.1 reads.2 writes.2 readOnce writeOnce]
  simp only [NormalTreeState.accessPre_iff, NormalTreeState.eventsPre_iff]
  change ((_ : Prop) ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨complete, write⟩ <;> refine ⟨complete, ?_⟩
  · unfold NormalTreeState.performAccess at write
    rw [writeSchedule complete] at write
    exact write
  · unfold NormalTreeState.performAccess
    rw [writeSchedule complete]
    exact write

end Miri.Verification.TreeVisitWP

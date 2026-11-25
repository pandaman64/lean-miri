import Miri.Verification.TreeNormalCommitWP
import Miri.Verification.TreeRangeAccess
import Miri.Verification.TreeTopologyWP

namespace Miri.Verification.TreeNormalRangeWP

open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Std.WP
open Miri.Verification.TreeVisitWP Miri.Verification.TreeRangeAccess

private theorem completed_event_in_bounds (view : NormalTreeState) (root : Nat)
    (kind : AccessKind) (events : List TraversalEvent)
    (complete : (view.processEvents root kind events).status = .Completed)
    (event : TraversalEvent) (visited : event ∈ events) :
    event.node < view.locationStates.size := by
  induction events generalizing view with
  | nil => simp at visited
  | cons first rest ih =>
    obtain ⟨_, _, _, _, after, _, _, _, updated, restComplete⟩ :=
      (completed_cons_iff view root kind first rest).mp complete
    have updateFacts : first.node < view.locationStates.size ∧
        after.locationStates.size = view.locationStates.size := by
      unfold NormalTreeState.setState at updated
      split at updated
      next bounded =>
        cases updated
        exact ⟨bounded, Array.size_set bounded⟩
      next => contradiction
    rcases List.mem_cons.mp visited with rfl | tail
    · exact updateFacts.1
    · exact updateFacts.2 ▸ ih after restComplete tail

private theorem completed_normal_visit_in_bounds (view : NormalTreeState) (source : Nat)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (complete : (view.performAccess source kind mode).status = .Completed)
    (event : TraversalEvent) (visited : event ∈ (view.performAccess source kind mode).visited) :
    event.node < view.locationStates.size := by
  rw [completed_visits _ _ _ _ complete] at visited
  exact completed_event_in_bounds view _ kind _ complete event visited

/-- The full-range concrete rule checks only initial structure and normal
permission events when every position in the node array is populated and
unexposed. In this domain a completed normal visitor needs no exposed-cache
transition and its retained permissions project back to the normal state. -/
theorem wp_uniform_read_write_iff (tree : BorrowTree) (location : LocationTree)
    (size : Size) (positive : size.bytes ≠ 0)
    (uniform : tree.locations = DedupRangeMap.new size location)
    (reader writer : BorTag) (readIndex writeIndex root : UniIndex)
    (readerAt : tree.indexOfTag reader = some readIndex)
    (writerAt : tree.indexOfTag writer = some writeIndex)
    (roots : tree.roots = #[root]) (tags : ProtectedTags)
    (readerRoot : UniIndex.ofNat?
      (((tree.normalView location tags).topology.ancestorPath readIndex.toNat).getLast!) = some root)
    (writerRoot : UniIndex.ofNat?
      (((tree.normalView location tags).topology.ancestorPath writeIndex.toNat).getLast!) = some root)
    (bounded : tree.nodes.data.size ≤ 2 ^ 32)
    (unexposed : ∀ position, position < tree.nodes.data.size →
      ∃ index node, UniIndex.ofNat? position = some index ∧ tree.nodeAt index = some node ∧
        node.isExposed = false)
    (readOnce : let view := tree.normalView location tags
      ((view.topology.traverseWithSkip readIndex.toNat .VisitChildrenOfAccessed
        (view.shouldSkipForeignNode .Read)).2.map (·.node)).Nodup)
    (writeOnce : let view := tree.normalView location tags
      let reads := (view.topology.traverseWithSkip readIndex.toNat .VisitChildrenOfAccessed
        (view.shouldSkipForeignNode .Read)).2
      ((writeScheduleAfterRead view reads writeIndex.toNat
        .VisitChildrenOfAccessed).2.map (·.node)).Nodup) :
    wp ((do
        let reads ← TreeBorrowsWP.access (.concrete reader) Size.ZERO size .Read tags .VisitChildrenOfAccessed
        let writes ← TreeBorrowsWP.access (.concrete writer) Size.ZERO size .Write tags .VisitChildrenOfAccessed
        pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
          (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace))
      (fun _ _ => True) (fun _ _ => False) tree ↔
    let view := tree.normalView location tags
    let reads := (view.topology.traverseWithSkip readIndex.toNat .VisitChildrenOfAccessed
      (view.shouldSkipForeignNode .Read)).2
    EventsReadWriteAllowed view reads
      (writeScheduleAfterRead view reads writeIndex.toNat .VisitChildrenOfAccessed).2 := by
  have commitNormal (initial : LocationTree) (source : UniIndex) (kind : AccessKind)
      (complete : (tree.performNormalAccessAt initial source kind tags .VisitChildrenOfAccessed).access.status =
        .Completed) :=
    TreeNormalCommitWP.normalView_after_access tree initial source kind tags .VisitChildrenOfAccessed
      bounded (by
        intro event visited
        have viewResult := normal_access_result tree initial tags source kind .VisitChildrenOfAccessed
        rw [viewResult] at complete visited
        have bound := completed_normal_visit_in_bounds _ _ _ _ complete event visited
        rw [TreeNormalCommitWP.normalView_size] at bound
        exact unexposed event.node bound)
  exact wp_uniform_read_write_normal_iff tree location size positive uniform reader writer readIndex
    writeIndex root readerAt writerAt roots tags readerRoot writerRoot
    (fun complete => (commitNormal location readIndex .Read complete).1)
    (fun complete => (commitNormal _ writeIndex .Write complete).1)
    (fun complete => (commitNormal location readIndex .Read complete).2) readOnce writeOnce

/-- In an addressed topology, the normal schedules need no separate
no-duplicate-visit proofs. -/
theorem wp_uniform_read_write_of_addressed_iff (tree : BorrowTree) (location : LocationTree)
    (size : Size) (positive : size.bytes ≠ 0)
    (uniform : tree.locations = DedupRangeMap.new size location)
    (reader writer : BorTag) (readIndex writeIndex root : UniIndex)
    (readerAt : tree.indexOfTag reader = some readIndex)
    (writerAt : tree.indexOfTag writer = some writeIndex)
    (roots : tree.roots = #[root]) (tags : ProtectedTags)
    (readerRoot : UniIndex.ofNat?
      (((tree.normalView location tags).topology.ancestorPath readIndex.toNat).getLast!) = some root)
    (writerRoot : UniIndex.ofNat?
      (((tree.normalView location tags).topology.ancestorPath writeIndex.toNat).getLast!) = some root)
    (bounded : tree.nodes.data.size ≤ 2 ^ 32)
    (unexposed : ∀ position, position < tree.nodes.data.size →
      ∃ index node, UniIndex.ofNat? position = some index ∧ tree.nodeAt index = some node ∧
        node.isExposed = false)
    (shape : (tree.normalView location tags).topology.Addressed) :
    wp ((do
        let reads ← TreeBorrowsWP.access (.concrete reader) Size.ZERO size .Read tags .VisitChildrenOfAccessed
        let writes ← TreeBorrowsWP.access (.concrete writer) Size.ZERO size .Write tags .VisitChildrenOfAccessed
        pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
          (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace))
      (fun _ _ => True) (fun _ _ => False) tree ↔
    let view := tree.normalView location tags
    let reads := (view.topology.traverseWithSkip readIndex.toNat .VisitChildrenOfAccessed
      (view.shouldSkipForeignNode .Read)).2
    EventsReadWriteAllowed view reads
      (writeScheduleAfterRead view reads writeIndex.toNat .VisitChildrenOfAccessed).2 := by
  exact wp_uniform_read_write_iff tree location size positive uniform reader writer readIndex writeIndex
    root readerAt writerAt roots tags readerRoot writerRoot bounded unexposed
    (TraversalTree.traverseWithSkip_nodup shape readIndex.toNat .VisitChildrenOfAccessed _)
    (TraversalTree.traverseWithSkip_nodup shape writeIndex.toNat .VisitChildrenOfAccessed _)

end Miri.Verification.TreeNormalRangeWP

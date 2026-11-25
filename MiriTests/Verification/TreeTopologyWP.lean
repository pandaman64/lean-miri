import Miri.Verification.TreeTopologyWP

namespace MiriTests.Verification.TreeTopologyWP

open Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification.TreeVisitWP

/-- One sibling has an index smaller than its parent, as can happen when a
tree reuses a vacant node index. -/
private def topology : TraversalTree :=
  ⟨#[⟨some 2, []⟩, ⟨some 2, []⟩, ⟨none, [0, 1]⟩]⟩

private def shape : topology.Addressed := by
  apply TraversalTree.Addressed.ofRooted topology
  · intro parent
    rcases parent with _ | _ | _ | parent <;> simp [topology, TraversalTree.nodeAt]
  · intro parent child edge
    rcases parent with _ | _ | _ | parent
    all_goals simp [topology, TraversalTree.nodeAt] at edge
    rcases edge with rfl | rfl <;> rfl
  · intro node
    rcases node with _ | _ | _ | node <;> cbv

private def tree : NormalTreeState := {
  topology
  defaultStates := #[⟨.Cell, false, .Write⟩, ⟨.ReservedFrz false, false, .Read⟩, ⟨.Unique, true, .None⟩]
  protectedNodes := []
  locationStates := #[none, none, none]
}

/-- The read invalidates a foreign pruning cache entry. The newly scheduled
write event still inherits uniqueness from the original topology. -/
example :
    let mode := ChildrenVisitMode.VisitChildrenOfAccessed
    let reads := (tree.topology.traverseWithSkip 0 mode (tree.shouldSkipForeignNode .Read)).2
    (writeScheduleAfterRead tree reads 1 mode).2 =
      [⟨1, .LocalAccess⟩, ⟨2, .LocalAccess⟩, ⟨0, .ForeignAccess⟩] ∧
    tree.accessPre 0 .Read mode (fun read => read.status = .Completed ∧
      read.tree.accessPre 1 .Write mode (fun write => write.status = .Completed)) := by
  constructor
  · cbv
  · apply (normal_read_write_pre_of_addressed_iff tree shape
      0 1 .VisitChildrenOfAccessed .VisitChildrenOfAccessed).mpr
    cbv
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals exact ⟨_, _, _, _, rfl, rfl, rfl⟩

private def protectedReader : NormalTreeState := {
  tree with
  defaultStates := #[⟨.Frozen, false, .Read⟩, ⟨.ReservedFrz false, false, .Read⟩,
    ⟨.Unique, true, .None⟩]
  protectedNodes := [0]
}

/-- A foreign write to the reader's branch is rejected once the preceding
read has marked its protected frozen location accessed. -/
example :
    let mode := ChildrenVisitMode.VisitChildrenOfAccessed
    (protectedReader.performAccess 0 .Read mode).status = .Completed ∧
    ¬ protectedReader.accessPre 0 .Read mode (fun read => read.status = .Completed ∧
      read.tree.accessPre 1 .Write mode (fun write => write.status = .Completed)) := by
  constructor
  · cbv
  · rw [normal_read_write_pre_of_addressed_iff protectedReader shape]
    intro allowed
    obtain ⟨old, recorded, next, transition, found, record, success⟩ :=
      allowed.2 ⟨0, .ForeignAccess⟩ (by cbv; exact .tail _ (.tail _ (.head _)))
    cbv at found
    cases found
    cbv at record
    cases record
    cbv at success
    cases success

end MiriTests.Verification.TreeTopologyWP

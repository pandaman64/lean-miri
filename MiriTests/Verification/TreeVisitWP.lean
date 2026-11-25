import Miri.Verification.TreeVisitWP
import Miri.Verification.TreeNormalRangeWP

namespace MiriTests.Verification.TreeVisitWP

open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification.TreeVisitWP Miri.Verification.TreeRangeAccess Std.WP

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-- Distinct scheduled nodes generate independent permission obligations on
the original location, even when their local/foreign relationships differ. -/
example (tree : NormalTreeState) (root first second : Nat) (kind : AccessKind)
    (distinct : first ≠ second) :
    (tree.processEvents root kind [⟨first, .LocalAccess⟩, ⟨second, .ForeignAccess⟩]).status =
      .Completed ↔ EventAllowed tree kind ⟨first, .LocalAccess⟩ ∧
        EventAllowed tree kind ⟨second, .ForeignAccess⟩ := by
  rw [events_complete_iff _ _ _ _ (by simp [distinct])]
  simp

private def fork : TraversalTree := ⟨#[⟨none, [1, 2]⟩, ⟨some 0, []⟩,
  ⟨some 0, [3]⟩, ⟨some 2, []⟩]⟩

/-- When the access is through 1, 3 is visited as foreign exactly when both
its own pruning check and the branch's check permit the visit. -/
example (skip : Nat → Bool) :
    (⟨3, .ForeignAccess⟩ : TraversalEvent) ∈
      (fork.traverseWithSkip 1 .SkipChildrenOfAccessed skip).2 ↔
    skip 2 = false ∧ skip 3 = false := by
  have branch : fork.ForeignBranch .SkipChildrenOfAccessed (fork.ancestorPath 1) none true 2 := by
    have path : fork.ancestorPath 1 = [1, 0] := by cbv
    rw [path]
    exact .above (.here (by decide) (by decide +kernel) (by decide))
  rw [TraversalTree.foreign_visit_iff]
  constructor
  · rintro ⟨root, chosen, reaches⟩
    have path : fork.ancestorPath 1 = [1, 0] := by cbv
    rw [path] at chosen
    have rootIs : root = 2 := by
      cases chosen with
      | here enter => contradiction
      | above higher =>
        cases higher with
        | here _ child offPath =>
          have child' : root ∈ [1, 2] := child
          simp at child'
          rcases child' with same | answer
          · subst root
            contradiction
          · exact answer
        | above impossible => cases impossible
    subst root
    cases reaches with
    | child enter edge reaches =>
      have single : _ ∈ [3] := edge
      simp at single
      subst_vars
      cases reaches with
      | here finish => exact ⟨enter, finish⟩
      | child _ empty => contradiction
  · rintro ⟨enter, finish⟩
    exact ⟨2, branch, .child enter (by decide +kernel) (.here finish)⟩

private def p : BorTag := ⟨2, by decide⟩
private def q : BorTag := ⟨3, by decide⟩
private def bytes := Size.ofBytes 1
private def permissions := DedupRangeMap.new bytes (⟨.ReservedFrz false, false, .None⟩ : LocationState)
private def protectors := (({} : ProtectedTags).insert p .StrongProtector).insert q .StrongProtector
private def parent := (BorrowTree.new BorTag.one bytes).newChild Size.ZERO (.concrete BorTag.one)
  p permissions (.ReservedFrz false) true
private def child := parent.tree.newChild Size.ZERO (.concrete p) q permissions (.ReservedFrz false) true
private def initial := (child.tree.locations.entries[0]?.map (·.data)).getD default
private def read := child.tree.performNormalAccessAt initial ⟨1⟩ .Read protectors .VisitChildrenOfAccessed

/-- The actual normal read on the parent visits its descendant as foreign.
A later write through the descendant visits the original source as local. -/
example :
    (⟨2, .ForeignAccess⟩ : TraversalEvent) ∈ read.access.visited ∧
      TagVisit child.tree read.location protectors q p .Write .VisitChildrenOfAccessed .LocalAccess := by
  have pAt : child.tree.indexOfTag p = some ⟨1⟩ := by cbv
  have qAt : child.tree.indexOfTag q = some ⟨2⟩ := by cbv
  constructor
  · have complete : read.access.status = .Completed := by cbv
    apply (tag_visit_iff_completed_normal child.tree initial protectors p q .Read .VisitChildrenOfAccessed
      .ForeignAccess ⟨1⟩ ⟨2⟩ pAt qAt complete).mp
    apply (tag_foreign_iff child.tree initial protectors p q .Read .VisitChildrenOfAccessed
      ⟨1⟩ ⟨2⟩ pAt qAt).mpr
    have path : (child.tree.normalView initial protectors).topology.ancestorPath 1 = [1, 0] := by cbv
    dsimp only
    rw [show (⟨1⟩ : UniIndex).toNat = 1 by rfl, path]
    refine ⟨2, .here (by decide) ?_ (by decide), ?_⟩
    · cbv
      exact .head _
    · have size : (child.tree.normalView initial protectors).topology.nodes.size = 3 := by cbv
      rw [size, show (⟨2⟩ : UniIndex).toNat = 2 by rfl]
      exact .here (by cbv)
  · apply (tag_local_snapshot_iff child.tree initial read.location protectors protectors q p
      .VisitChildrenOfAccessed .VisitChildrenOfAccessed).mpr
    apply (tag_local_iff child.tree initial protectors q p .Read .VisitChildrenOfAccessed
      ⟨2⟩ ⟨1⟩ qAt pAt).mpr
    cbv
    exact .tail _ (.head _)

private def rangeMode := ChildrenVisitMode.VisitChildrenOfAccessed

/-- An ancestor read makes its protected descendant conflicted. The
descendant's subsequent local write is permitted only without its protector
during the read. The write alone starts with an unconflicted permission. -/
example (protectReadOfQ : Bool) :
    let readTags := if protectReadOfQ then protectors else protectors.remove q
    wp ((do
      let reads ← Miri.Verification.TreeBorrowsWP.access (.concrete p) Size.ZERO bytes
        .Read readTags rangeMode
      let writes ← Miri.Verification.TreeBorrowsWP.access (.concrete q) Size.ZERO bytes
        .Write protectors rangeMode
      pure (reads, writes)) : EStateM
        (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult)
        BorrowTree (Array BorrowTree.BorrowTreeLocationResult × Array BorrowTree.BorrowTreeLocationResult))
      (fun (reads, writes) _ => reads.size = 1 ∧ writes.size = 1) (fun _ _ => False) child.tree ↔
    protectReadOfQ = false := by
  dsimp only
  miri_tree_range_wp
  cases protectReadOfQ <;> cbv <;> rfl

private def readPrepared := child.tree.locations.iterMut Size.ZERO bytes
private def qAfterRead : LocationState := ⟨.ReservedFrz true, false, .Read⟩
private def retainedRead : BorrowTree.TreeLocationAccessAtResult :=
  let events : List TraversalEvent := [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩, ⟨2, .ForeignAccess⟩]
  let trace := (child.tree.normalView initial protectors).processEvents 0 .Read events
  let perms := (initial.perms.insert ⟨1⟩ ⟨.ReservedFrz false, true, .None⟩).insert ⟨2⟩ qAfterRead
  ⟨{ initial with perms }, some trace, none⟩

/-- The pointwise successor obtains q's conflicted permission directly from
the read's retained location. -/
example :
    SnapshotAuthorized child.tree readPrepared (some ⟨1⟩)
      .Read protectors rangeMode 0 retainedRead ∧
    let after := snapshotSuccessor child.tree readPrepared
      (fun _ => retainedRead)
    (after.1.locations.entries[0]?.map (·.data)).bind (fun location => location.perms.get ⟨2⟩) =
      some qAfterRead := by
  constructor
  · refine ⟨0, _, by cbv, by cbv, by cbv, ?_⟩
    cbv
  · dsimp only
    rw [snapshotSuccessor_locationAt]
    cbv

/-- The fused rule rejects the write by inspecting q's initial read event
and its resulting conflicted permission. -/
example :
    ¬ wp ((do
      let reads ← Miri.Verification.TreeBorrowsWP.access (.concrete p) Size.ZERO bytes
        .Read protectors rangeMode
      let writes ← Miri.Verification.TreeBorrowsWP.access (.concrete q) Size.ZERO bytes
        .Write protectors rangeMode
      pure (reads, writes)) : EStateM
        (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult)
        BorrowTree (Array BorrowTree.BorrowTreeLocationResult × Array BorrowTree.BorrowTreeLocationResult))
      (fun _ _ => True) (fun _ _ => False) child.tree := by
  unfold rangeMode
  have unexposed (position : Nat) (inside : position < child.tree.nodes.data.size) :
      ∃ index node, UniIndex.ofNat? position = some index ∧ child.tree.nodeAt index = some node ∧
        node.isExposed = false := by
    have nodeCount : child.tree.nodes.data.size = 3 := by cbv
    rw [nodeCount] at inside
    have cursor : position = 0 ∨ position = 1 ∨ position = 2 := by omega
    rcases cursor with rfl | rfl | rfl
    · exact ⟨⟨0⟩, _, by cbv, by cbv, by cbv⟩
    · exact ⟨⟨1⟩, _, by cbv, by cbv, by cbv⟩
    · exact ⟨⟨2⟩, _, by cbv, by cbv, by cbv⟩
  rw [Miri.Verification.TreeNormalRangeWP.wp_uniform_read_write_iff child.tree initial bytes
    (by cbv) (by cbv) p q ⟨1⟩ ⟨2⟩ ⟨0⟩ (by cbv) (by cbv) (by cbv) protectors
    (by cbv) (by cbv) (by cbv <;> decide) unexposed (by cbv <;> decide) (by cbv <;> decide)]
  let view := child.tree.normalView initial protectors
  let reads := (view.topology.traverseWithSkip 1 rangeMode (view.shouldSkipForeignNode .Read)).2
  let writes := (writeScheduleAfterRead view reads 2 rangeMode).2
  intro obligations
  have qWritten : (⟨2, .LocalAccess⟩ : TraversalEvent) ∈ writes := by
    dsimp only [writes, reads, view]
    cbv
    exact .head _
  obtain ⟨old, recorded, next, transition, found, record, allowed⟩ :=
    obligations.2 ⟨2, .LocalAccess⟩ qWritten
  have readEffect : stateAfterEventsAt view .Read reads 2 = some qAfterRead := by
    dsimp only [reads, view]
    cbv
  have oldEq : old = qAfterRead := Option.some.inj (found.symm.trans readEffect)
  subst old
  have qRecord : qAfterRead.recordNewAccess .Write .LocalAccess =
      .Recorded { qAfterRead with idempotentForeignAccess := .None } := by cbv
  have recordedEq : recorded = { qAfterRead with idempotentForeignAccess := .None } :=
    LocationState.RecordAccessResult.Recorded.inj (record.symm.trans qRecord)
  subst recorded
  cbv at allowed
  cases allowed

end MiriTests.Verification.TreeVisitWP

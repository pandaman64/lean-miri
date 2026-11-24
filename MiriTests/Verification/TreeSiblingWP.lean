import Miri.Verification.TreeBorrowsWP
import Miri.Verification.TreeReadWriteWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeSiblingWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.Verification.TreeBorrowsWP Std.WP

namespace SiblingAccess

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def reader : BorTag := ⟨2, by decide⟩
def writer : BorTag := ⟨3, by decide⟩
def size : Size := Size.ofBytes 1

def protectors (readerHeld writerHeld : Bool) : ProtectedTags :=
  let tags : ProtectedTags := if readerHeld then
    ({} : ProtectedTags).insert reader .StrongProtector
  else {}
  if writerHeld then tags.insert writer .StrongProtector else tags

private def addReader (readerHeld : Bool) : BorrowTree.ChildInsertResult :=
  (BorrowTree.new BorTag.one size).newChild Size.ZERO (.concrete BorTag.one) reader
    (DedupRangeMap.new size ⟨.Frozen, false, .Read⟩) .Frozen readerHeld

private def addWriter (readerHeld writerHeld : Bool) : BorrowTree.ChildInsertResult :=
  let sifa : IdempotentForeignAccess := if writerHeld then .None else .Read
  (addReader readerHeld).tree.newChild Size.ZERO (.concrete BorTag.one) writer
    (DedupRangeMap.new size ⟨.ReservedFrz false, false, sifa⟩) (.ReservedFrz false) writerHeld

/-- One byte with an unaccessed frozen reader and unaccessed reserved writer
on separate branches of the same allocation root. -/
def initialTree (readerHeld writerHeld : Bool) : BorrowTree :=
  (addWriter readerHeld writerHeld).tree

private theorem inserted (readerHeld writerHeld : Bool) :
    (addReader readerHeld).outcome = .ok () ∧ (addWriter readerHeld writerHeld).outcome = .ok () := by
  cases readerHeld <;> cases writerHeld <;> cbv

/-- Reading through the frozen tag makes its location accessed. A subsequent
write through the sibling requires that reader to be unprotected. It also
requires an unprotected writer, since the first access conflicts with a
protected reservation on the writer's branch. -/
theorem readThenWrite (readerHeld writerHeld : Bool) :
    accessPre (initialTree readerHeld writerHeld) (.concrete reader) Size.ZERO size .Read
        (protectors readerHeld writerHeld) .VisitChildrenOfAccessed
        (fun afterRead _ => accessPre afterRead (.concrete writer) Size.ZERO size .Write
          (protectors readerHeld writerHeld) .VisitChildrenOfAccessed
          (fun _ _ => True) (fun _ _ _ => False))
        (fun _ _ _ => False) ↔
      readerHeld = false ∧ writerHeld = false := by
  simp only [accessPre_iff]
  cases readerHeld <;> cases writerHeld <;> cbv <;> decide

end SiblingAccess

set_option experimental.vcgen true

private theorem writeWP (tags : ProtectedTags) (tree : BorrowTree) :
    wp (access (.concrete SiblingAccess.writer) Size.ZERO SiblingAccess.size .Write
        tags .VisitChildrenOfAccessed) (fun _ _ => True) (fun _ _ => False) tree ↔
      accessPre tree (.concrete SiblingAccess.writer) Size.ZERO SiblingAccess.size .Write
        tags .VisitChildrenOfAccessed (fun _ _ => True) (fun _ _ _ => False) := by
  simp only [accessPre_iff, wp, WP.wpTrans, access]
  generalize tree.performBorrowAccessRange (.concrete SiblingAccess.writer) Size.ZERO
    SiblingAccess.size .Write tags .VisitChildrenOfAccessed = result
  rcases result with ⟨after, locations, status⟩
  cases status <;> rfl

/-- The ordinary ranged effects generate the protector condition for distinct
reader and writer tags on branches of the same allocation. -/
example (readerHeld writerHeld : Bool) :
    let tags := SiblingAccess.protectors readerHeld writerHeld
    Triple (do
      let _ ← access (.concrete SiblingAccess.reader) Size.ZERO SiblingAccess.size
        .Read tags .VisitChildrenOfAccessed
      access (.concrete SiblingAccess.writer) Size.ZERO SiblingAccess.size
        .Write tags .VisitChildrenOfAccessed)
      (fun tree => tree = SiblingAccess.initialTree readerHeld writerHeld ∧
        readerHeld = false ∧ writerHeld = false)
      (fun _ _ => True) (fun _ _ => False) := by
  dsimp only
  vcgen
  rename_i before h
  obtain ⟨rfl, safe⟩ := h
  simpa only [binderNameHint, writeWP] using (SiblingAccess.readThenWrite readerHeld writerHeld).mpr safe

private def cellSiblings : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1, 2]⟩, ⟨some 0, []⟩, ⟨some 0, []⟩]⟩
  defaultStates := #[⟨.Unique, true, .None⟩, ⟨.Cell, false, .Write⟩,
    ⟨.ReservedFrz false, false, .Read⟩]
  protectedNodes := []
  locationStates := #[none, none, none]
}

/-- The local read clears the reader's SIFA. A write through its sibling
then visits that branch, which would have been pruned before the read. -/
example :
    let mode := Tree.ChildrenVisitMode.VisitChildrenOfAccessed
    let reads := (cellSiblings.topology.traverseWithSkip 1 mode
      (cellSiblings.shouldSkipForeignNode .Read)).2
    (cellSiblings.topology.traverseWithSkip 2 mode
      (cellSiblings.shouldSkipForeignNode .Write)).2 = [⟨2, .LocalAccess⟩, ⟨0, .LocalAccess⟩] ∧
    (Miri.Verification.TreeVisitWP.writeScheduleAfterRead cellSiblings reads 2 mode).2 =
      [⟨2, .LocalAccess⟩, ⟨0, .LocalAccess⟩, ⟨1, .ForeignAccess⟩] := by
  cbv

example :
    cellSiblings.accessPre 1 .Read .VisitChildrenOfAccessed (fun read =>
      read.status = .Completed ∧
        read.tree.accessPre 2 .Write .VisitChildrenOfAccessed (fun write => write.status = .Completed)) := by
  apply (Miri.Verification.TreeVisitWP.normal_read_write_pre_iff cellSiblings
    1 2 .VisitChildrenOfAccessed .VisitChildrenOfAccessed (by cbv; decide) (by cbv; decide)).mpr
  cbv
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals exact ⟨_, _, _, _, rfl, rfl, rfl⟩

end MiriTests.Verification.TreeSiblingWP

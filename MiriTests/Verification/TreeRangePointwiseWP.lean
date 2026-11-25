import Miri.Verification.TreeRangePointwiseWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeRangePointwiseWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open Miri.Verification.TreeRangeOutcomeWP Miri.Verification.TreeRangePointwiseWP
open Miri.Verification.TreeBorrowsWP

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def child : BorTag := ⟨2, by decide⟩
private def twoBytes := Size.ofBytes 2
private def frozen := DedupRangeMap.new (Size.ofBytes 1) (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
private def withChild :=
  (BorrowTree.new BorTag.one twoBytes).newChild Size.ZERO (.concrete BorTag.one) child frozen .Cell false
private def initial := (withChild.tree.exposeTag {} BorTag.one).tree
private def readSlots := initial.locations.iterMut Size.ZERO twoBytes

private def retained (cursor : Nat) : BorrowTree.TreeLocationAccessAtResult :=
  match readSlots.segments[cursor]? with
  | none => ⟨default, none, none⟩
  | some segment => ⟨segment.data, none, none⟩

private def writeSlots := (readLocations readSlots retained).iterMut Size.ZERO twoBytes

/-- The same two-byte region has two aligned snapshots for a wildcard read
followed by a concrete write. The proof uses the individual read results and
the write's pointwise locations through the original topology. -/
example :
    wp ((do
      let reads ← access .wildcard Size.ZERO twoBytes .Read {} .VisitChildrenOfAccessed
      let writes ← access (.concrete BorTag.one) Size.ZERO twoBytes .Write {} .VisitChildrenOfAccessed
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => True) (fun _ _ => False) initial := by
  miri_tree_range_wp pointwise
  refine ⟨True.intro, by cbv, retained, ?_, ?_⟩
  · have count : readSlots.positions.size = 2 := by cbv
    intro i inside
    change i < readSlots.positions.size at inside
    rw [count] at inside
    have select : i = 0 ∨ i = 1 := by omega
    rcases select with rfl | rfl
    · refine ⟨0, _, by cbv, by cbv, by cbv, ?_⟩
      cbv
    · refine ⟨1, _, by cbv, by cbv, by cbv, ?_⟩
      cbv
  · have count : writeSlots.positions.size = 2 := by cbv
    refine ⟨by cbv, by cbv, ?_⟩
    intro i inside
    change i < writeSlots.positions.size at inside
    rw [count] at inside
    have select : i = 0 ∨ i = 1 := by omega
    rcases select with rfl | rfl
    · refine ⟨0, _, by cbv, by cbv, by cbv, ?_⟩
      cbv
    · refine ⟨1, _, by cbv, by cbv, by cbv, ?_⟩
      cbv

private def oneByte := Size.ofBytes 1
private def exposedRoot := ((BorrowTree.new BorTag.one twoBytes).exposeTag {} BorTag.one).tree
private def splitRead := exposedRoot.locations.iterMut Size.ZERO oneByte
private def splitRetained (cursor : Nat) : BorrowTree.TreeLocationAccessAtResult :=
  ⟨(splitRead.segments[cursor]?.map (·.data)).getD default, none, none⟩
private def mergeWrite := (readLocations splitRead splitRetained).iterMut Size.ZERO twoBytes

/-- The one-byte read splits the original segment. The two-byte write then
merges equal adjacent locations before checking its single snapshot. -/
example :
    wp ((do
      let reads ← access .wildcard Size.ZERO oneByte .Read {} .VisitChildrenOfAccessed
      let writes ← access (.concrete BorTag.one) Size.ZERO twoBytes .Write {} .VisitChildrenOfAccessed
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => True) (fun _ _ => False) exposedRoot := by
  miri_tree_range_wp pointwise
  refine ⟨True.intro, by cbv, splitRetained, ?_, ?_⟩
  · have split : splitRead.state.entries.size = 2 := by cbv
    have count : splitRead.positions.size = 1 := by cbv
    intro i inside
    change i < splitRead.positions.size at inside
    rw [count] at inside
    have zero : i = 0 := by omega
    subst i
    have first : 0 < splitRead.state.entries.size := by rw [split]; decide
    refine ⟨0, _, by cbv, by cbv, first, ?_⟩
    cbv
  · have merged : mergeWrite.positions.size = 1 := by cbv
    refine ⟨by cbv, by cbv, ?_⟩
    intro i inside
    change i < mergeWrite.positions.size at inside
    rw [merged] at inside
    have zero : i = 0 := by omega
    subst i
    refine ⟨0, _, by cbv, by cbv, by cbv, ?_⟩
    cbv

end MiriTests.Verification.TreeRangePointwiseWP

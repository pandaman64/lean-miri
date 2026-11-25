import Miri.Verification.TreeWildcardPairWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeWildcardPairWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open Miri.Verification.TreeBorrowsWP Miri.Verification.TreeRangeOutcomeWP
open Miri.Verification.TreeWildcardPairWP

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def aliasTag : BorTag := ⟨2, by decide⟩
private def oneByte := Size.ofBytes 1
private def frozen := DedupRangeMap.new oneByte (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
private def protectors := ({} : ProtectedTags).insert aliasTag .StrongProtector
private def initial :=
  let main := BorrowTree.new BorTag.one oneByte
  let pair := main.newChild Size.ZERO .wildcard aliasTag frozen .Frozen true
  (pair.tree.exposeTag {} BorTag.one).tree

private def prepared := initial.locations.iterMut Size.ZERO oneByte
private def initialLocation := (prepared.segments[0]?.map (·.data)).getD default

private theorem twoRoots : initial.roots = #[⟨0⟩, ⟨1⟩] := by cbv

private theorem forest : LeafForest initial := by
  intro root member
  rw [twoRoots] at member
  simp at member
  rcases member with rfl | rfl <;> exact ⟨_, by cbv, by cbv⟩

/-- Protecting the second root still permits a read. The same initial
permissions reject a wildcard write because that root sees a foreign access. -/
example :
    rootsPre initial .Read protectors (fun _ => True)
      (List.range' 0 initial.roots.size) initialLocation ∧
      ¬ rootsPre initial .Write protectors (fun _ => True)
        (List.range' 0 initial.roots.size) initialLocation := by
  rw [rootsPre_iff_leafForest initial forest, rootsPre_iff_leafForest initial forest]
  cbv

private def retained (_ : Nat) : BorrowTree.TreeLocationAccessAtResult :=
  ⟨initialLocation, none, none⟩

private def writeSlots :=
  (Miri.Verification.TreeRangePointwiseWP.readLocations prepared retained).iterMut Size.ZERO oneByte

/-- Without the write protector, the same two-root read and write passes the
whole ranged WP. The independent read snapshot determines the write map. -/
example :
    wp ((do
      let reads ← access .wildcard Size.ZERO oneByte .Read protectors .SkipChildrenOfAccessed
      let writes ← access .wildcard Size.ZERO oneByte .Write {} .VisitChildrenOfAccessed
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => True) (fun _ _ => False) initial := by
  rw [wp_read_write_iff]
  refine ⟨by cbv, retained, ?_, by cbv, ?_⟩
  · intro cursor inside
    change cursor < prepared.positions.size at inside
    have count : prepared.positions.size = 1 := by cbv
    rw [count] at inside
    have zero : cursor = 0 := by omega
    subst cursor
    refine ⟨0, _, by cbv, by cbv, by cbv, ?_⟩
    rw [rootsPre_iff_leafForest initial forest]
    cbv
  · intro cursor inside
    change cursor < writeSlots.positions.size at inside
    have count : writeSlots.positions.size = 1 := by cbv
    rw [count] at inside
    have zero : cursor = 0 := by omega
    subst cursor
    refine ⟨0, _, by cbv, by cbv, by cbv, ?_⟩
    rw [rootsPre_iff_leafForest initial forest]
    cbv

private def descendant : BorTag := ⟨3, by decide⟩
private def nested :=
  (initial.newChild Size.ZERO (.concrete aliasTag) descendant frozen .Frozen true).tree
private def nestedLocation :=
  (((nested.locations.iterMut Size.ZERO oneByte).segments[0]?).map (·.data)).getD default
private def heldDescendant := ({} : ProtectedTags).insert descendant .StrongProtector

private theorem nestedRoots : nested.roots = #[⟨0⟩, ⟨1⟩] := by cbv

private def descendantDisabled (after : LocationTree) : Prop :=
  (after.perms.get ⟨2⟩).map (·.permission) = some .Disabled

/-- A protector on a child of the secondary root also rejects a foreign
write. The per-position rule checks the child before the secondary root. -/
example :
    rootsPre nested .Read heldDescendant (fun _ => True)
      (List.range' 0 nested.roots.size) nestedLocation ∧
      (¬ rootsPre nested .Write heldDescendant (fun _ => True)
        (List.range' 0 nested.roots.size) nestedLocation) ∧
      rootsPre nested .Write {} descendantDisabled
        (List.range' 0 nested.roots.size) nestedLocation := by
  simp only [rootsPre_two nested _ _ nestedRoots, ← permissionRootPre_iff]
  cbv <;> simp

end MiriTests.Verification.TreeWildcardPairWP

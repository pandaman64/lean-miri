import Miri.Verification.TreeRangeOutcomeWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeRangeOutcomeWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.Verification.TreeBorrowsWP Miri.Verification.TreeRangeOutcomeWP Std.WP

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def prefixTag : BorTag := ⟨2, by decide⟩
private def heldTag : BorTag := ⟨3, by decide⟩
private def oneByte := Size.ofBytes 1
private def threeBytes := Size.ofBytes 3
private def frozen := DedupRangeMap.new oneByte (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
private def protectors := ({} : ProtectedTags).insert heldTag .StrongProtector
private def root := BorrowTree.new BorTag.one threeBytes
private def withPrefix := (root.newChild Size.ZERO (.concrete BorTag.one) prefixTag frozen .Cell false).tree
private def withHeld := (withPrefix.newChild oneByte (.concrete BorTag.one) heldTag frozen .Cell true).tree
private def exposed := (withHeld.exposeTag {} BorTag.one).tree

private def permissionAt (tree : BorrowTree) (position : Nat) (node : UniIndex) : Option Permission :=
  (tree.locations.entries[position]?.bind fun segment => segment.data.perms.get node).map (·.permission)

/-- A wildcard read succeeds before a concrete write fails on its second
snapshot. The typed error carries only the two visited write ranges. The
first and failing snapshots both commit their disabled permissions. -/
example :
    wp ((do
      let reads ← access .wildcard Size.ZERO oneByte .Read {} .VisitChildrenOfAccessed
      let writes ← access (.concrete BorTag.one) Size.ZERO threeBytes .Write protectors
        .VisitChildrenOfAccessed
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => False)
      (fun (error, locations) tree =>
        error = .AccessFailure ⟨1, 2⟩ (.TransitionError 2 (.ProtectedDisabled .Frozen)) ∧
          locations.map (·.range) = #[⟨0, 1⟩, ⟨1, 2⟩] ∧
          permissionAt tree 0 ⟨1⟩ = some .Disabled ∧
          permissionAt tree 1 ⟨2⟩ = some .Disabled ∧
          tree.locations.entries[2]? = exposed.locations.entries[2]?) exposed := by
  rw [wp_read_write_outcomePre_iff]
  cbv

private def broken : BorrowTree := { exposed with roots := #[⟨0⟩, ⟨9⟩] }

/-- A wildcard read stops at the missing root, and its failure retains the
range trace. Even a missing writer tag is never checked in this branch. -/
example :
    wp ((do
      let reads ← access .wildcard Size.ZERO threeBytes .Read {} .VisitChildrenOfAccessed
      let writes ← access (.concrete ⟨4, by decide⟩) Size.ZERO threeBytes .Write {}
        .VisitChildrenOfAccessed
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => False)
      (fun (error, locations) tree =>
        error = .WildcardFailure ⟨0, 1⟩ (.MissingNode ⟨9⟩) ∧
          locations.map (·.range) = #[⟨0, 1⟩] ∧ tree.roots = broken.roots) broken := by
  rw [wp_read_write_outcomePre_iff]
  cbv

end MiriTests.Verification.TreeRangeOutcomeWP

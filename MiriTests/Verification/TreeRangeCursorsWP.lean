import Miri.Verification.TreeRangeCursorsWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeRangeCursorsWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open Miri.Verification.TreeRangeOutcomeWP Miri.Verification.TreeBorrowsWP
open Miri.Verification.TreeRangeCursorsWP

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def detached : BorrowTree := ⟨{}, {}, {}, #[]⟩
private def changed : LocationTree where
  perms := ({} : UniValMap Tree.LocationState).insert ⟨0⟩ ⟨.Frozen, true, .Read⟩

private def prepared : IterMutResult LocationTree :=
  let segments := #[⟨⟨0, 1⟩, changed⟩, ⟨⟨1, 2⟩, {}⟩]
  ⟨⟨segments⟩, #[0, 1], segments, .ok ()⟩

/-- The cursor continuation retains both prepared read locations by index. -/
example :
    readCursorsPre detached prepared none {} .VisitChildrenOfAccessed
      (fun retained => (retained 0).location = changed ∧ (retained 1).location = {})
      [0, 1] (fun _ => ⟨{}, none, none⟩) := by
  cbv

/-- The same tactic handles a raw weakest precondition. -/
example (tree : BorrowTree) (reader writer : ProvenanceExtra) (readLength writeLength : Size)
    (safe : Miri.Verification.TreeRangeCursorsWP.readWritePre tree reader writer Size.ZERO readLength
      Size.ZERO writeLength {} {} .VisitChildrenOfAccessed .VisitChildrenOfAccessed) :
    wp ((do
      let reads ← access reader Size.ZERO readLength .Read {} .VisitChildrenOfAccessed
      let writes ← access writer Size.ZERO writeLength .Write {} .VisitChildrenOfAccessed
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun _ _ => True) (fun _ _ => False) tree := by
  miri_tree_range_wp safety
  exact safe

set_option experimental.vcgen true in
/-- A nested read and write goes through VC generation before the safety
tactic applies the initial-state cursor rule. -/
example (reader writer : ProvenanceExtra) (readLength writeLength : Size) :
    Triple ((do
      let reads ← access reader Size.ZERO readLength .Read {} .VisitChildrenOfAccessed
      let writes ← access writer Size.ZERO writeLength .Write {} .VisitChildrenOfAccessed
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace))
      (fun current => Miri.Verification.TreeRangeCursorsWP.readWritePre current reader writer Size.ZERO readLength
        Size.ZERO writeLength {} {} .VisitChildrenOfAccessed .VisitChildrenOfAccessed)
      (fun _ _ => True) (fun _ _ => False) := by
  vcgen
  miri_tree_range_wp safety
  assumption

end MiriTests.Verification.TreeRangeCursorsWP

import Miri.Verification.MutableRetagFootprint

namespace Miri.Verification.MutableRetagFootprint

open Miri.ABI Miri.DataStructures Miri.TreeBorrows
open BorrowTree BorrowTree.ZeroProtection BorrowTree.MutationVerification

/-- A materialized location's rights depend on these two fields; its SIFA
can be weakened independently. -/
def storedPermission (location : LocationTree) (query : UniIndex) :
    Option (Permission × Bool) :=
  (location.perms.get query).map (fun state => (state.permission, state.accessed))

/-- A concrete ancestor bookkeeping update preserves both permission fields
at every member of the actual allocation's range table. -/
theorem weakened_storedPermission (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess) (position : Nat) (valid : position < tree.locations.entries.size)
    (query : UniIndex) :
    let next := weakened tree index node strongest
    let stillValid : position < next.locations.entries.size := by
      simpa [next, weakened, DedupRangeMap.modifyAll] using valid
    next.locations.entries[position].range = tree.locations.entries[position].range ∧
      storedPermission next.locations.entries[position].data query =
        storedPermission tree.locations.entries[position].data query := by
  dsimp only
  simp only [weakened, DedupRangeMap.modifyAll, Array.getElem_map]
  generalize tree.locations.entries[position].data = location
  cases found : location.perms.get index with
  | none => simp
  | some prior =>
    by_cases self : query = index
    · subst query
      simp [found, storedPermission, Sparse.get_same]
    · simp [storedPermission, Sparse.get_other _ _ _ _ self]

end Miri.Verification.MutableRetagFootprint

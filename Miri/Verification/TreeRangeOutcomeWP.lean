import Miri.Verification.TreeBorrowsWP

namespace Miri.Verification.TreeRangeOutcomeWP

open Miri.ABI Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree

abbrev Trace := Array BorrowTreeLocationResult
abbrev RangeAccessError := BorrowTreeAccessStatus × Trace

/-- The exact range contract checks the initial prepared snapshots in order.
Each location contract commits the visited state and trace before dispatching
an error. The write prepares its snapshots only after the read completes. -/
def readWritePre (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (post : Trace × Trace → BorrowTree → Prop) (failure : RangeAccessError → BorrowTree → Prop) : Prop :=
  TreeBorrowsWP.accessPre tree reader readOffset readLength .Read readTags readMode
    (fun after reads =>
      TreeBorrowsWP.accessPre after writer writeOffset writeLength .Write writeTags writeMode
        (fun final writes => post (reads, writes) final)
        (fun status retained writes => failure (status, writes) retained))
    (fun status retained reads => failure (status, reads) retained)

/-- Expose the exact range contract in a state-monad continuation. -/
theorem wp_access_outcomePre_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : Trace → BorrowTree → Prop)
    (failure : RangeAccessError → BorrowTree → Prop) :
    wp (TreeBorrowsWP.access provenance offset length kind tags mode) post failure tree ↔
      TreeBorrowsWP.accessPre tree provenance offset length kind tags mode
        (fun next locations => post locations next)
        (fun status retained locations => failure (status, locations) retained) := by
  rw [TreeBorrowsWP.accessPre_iff]
  simp only [wp, WP.wpTrans, TreeBorrowsWP.access]
  generalize tree.performBorrowAccessRange provenance offset length kind tags mode = result
  rcases result with ⟨after, locations, status⟩
  cases status <;> rfl

/-- Pair two successful results and pass the state at either error to the same continuation. -/
theorem wp_pair_bind_iff {E S A B : Type} (read : EStateM E S A) (write : EStateM E S B)
    (state : S) (post : A × B → S → Prop) (failure : E → S → Prop) :
    wp ((do
      let reads ← read
      let writes ← write
      pure (reads, writes)) : EStateM E S (A × B)) post failure state ↔
    wp read (fun reads after =>
      wp write (fun writes => post (reads, writes)) failure after) failure state := by
  simp only [wp, WP.wpTrans, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases read state with
  | error => rfl
  | ok value next =>
    simp only []
    cases write next <;> rfl

/-- Pull a ranged read and write back through their ordered location contracts.
The error continuation receives the failing access's status, trace and
partially updated tree. On success, the postcondition receives both traces. -/
theorem wp_read_write_outcomePre_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (post : Trace × Trace → BorrowTree → Prop) (failure : RangeAccessError → BorrowTree → Prop) :
    wp ((do
      let reads ← TreeBorrowsWP.access reader readOffset readLength .Read readTags readMode
      let writes ← TreeBorrowsWP.access writer writeOffset writeLength .Write writeTags writeMode
      pure (reads, writes)) : EStateM RangeAccessError BorrowTree (Trace × Trace)) post failure tree ↔
    readWritePre tree reader writer readOffset readLength writeOffset writeLength
      readTags writeTags readMode writeMode post failure := by
  simp only [wp_pair_bind_iff, wp_access_outcomePre_iff, readWritePre]

end Miri.Verification.TreeRangeOutcomeWP

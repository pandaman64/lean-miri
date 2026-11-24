import Miri.Verification.TreeBorrowsWP

namespace Miri.Verification.TreeBorrowsWP

open Miri.ABI Miri.Memory Miri.TreeBorrows Std.WP

/-- Full-range access through the root of a fresh allocation succeeds and
preserves the tree. Postconditions that ignore diagnostics reduce directly
to obligations on the input tree. -/
@[simp] theorem accessPre_fresh_root_full (tag : BorTag) (size : Size) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop)
    (failure : BorrowTree.BorrowTreeAccessStatus →
      BorrowTree → Array BorrowTree.BorrowTreeLocationResult → Prop) :
    accessPre (BorrowTree.new tag size) (.concrete tag) Size.ZERO size kind tags mode post failure ↔
      post (BorrowTree.new tag size) (BorrowTree.freshRootAccessLocations tag size tags) := by
  rw [accessPre_iff, BorrowTree.fresh_root_full_access]

/-- The fresh-root rule also applies inside the continuation of a preceding
state effect, where VC generation leaves a weakest precondition. -/
@[simp] theorem wp_access_fresh_root_full (tag : BorTag) (size : Size) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (failure : (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult) →
      BorrowTree → Prop) :
    wp (access (.concrete tag) Size.ZERO size kind tags mode) post failure
      (BorrowTree.new tag size) ↔
      post (BorrowTree.freshRootAccessLocations tag size tags) (BorrowTree.new tag size) := by
  simp only [wp, WP.wpTrans, access, BorrowTree.fresh_root_full_access]

end Miri.Verification.TreeBorrowsWP

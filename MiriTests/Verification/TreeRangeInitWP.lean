import Miri.Verification.ExactWP

namespace MiriTests.Verification.TreeRangeInitWP

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Verification.TreeBorrowsWP Std.WP

set_option experimental.vcgen true

/-- The generated safety condition simplifies for a symbolic allocation size,
access kind, visit mode and protector table. -/
theorem freshRootAccess (tag : BorTag) (size : Size) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (post : BorrowTree → Prop) :
    Triple (access (.concrete tag) Size.ZERO size kind tags mode)
      (fun tree => tree = BorrowTree.new tag size ∧ post tree)
      (fun _ => post) (fun _ _ => False) := by
  vcgen
  rename_i before h
  obtain ⟨rfl, safe⟩ := h
  simpa using safe

/-- A full-range read leaves the same fresh tree for the subsequent write.
The read and write may use different global protector tables. -/
theorem freshRootReadThenWrite (tag : BorTag) (size : Size)
    (readTags writeTags : ProtectedTags) (post : BorrowTree → Prop) :
    Triple (do
      let _ ← access (.concrete tag) Size.ZERO size .Read readTags .VisitChildrenOfAccessed
      access (.concrete tag) Size.ZERO size .Write writeTags .VisitChildrenOfAccessed)
      (fun tree => tree = BorrowTree.new tag size ∧ post tree)
      (fun _ => post) (fun _ _ => False) := by
  vcgen
  rename_i before h
  obtain ⟨rfl, safe⟩ := h
  simpa using safe

/-- For a positive size, the trace exposes the original byte range and
records a single local visit. -/
example (tag : BorTag) (size : Size) (positive : size.bytes ≠ 0)
    (tags : ProtectedTags) :
    Triple (access (.concrete tag) Size.ZERO size .Read tags .SkipChildrenOfAccessed)
      (· = BorrowTree.new tag size)
      (fun locations _ =>
        (locations[0]?.map (·.range)) = some ⟨0, size.bytes⟩ ∧
        ((locations[0]?.bind (·.normalAccess)).map (·.visited)) = some [⟨0, .LocalAccess⟩])
      (fun _ _ => False) := by
  vcgen
  subst_vars
  simp [BorrowTree.freshRootAccessLocations, positive]

end MiriTests.Verification.TreeRangeInitWP

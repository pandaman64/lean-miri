import Miri.Verification.MutableTypedRetag
namespace Miri.TreeBorrows.ProtectedTags
open Miri.Memory

/-- Removing a newly inserted protector restores the original map
when the fresh tag was absent. -/
theorem remove_insert_of_absent (tags : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (absent : tags.contains tag = false) : (tags.insert tag kind).remove tag = tags := by
  have missing : tags.entries.find? (fun pair => pair.1 == tag) = none := by
    cases found : tags.entries.find? (fun pair => pair.1 == tag) with
    | none => rfl
    | some pair => simp [contains, get, found] at absent
  have filter : (tags.entries.filter fun pair => pair.1 != tag) = tags.entries := by
    apply Array.filter_eq_self.mpr
    intro pair member
    have different := Array.find?_eq_none.mp missing pair member
    simp [bne, different]
  unfold insert remove
  simp [filter]

theorem remove_of_absent (tags : ProtectedTags) (tag : BorTag)
    (absent : tags.contains tag = false) : tags.remove tag = tags := by
  have missing : tags.entries.find? (fun pair => pair.1 == tag) = none := by
    cases found : tags.entries.find? (fun pair => pair.1 == tag) with
    | none => rfl
    | some pair => simp [contains, get, found] at absent
  have filter : (tags.entries.filter fun pair => pair.1 != tag) = tags.entries := by
    apply Array.filter_eq_self.mpr
    intro pair member
    have different := Array.find?_eq_none.mp missing pair member
    simp [bne, different]
  cases tags
  simp only [remove, filter]

#print axioms remove_insert_of_absent
#print axioms remove_of_absent
end Miri.TreeBorrows.ProtectedTags

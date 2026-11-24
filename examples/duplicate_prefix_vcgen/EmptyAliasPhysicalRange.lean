import CanonicalCallDomain
import duplicate_prefix.RetagReleaseFootprint

namespace DuplicatePrefix.CanonicalCallDomain
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.Verification
open ArchiveForestProjection GeneralRangeMapOrigins SourceDomain

theorem ReleaseRange.ofByteScope {tree : BorrowTree} {holder : UniIndex} {start : Size}
    (forest : CoherentForest tree) (fits : start.bytes.toNat + 1 ≤ tree.locations.size.bytes.toNat)
    (roots : ∃ root, tree.roots = #[root])
    (scope : RetagReleaseFootprint.MaterializedWithin tree holder start.bytes (start.bytes + 1))
    (vacant : ∀ index, tree.nodeAt index = none → ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none) :
    ReleaseRange tree holder start 1 := by
  have upper : (start.bytes + 1).toNat = start.bytes.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by have h := tree.locations.size.bytes.toNat_lt; omega)]
  refine ⟨fun _ => roots, by simpa using fits, ?_, ?_⟩
  · intro segment member isSome
    obtain ⟨index, valid, eq⟩ := Array.mem_iff_getElem.mp member
    subst segment
    let row := tree.locations.entries[index]
    have formed := forest.ranges
    have nonempty : tree.locations.entries.size ≠ 0 := by omega
    simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at formed
    have proper : row.range.start < row.range.stop := formed.2.1 index valid
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp isSome
    have low := scope row.range.start index valid (UInt64.le_refl _) proper value stored
    let last := UInt64.ofNat (row.range.stop.toNat - 1)
    have lastNat : last.toNat = row.range.stop.toNat - 1 := by
      change (row.range.stop.toNat - 1) % 2^64 = _
      have bound := row.range.stop.toNat_lt
      exact Nat.mod_eq_of_lt (by omega)
    have ordered := UInt64.lt_iff_toNat_lt.mp proper
    have lastLower : row.range.start ≤ last := UInt64.le_iff_toNat_le.mpr (by omega)
    have lastUpper : last < row.range.stop := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have high := scope last index valid lastLower lastUpper value stored
    rw [upper, lastNat] at high
    simp only [UInt64.toNat_one]
    change start.bytes.toNat ≤ row.range.start.toNat ∧ row.range.stop.toNat ≤ start.bytes.toNat + 1
    exact ⟨low.1, by omega⟩
  · intro index missing row member
    obtain ⟨position, valid, same⟩ := Array.mem_iff_getElem.mp member
    subst row
    exact vacant index missing position valid

theorem byteGrant_of_owned {tree : BorrowTree} {point : UInt64} {source : UniIndex} {tags : ProtectedTags}
    (bound : point.toNat + 1 < 2^64)
    (owned : OwnedOn (fun row => LocationRights tree row tags source) point (point + 1) tree.locations) :
    ByteWriteGrant tree point source tags := by
  have upper : (point + 1).toNat = point.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt bound]
  intro segment member begin ends
  obtain ⟨index, valid, same⟩ := Array.mem_iff_getElem.mp member
  subst segment
  have lo := UInt64.le_iff_toNat_le.mp begin
  have hi := UInt64.lt_iff_toNat_lt.mp ends
  exact owned index valid (by omega) (by omega) (by omega)

private theorem orderedRows {map : DedupRangeMap LocationTree} (formed : map.WellFormed)
    (left right : Nat) (h : left < right) (valid : right < map.entries.size) :
    (map.entries[left]'(by omega)).range.stop ≤ map.entries[right].range.start := by
  have nonempty : map.entries.size ≠ 0 := by omega
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at formed
  induction right with
  | zero => omega
  | succ previous ih =>
    have adjacent := formed.2.2 previous valid
    by_cases same : left = previous
    · subst left
      rw [adjacent]
      exact UInt64.le_refl _
    · have between : left < previous := by omega
      have before := ih between (by omega)
      have grows := formed.2.1 previous (by omega)
      rw [← adjacent]
      exact UInt64.le_iff_toNat_le.mpr
        (Nat.le_trans (UInt64.le_iff_toNat_le.mp before) (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp grows)))

theorem ownedAtByte {tree : BorrowTree} {point : UInt64} {source : UniIndex} {tags : ProtectedTags}
    (formed : tree.locations.WellFormed) (bound : point.toNat + 1 < 2^64)
    (covered : ∃ row ∈ tree.locations.entries,
      row.range.start ≤ point ∧ point < row.range.stop ∧ LocationRights tree row.data tags source) :
    OwnedOn (fun row => LocationRights tree row tags source) point (point+1) tree.locations := by
  obtain ⟨row, member, lower, upper, rights⟩ := covered
  obtain ⟨old, oldFits, rowAt⟩ := Array.mem_iff_getElem.mp member
  subst row
  have next : (point+1).toNat = point.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt bound]
  intro current valid less begins ends
  have coversCurrent : tree.locations.entries[current].range.start ≤ point := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have endsCurrent : point < tree.locations.entries[current].range.stop := UInt64.lt_iff_toNat_lt.mpr ends
  by_cases eq : current = old
  · subst current
    exact rights
  · have leftLower := UInt64.le_iff_toNat_le.mp lower
    have leftUpper := UInt64.lt_iff_toNat_lt.mp upper
    have rightLower := UInt64.le_iff_toNat_le.mp coversCurrent
    have rightUpper := UInt64.lt_iff_toNat_lt.mp endsCurrent
    by_cases before : old < current
    · have incompatible := UInt64.le_iff_toNat_le.mp (orderedRows formed old current before valid)
      omega
    · have after : current < old := by omega
      have incompatible := UInt64.le_iff_toNat_le.mp (orderedRows formed current old after oldFits)
      omega

/-- Exact range geometry preserves a selected covered byte, and the retained
pointwise grant supplies rights in the newly stored location row. -/
theorem coveredAfter {before after : BorrowTree}
    (geometry : after.locations.entries.map (·.range) = before.locations.entries.map (·.range))
    {point : UInt64} {source : UniIndex} {tags : ProtectedTags}
    (bound : point.toNat + 1 < 2^64)
    (original : ∃ row ∈ before.locations.entries,
      row.range.start ≤ point ∧ point < row.range.stop)
    (owned : OwnedOn (fun row => LocationRights after row tags source) point (point + 1) after.locations) :
    ∃ row ∈ after.locations.entries, row.range.start ≤ point ∧ point < row.range.stop ∧
      LocationRights after row.data tags source := by
  obtain ⟨row, member, lower, upper⟩ := original
  obtain ⟨index, valid, found⟩ := Array.mem_iff_getElem.mp member
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [Array.size_map] using congrArg Array.size geometry
  have fits : index < after.locations.entries.size := by omega
  have same : after.locations.entries[index].range = row.range := by
    have ranges := congrArg (fun spans : Array ByteRange => spans[index]?) geometry
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem fits, Array.getElem?_eq_getElem valid,
      Option.map_some, Option.some.injEq, found] at ranges
    exact ranges
  refine ⟨_, Array.mem_iff_getElem.mpr ⟨index, fits, rfl⟩, ?_, ?_, ?_⟩
  · rw [same]; exact lower
  · rw [same]; exact upper
  · have next : (point+1).toNat = point.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt bound]
    exact owned index fits (by omega)
      (by rw [same]; have h := UInt64.le_iff_toNat_le.mp lower; omega)
      (by rw [same]; exact UInt64.lt_iff_toNat_lt.mp upper)

#print axioms ReleaseRange.ofByteScope
#print axioms byteGrant_of_owned
#print axioms ownedAtByte
#print axioms coveredAfter

end DuplicatePrefix.CanonicalCallDomain

import CanonicalCallDomain
import AccessedOnlyAuthorize

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open ScopedPhysicalRelease SourceDomain ArchiveForestProjection RetagReleaseFootprint

/-- Every materialized row whose protector is active lies in the given span. -/
def AccessedOnlyWithin (tree : BorrowTree) (holder : UniIndex) (lower upper : Nat) : Prop :=
  Miri.Verification.RangeModifyLaw.EachByte tree.locations (fun point row =>
    ∀ state, row.perms.get holder = some state → state.accessed = true →
      lower ≤ point.toNat ∧ point.toNat < upper)

theorem ReleaseRange.accessedWithin {tree holder start length}
    (ready : ReleaseRange tree holder start length true) :
    AccessedOnlyWithin tree holder start.bytes.toNat (start.bytes.toNat + length.toNat) := by
  intro point position inside lower upper state found accessed
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  have active : (segment.data.perms.get holder).any (·.accessed) = true := by
    simp [segment,found,accessed]
  obtain ⟨starts,stops⟩ := ready.materialized segment member active
  exact ⟨Nat.le_trans starts (UInt64.le_iff_toNat_le.mp lower),
    Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp upper) stops⟩

theorem AccessedOnlyWithin.visitsWithin {tree holder lower upper}
    (scope : AccessedOnlyWithin tree holder lower upper) : VisitsWithin tree holder lower upper := by
  intro point position inside lo hi state _ stored accessed _
  exact scope point position inside lo hi state stored accessed

theorem ReleaseRange.visitsWithin {tree holder start length}
    (ready : ReleaseRange tree holder start length true) :
    VisitsWithin tree holder start.bytes.toNat (start.bytes.toNat + length.toNat) :=
  ready.accessedWithin.visitsWithin

theorem ReleaseRange.toActive {tree holder start length} (ready : ReleaseRange tree holder start length) :
    ReleaseRange tree holder start length true := by
  refine ⟨ready.root,ready.extent,?_,ready.vacant⟩
  intro row member active
  apply ready.materialized row member
  cases saved : row.data.perms.get holder with
  | none => simp [saved] at active
  | some _ => simp

/-- Both endpoint orders permit adjacency at the half-open boundary. -/
theorem disjointResultByteRelative (base byte start : Nat) (length : UInt64) :
    DisjointResultByte (base + byte) (base + start) length ↔ DisjointResultByte byte start length := by
  unfold DisjointResultByte
  omega

theorem ReleaseRange.ofActiveByteScope {tree : BorrowTree} {holder : UniIndex} {start : Size}
    (forest : CoherentForest tree) (fits : start.bytes.toNat + 1 ≤ tree.locations.size.bytes.toNat)
    (roots : ∃ root, tree.roots = #[root])
    (scope : AccessedOnlyWithin tree holder start.bytes.toNat (start.bytes.toNat+1))
    (vacant : ∀ index, tree.nodeAt index = none → ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none) :
    ReleaseRange tree holder start 1 true := by
  refine ⟨fun _ => roots, by simpa using fits, ?_, ?_⟩
  · intro segment member isSome
    obtain ⟨index, valid, eq⟩ := Array.mem_iff_getElem.mp member
    subst segment
    let row := tree.locations.entries[index]
    have formed := forest.ranges
    have nonempty : tree.locations.entries.size ≠ 0 := by omega
    simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at formed
    have proper : row.range.start < row.range.stop := formed.2.1 index valid
    change (row.data.perms.get holder).any (·.accessed) = true at isSome
    cases stored : row.data.perms.get holder with
    | none => simp [stored] at isSome
    | some value =>
      have accessed : value.accessed = true := by simpa [stored] using isSome
      have low := scope row.range.start index valid (UInt64.le_refl _) proper value stored accessed
      let last := UInt64.ofNat (row.range.stop.toNat - 1)
      have lastNat : last.toNat = row.range.stop.toNat - 1 := by
        change (row.range.stop.toNat - 1) % 2^64 = _
        have bound := row.range.stop.toNat_lt
        exact Nat.mod_eq_of_lt (by omega)
      have ordered := UInt64.lt_iff_toNat_lt.mp proper
      have lastLower : row.range.start ≤ last := UInt64.le_iff_toNat_le.mpr (by omega)
      have lastUpper : last < row.range.stop := UInt64.lt_iff_toNat_lt.mpr (by omega)
      have high := scope last index valid lastLower lastUpper value stored accessed
      rw [lastNat] at high
      simp only [UInt64.toNat_one]
      change start.bytes.toNat ≤ row.range.start.toNat ∧ row.range.stop.toNat ≤ start.bytes.toNat + 1
      exact ⟨low.1, by omega⟩
  · intro index missing row member
    obtain ⟨position, valid, same⟩ := Array.mem_iff_getElem.mp member
    subst row
    exact vacant index missing position valid

#print axioms ReleaseRange.visitsWithin
#print axioms ReleaseRange.toActive
end DuplicatePrefix.CanonicalCallDomain

import Lean

namespace DuplicatePrefix.CopySortMembership

open Lean Meta Elab Term

private def resolveArrayRoutine (suffix : String) : TermElabM Expr := do
  let [name] := (← getEnv).constants.toList.filterMap (fun (name, _) =>
      if name.toString.endsWith suffix then some name else none)
    | throwError "expected one array sorting declaration for {suffix}"
  mkConstWithFreshMVarLevels name

local elab "sort_core" : term => resolveArrayRoutine ".Array.qsort.sort"
local elab "partition_core" : term => resolveArrayRoutine ".Array.qpartition.loop"
local elab "sort_equation" : term => resolveArrayRoutine ".Array.qsort.sort.eq_def"
local elab "partition_equation" : term => resolveArrayRoutine ".Array.qpartition.loop.eq_def"

private def EveryEntry (holds : α → Prop) (vector : Vector α size) : Prop :=
  ∀ i (valid : i < size), holds vector[i]

private theorem swapped (holds : α → Prop) (as : Vector α size)
    (i j : Nat) (hi : i < size) (hj : j < size) (prior : EveryEntry holds as) :
    EveryEntry holds (as.swap i j hi hj) := by
  intro k hk
  rw [Vector.getElem_swap hi hj hk]
  split <;> first | exact prior j hj | split <;> first | exact prior i hi | exact prior k hk

private theorem partitionLoop (holds : α → Prop) (lt : α → α → Bool)
    (lo hi : Nat) (bounded : hi < size) (pivot : α)
    (as : Vector α size) (i k : Nat) (low : lo ≤ i) (order : i ≤ k) (top : k ≤ hi)
    (initial : EveryEntry holds as) :
    EveryEntry holds (partition_core lt lo hi bounded pivot as i k low order top).2 := by
  rw [partition_equation]
  split
  · rename_i more
    split
    · exact partitionLoop holds lt lo hi bounded pivot _ (i+1) (k+1)
        (by omega) (by omega) (by omega) (swapped holds as i k (by omega) (by omega) initial)
    · exact partitionLoop holds lt lo hi bounded pivot as i (k+1)
        low (by omega) (by omega) initial
  · exact swapped holds as i hi (by omega) bounded initial
termination_by hi - k

private theorem partition (holds : α → Prop) (lt : α → α → Bool)
    (as : Vector α size) (lo hi : Nat) (order : lo ≤ hi)
    (lower : lo < size) (upper : hi < size) (initial : EveryEntry holds as) :
    EveryEntry holds (Array.qpartition as lt lo hi order lower upper).2 := by
  unfold Array.qpartition
  apply partitionLoop
  repeat' (first | exact initial | split | apply swapped)

private theorem sort (holds : α → Prop) (lt : α → α → Bool)
    (as : Vector α size) (lo hi : Nat) (order : lo ≤ hi)
    (lower : lo < size) (upper : hi < size) (initial : EveryEntry holds as) :
    EveryEntry holds (sort_core lt as lo hi order lower upper) := by
  rw [sort_equation]
  split
  · rename_i more
    have retained := partition holds lt as lo hi order lower upper initial
    generalize parts : Array.qpartition as lt lo hi order lower upper = result at retained ⊢
    rcases result with ⟨⟨mid, range⟩, region⟩
    simp only at retained ⊢
    split
    · exact retained
    · rename_i narrower
      have left := sort holds lt region lo mid range.1 lower (by omega) retained
      exact sort holds lt _ (mid+1) hi (by omega) (by omega) upper left
  · exact initial
termination_by hi - lo

/-- Sorting a provenance table does not introduce any entries. -/
theorem subset (as : Array α) (lt : α → α → Bool) (a : α)
    (member : a ∈ as.qsort lt) : a ∈ as := by
  unfold Array.qsort at member
  split at member
  · exact member
  · have all := sort (fun x => x ∈ as) lt as.toVector 0 (as.size-1)
      (Nat.zero_le _) (by omega) (by omega) (fun i valid => Array.getElem_mem valid)
    obtain ⟨i, valid, exactValue⟩ := Array.mem_iff_getElem.mp member
    have legal : i < as.size := by simpa using valid
    have value : (sort_core lt as.toVector 0 (as.size-1) (Nat.zero_le _) (by omega) (by omega))[i]'legal = a := by
      simpa only [Nat.zero_min, Nat.min_self, Nat.max_eq_right (Nat.zero_le _), Vector.getElem_toArray] using exactValue
    exact value ▸ all i legal

#print axioms subset
end DuplicatePrefix.CopySortMembership

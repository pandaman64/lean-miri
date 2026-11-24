import Miri.TreeBorrows.TreeState

namespace Miri.TreeBorrows.BorrowTree.ZeroProtection

open Miri.Memory

/-- A path of actual occupied table indices, starting at the selected node. -/
private def occupiedPath (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) : List Nat :=
  match present : nodes.get index with
  | none => []
  | some node =>
    match edge : node.parent with
    | none => [index.toNat]
    | some parent => index.toNat :: occupiedPath nodes depth parent
termination_by depth.depth index
decreasing_by exact (depth.parent index node present parent edge).choose_spec.2

private theorem path_nonempty (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) :
    0 < (occupiedPath nodes depth index).length := by
  rw [occupiedPath, present]
  dsimp only
  split <;> simp

private theorem path_slots (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) :
    (occupiedPath nodes depth index).Nodup ∧
      ∀ position ∈ occupiedPath nodes depth index, ∃ query node,
        query.toNat = position ∧ nodes.get query = some node ∧ depth.depth query ≤ depth.depth index := by
  rw [occupiedPath]
  split
  · simp
  · rename_i node stored
    split
    · refine ⟨by simp, ?_⟩
      intro position member
      simp only [List.mem_singleton] at member
      exact ⟨index, node, member.symm, stored, Nat.le_refl _⟩
    · rename_i parent edge
      obtain ⟨prior, before, smaller⟩ := depth.parent index node stored parent edge
      obtain ⟨distinct, bounded⟩ := path_slots nodes depth parent
      refine ⟨List.nodup_cons.mpr ⟨?_, distinct⟩, ?_⟩
      · intro included
        obtain ⟨query, _, equal, _, priorDepth⟩ := bounded index.toNat included
        cases index_injective query index equal
        omega
      · intro position included
        rw [List.mem_cons] at included
        rcases included with same | tail
        · exact ⟨index, node, same.symm, stored, Nat.le_refl _⟩
        · obtain ⟨query, earlier, eq, present, priorDepth⟩ := bounded position tail
          exact ⟨query, earlier, eq, present, Nat.le_trans priorDepth (Nat.le_of_lt smaller)⟩
termination_by depth.depth index
decreasing_by assumption

private theorem path_fits (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) : (occupiedPath nodes depth index).length ≤ nodes.size := by
  obtain ⟨unique, bounded⟩ := path_slots nodes depth index
  have included : occupiedPath nodes depth index ⊆ List.range nodes.size := by
    intro position member
    obtain ⟨query, node, eq, present, _⟩ := bounded position member
    rw [← eq, List.mem_range]
    exact lookup_valid nodes query node present
  have fits := unique.length_le_of_subset included
  simpa only [List.length_range] using fits

/-- Any acyclic occupied parent forest has a depth certificate that is
strictly below the table size at every occupied slot. Its rank is the
number of real parent edges to a root. -/
theorem ParentDepth.tight (nodes : UniValMap TreeNode) (certificate : ParentDepth nodes) :
    ∃ depth : ParentDepth nodes, ∀ index node, nodes.get index = some node →
      depth.depth index < nodes.size := by
  let rank (index : UniIndex) := (occupiedPath nodes certificate index).length - 1
  have bound : ∀ index node, nodes.get index = some node → rank index < nodes.size := by
    intro index node stored
    have nonempty := path_nonempty nodes certificate index node stored
    have fits := path_fits nodes certificate index
    dsimp only [rank]
    omega
  let next : ParentDepth nodes := {
    depth := rank
    bounded := fun index node stored => Nat.le_of_lt (bound index node stored)
    parent := by
      intro index node stored parent edge
      obtain ⟨prior, present, _⟩ := certificate.parent index node stored parent edge
      have positive := path_nonempty nodes certificate parent prior present
      refine ⟨prior, present, ?_⟩
      dsimp only [rank]
      have step : occupiedPath nodes certificate index = index.toNat :: occupiedPath nodes certificate parent := by
        rw [occupiedPath, stored]
        dsimp only
        rw [edge]
      rw [step]
      simp only [List.length_cons]
      omega }
  exact ⟨next, bound⟩

#print axioms ParentDepth.tight
end Miri.TreeBorrows.BorrowTree.ZeroProtection

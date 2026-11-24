import PreparedCallWitness

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix SourceDomain CanonicalCallDomain

namespace DuplicatePrefix.SameAllocationWitness

abbrev rootTag := PreparedCallWitness.srcTag
abbrev sliceTag := PreparedCallWitness.heldTag
def outputTag : BorTag := ⟨33, by decide⟩
def rootIndex : UniIndex := ⟨0⟩
def sliceIndex : UniIndex := ⟨1⟩
def outputIndex : UniIndex := ⟨2⟩

def rootNode : TreeNode := {
  tag := rootTag, parent := none, children := #[sliceIndex, outputIndex],
  defaultInitialPermission := .Disabled, defaultInitialSifa := .None
}

def child (tag : BorTag) : TreeNode := {
  tag, parent := some rootIndex, children := #[],
  defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None
}

def parentPermission : LocationState := ⟨.Unique, true, .None⟩
def childPermission : LocationState := ⟨.ReservedFrz false, true, .None⟩
def sourcePermissions : LocationTree := ⟨⟨#[some parentPermission, some childPermission]⟩, {}⟩
def dormantSlicePermission : LocationState := ⟨.Disabled, false, .Write⟩
def outputPermissions : LocationTree :=
  ⟨⟨#[some parentPermission, some dormantSlicePermission, some childPermission]⟩, {}⟩

def sourceRow : RangeMapSegment LocationTree := ⟨⟨0, 2⟩, sourcePermissions⟩
def outputRow : RangeMapSegment LocationTree := ⟨⟨2, 3⟩, outputPermissions⟩

def tree : BorrowTree := {
  tagMapping := { mapping := #[(rootTag, rootIndex), (sliceTag, sliceIndex), (outputTag, outputIndex)] }
  nodes := { data := #[some rootNode, some (child sliceTag), some (child outputTag)] }
  locations := ⟨#[sourceRow, outputRow]⟩
  roots := #[rootIndex]
}

theorem lookupCases {index : UniIndex} {node : TreeNode}
    (found : tree.nodeAt index = some node) :
    (index = rootIndex ∧ node = rootNode) ∨
      (index = sliceIndex ∧ node = child sliceTag) ∨
      (index = outputIndex ∧ node = child outputTag) := by
  have bound : index.toNat < 3 := by
    by_cases valid : index.toNat < 3
    · exact valid
    · exfalso
      have missing := Array.getElem?_eq_none (xs := tree.nodes.data) (by change 3 ≤ index.toNat; omega)
      simp [BorrowTree.nodeAt, UniValMap.get, missing] at found
  have cases : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 := by omega
  rcases cases with zero | one | two
  · have eq : index = rootIndex := Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
      ((congrArg UniIndex.ofNat? zero).trans rfl))
    subst index
    exact .inl ⟨rfl, (Option.some.inj found).symm⟩
  · have eq : index = sliceIndex := Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
      ((congrArg UniIndex.ofNat? one).trans rfl))
    subst index
    exact .inr (.inl ⟨rfl, (Option.some.inj found).symm⟩)
  · have eq : index = outputIndex := Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
      ((congrArg UniIndex.ofNat? two).trans rfl))
    subst index
    exact .inr (.inr ⟨rfl, (Option.some.inj found).symm⟩)

private theorem rowsWellFormed : tree.locations.WellFormed := by
  change (if h : 2 = 0 then True else _)
  simp only [Nat.reduceEqDiff, ↓reduceDIte]
  refine ⟨rfl, ?_, ?_⟩
  · intro index bound
    change index < 2 at bound
    have indices : index = 0 ∨ index = 1 := by omega
    rcases indices with rfl | rfl
    · change (0 : UInt64) < 2; decide
    · change (2 : UInt64) < 3; decide
  · intro index bound
    change index + 1 < 2 at bound
    have zero : index = 0 := by omega
    subst index
    rfl

theorem coherent : CoherentForest tree := by
  refine ⟨rowsWellFormed, by decide, by decide, ?_, ⟨UniIndex.toNat, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro index member
    have eq : index = rootIndex := by simpa [tree] using member
    subst index
    exact ⟨rootNode, rfl⟩
  · intro index node found
    rcases lookupCases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro index node parent found edge
    rcases lookupCases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · contradiction
    · have eq : parent = rootIndex := (Option.some.inj edge).symm
      subst parent
      decide
    · have eq : parent = rootIndex := (Option.some.inj edge).symm
      subst parent
      decide
  · intro index node found
    rcases lookupCases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [tree, rootNode, child, rootIndex, sliceIndex, outputIndex]
  · intro index node found
    rcases lookupCases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨by decide, ?_, ?_⟩
      · intro next member
        have cases : next = sliceIndex ∨ next = outputIndex := by
          simpa [rootNode] using member
        rcases cases with rfl | rfl <;> exact ⟨_, rfl, rfl⟩
      · intro next node present edge
        rcases lookupCases present with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · contradiction
        · simp [rootNode]
        · simp [rootNode]
    · refine ⟨by decide, fun next member => ?_, fun next node present edge => ?_⟩
      · simp [child] at member
      · rcases lookupCases present with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · contradiction
        · exact False.elim ((by decide : rootIndex ≠ sliceIndex) (Option.some.inj edge))
        · exact False.elim ((by decide : rootIndex ≠ sliceIndex) (Option.some.inj edge))
    · refine ⟨by decide, fun next member => ?_, fun next node present edge => ?_⟩
      · simp [child] at member
      · rcases lookupCases present with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · contradiction
        · exact False.elim ((by decide : rootIndex ≠ outputIndex) (Option.some.inj edge))
        · exact False.elim ((by decide : rootIndex ≠ outputIndex) (Option.some.inj edge))
  · intro index node parent found edge
    rcases lookupCases found with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · contradiction
    · have eq : parent = rootIndex := (Option.some.inj edge).symm
      subst parent
      exact ⟨rootNode, rfl⟩
    · have eq : parent = rootIndex := (Option.some.inj edge).symm
      subst parent
      exact ⟨rootNode, rfl⟩

theorem rowCases {row : RangeMapSegment LocationTree} (member : row ∈ tree.locations.entries) :
    row = sourceRow ∨ row = outputRow := by
  simpa [tree] using member

theorem availableKeys : RetagInsertionCapacity.Ready tree := by
  refine ⟨?_, ?_, by decide, rfl, by decide, ?_⟩
  · intro key member
    change key ∈ #[(rootTag,rootIndex), (sliceTag,sliceIndex), (outputTag,outputIndex)] at member
    have cases : key = (rootTag,rootIndex) ∨ key = (sliceTag,sliceIndex) ∨
      key = (outputTag,outputIndex) := by simpa using member
    rcases cases with rfl | rfl | rfl <;> exact ⟨_,rfl,rfl⟩
  · intro index member
    change index ∈ #[] at member
    simp at member
  · intro index absent position inside
    have large : 3 ≤ index.toNat := by
      by_cases lower : index.toNat < 3
      · exfalso
        have cases : index.toNat = 0 ∨ index.toNat = 1 ∨ index.toNat = 2 := by omega
        rcases cases with zero | one | two
        · have eq : index = rootIndex := Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
            ((congrArg UniIndex.ofNat? zero).trans rfl))
          subst index
          contradiction
        · have eq : index = sliceIndex := Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
            ((congrArg UniIndex.ofNat? one).trans rfl))
          subst index
          contradiction
        · have eq : index = outputIndex := Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
            ((congrArg UniIndex.ofNat? two).trans rfl))
          subst index
          contradiction
      · omega
    have member : tree.locations.entries[position] ∈ tree.locations.entries := Array.getElem_mem inside
    rcases rowCases member with source | output
    · rw [source]
      unfold sourceRow sourcePermissions UniValMap.get
      rw [Array.getElem?_eq_none (by change 2 ≤ index.toNat; omega)]
    · rw [output]
      unfold outputRow outputPermissions UniValMap.get
      rw [Array.getElem?_eq_none (by change 3 ≤ index.toNat; omega)]

theorem sliceRelease : ReleaseRange tree sliceIndex Size.ZERO 2 true := by
  refine ⟨fun _ => ⟨rootIndex,rfl⟩, by decide, ?_, ?_⟩
  · intro row member nonempty
    rcases rowCases member with rfl | rfl
    · decide
    · contradiction
  · intro index absent row member
    obtain ⟨position, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    exact availableKeys.rowVacant index absent position inside

/-- The inactive slice tag remains stored at the return byte. The release
contract based on all stored rows therefore cannot certify the same input. -/
theorem sliceReleaseRequiresAccessedRange : ¬ ReleaseRange tree sliceIndex Size.ZERO 2 := by
  intro release
  have member : outputRow ∈ tree.locations.entries := by
    change outputRow ∈ #[sourceRow, outputRow]
    simp
  have extent := release.materialized outputRow member (by decide)
  exact (by decide : ¬ 3 ≤ 0 + 2) extent.2

theorem outputRelease : ReleaseRange tree outputIndex (Size.ofBytes 2) 1 true := by
  refine ⟨fun _ => ⟨rootIndex,rfl⟩, by decide, ?_, ?_⟩
  · intro row member nonempty
    rcases rowCases member with rfl | rfl
    · contradiction
    · decide
  · intro index absent row member
    obtain ⟨position, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    exact availableKeys.rowVacant index absent position inside

theorem leafAncestor {i childIndex : UniIndex} {tag : BorTag}
    (present : tree.nodeAt childIndex = some (child tag))
    (path : Ancestor tree i childIndex) : i = childIndex ∨ i = rootIndex := by
  revert present
  induction path with
  | self index => intro _; exact Or.inl rfl
  | @parent _ lower root path data found edge ih =>
    intro present
    rcases ih present with rfl | rfl
    · rw [present] at found
      cases found
      exact Or.inr ((Option.some.inj edge).symm)
    · change some rootNode = some data at found
      cases found
      contradiction

theorem sourcePermission {index : UniIndex} {node : TreeNode} (present : tree.nodeAt index = some node)
    (protections : ProtectedTags) :
    ∃ current, tree.locationStateAt sourcePermissions index = some current ∧
      (Ancestor tree index sliceIndex → localOwns current (protections.contains node.tag)) ∧
      (¬Ancestor tree index sliceIndex → foreignCompatible current (protections.contains node.tag)) := by
  rcases lookupCases present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨parentPermission,rfl,fun _ => ⟨rfl,trivial⟩,
      fun absent => (absent (.parent (.self _) _ rfl rfl)).elim⟩
  · exact ⟨childPermission,rfl,fun _ => ⟨rfl,trivial⟩,fun absent => (absent (.self _)).elim⟩
  · refine ⟨_,rfl,?_,?_⟩
    · intro path
      rcases leafAncestor (tag := sliceTag) rfl path with out | out
      · exact (by decide : outputIndex ≠ sliceIndex) out |>.elim
      · exact (by decide : outputIndex ≠ rootIndex) out |>.elim
    · intro _
      exact ⟨rfl, Or.inr (Or.inr ⟨rfl,by decide⟩)⟩

theorem outputPermission {index : UniIndex} {node : TreeNode} (present : tree.nodeAt index = some node)
    (protections : ProtectedTags) :
    ∃ current, tree.locationStateAt outputPermissions index = some current ∧
      (Ancestor tree index outputIndex → localOwns current (protections.contains node.tag)) ∧
      (¬Ancestor tree index outputIndex → foreignCompatible current (protections.contains node.tag)) := by
  rcases lookupCases present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨parentPermission,rfl,fun _ => ⟨rfl,trivial⟩,
      fun absent => (absent (.parent (.self _) _ rfl rfl)).elim⟩
  · refine ⟨_,rfl,?_,?_⟩
    · intro path
      rcases leafAncestor (tag := outputTag) rfl path with out | out
      · exact (by decide : sliceIndex ≠ outputIndex) out |>.elim
      · exact (by decide : sliceIndex ≠ rootIndex) out |>.elim
    · intro _
      exact ⟨rfl, Or.inr (Or.inr ⟨rfl,by decide⟩)⟩
  · exact ⟨childPermission,rfl,fun _ => ⟨rfl,trivial⟩,fun absent => (absent (.self _)).elim⟩

#print axioms coherent
#print axioms availableKeys
#print axioms sliceRelease
#print axioms sliceReleaseRequiresAccessedRange
#print axioms outputRelease
#print axioms sourcePermission
#print axioms outputPermission
end DuplicatePrefix.SameAllocationWitness

import duplicate_prefix.AccessedCopyHolderRights
import duplicate_prefix.NonemptyReturnWatch

namespace DuplicatePrefix.AliasedCopyTree

open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins AccessedCopyHolderRights
open NonemptyReturnWatch Miri.Verification.RangeModifyLaw

set_option maxRecDepth 65536

/-- The actual adjacent copy leaves the independent output protector dormant
outside its original byte, and gives the same permission row at any byte
outside the slice. -/
theorem ancestor_from_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (watch source : UniIndex) (path : Ancestor {tree with locations} watch source) : Ancestor tree watch source := by
  induction path with
  | self => exact .self _
  | parent _ node known edge previous => exact .parent previous node known edge

theorem adjacent (tree : BorrowTree) (tag : BorTag) (source holder root : UniIndex)
    (tags : ProtectedTags) (offset : Size) (count length : UInt64)
    (canonical : count.toNat + count.toNat ≤ length.toNat)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (found : tree.indexOfTag tag = some source) (node : TreeNode) (known : tree.nodeAt source = some node)
    (lineage : Ancestor tree holder source)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index source → ¬ Ancestor tree index holder → tags.contains data.tag = false)
    (fits : offset.bytes.toNat+length.toNat ≤ tree.locations.size.bytes.toNat)
    (before : Footprint tree tags source holder offset.bytes (offset.bytes+length))
    (watch : UniIndex) (watchNode : TreeNode) (watchAt : tree.nodeAt watch = some watchNode)
    (foreign : ¬ Ancestor tree watch source) (outLo outHi : UInt64)
    (initial : AccessedWithin tree watch outLo outHi) :
    let read := tree.performBorrowAccessRange (.concrete tag) offset (Size.ofBytes count)
      .Read tags .VisitChildrenOfAccessed
    let written := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset.bytes+count))
      (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed
    AccessedWithin written.tree watch outLo outHi ∧ EachByte written.tree.locations (fun point row =>
      (point.toNat < offset.bytes.toNat ∨ offset.bytes.toNat+length.toNat ≤ point.toNat) →
      ValueAt tree.locations point row) := by
  let middle := offset.bytes+count
  let right := offset.bytes+length
  let read := tree.performBorrowAccessRange (.concrete tag) offset (Size.ofBytes count) .Read tags .VisitChildrenOfAccessed
  have first : offset.bytes.toNat+count.toNat ≤ tree.locations.size.bytes.toNat := by omega
  have midNat : middle.toNat = offset.bytes.toNat+count.toNat := by
    simp only [middle,UInt64.toNat_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt first tree.locations.size.bytes.toNat_lt)]
  have rightNat : right.toNat = offset.bytes.toNat+length.toNat := by
    simp only [right,UInt64.toNat_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt fits tree.locations.size.bytes.toNat_lt)]
  have selected1 : OwnedOn (fun row => LocationRights tree row tags source) offset.bytes middle tree.locations :=
    fun i hi good lo hi' => before.sourceRights i hi (by change offset.bytes.toNat < right.toNat; omega) (by change _ < right.toNat; omega) hi'
  let outside (point : UInt64) (row : LocationTree) :=
    (point.toNat < offset.bytes.toNat ∨ offset.bytes.toNat+length.toNat ≤ point.toNat) →
      ValueAt tree.locations point row
  have original : EachByte tree.locations (fun (point : UInt64) row =>
      (point.toNat < offset.bytes.toNat ∨ (offset.bytes+(Size.ofBytes count).bytes).toNat ≤ point.toNat) →
      outside point row) := by
    intro point pos valid lo hi _ _
    exact ⟨pos,valid,UInt64.le_iff_toNat_le.mp lo,UInt64.lt_iff_toNat_lt.mp hi,rfl⟩
  have readFrame := rangeKeepsWatch tree tags tag source watch root .Read offset (Size.ofBytes count)
    coherent roots node watchNode known watchAt found first
    (bounded_slots tree tags source root .Read offset (Size.ofBytes count) coherent node known roots first selected1)
    outLo outHi (.inl foreign) initial outside original
  obtain ⟨_,same,readCoherent,readSize,readOwned⟩ :=
    accessRange_retains_holder tree tags tag source holder root .Read offset (Size.ofBytes count) offset.bytes right
      coherent node known roots found lineage unheld first (Nat.le_refl _) (show middle.toNat ≤ right.toNat by omega) before
  change read.tree = {tree with locations := read.tree.locations} at same
  have second : middle.toNat+count.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [readSize]; omega
  have endNat : (middle+count).toNat = middle.toNat+count.toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt second read.tree.locations.size.bytes.toNat_lt)]
  have selected2 : OwnedOn (fun row => LocationRights read.tree row tags source) middle (middle+count) read.tree.locations :=
    by
      intro i hi good lo hi'
      change read.tree.locations.entries[i].range.start.toNat < (middle+count).toNat at lo
      change middle.toNat < read.tree.locations.entries[i].range.stop.toNat at hi'
      refine readOwned.sourceRights i hi (by omega) ?_ ?_
      · change read.tree.locations.entries[i].range.start.toNat < right.toNat
        omega
      · change offset.bytes.toNat < read.tree.locations.entries[i].range.stop.toNat
        omega
  have readRoots : read.tree.roots = #[root] := by rw [same]; exact roots
  have readFound : read.tree.indexOfTag tag = some source := by rw [same]; exact found
  have readKnown : read.tree.nodeAt source = some node := by rw [same]; exact known
  have readWatch : read.tree.nodeAt watch = some watchNode := by rw [same]; exact watchAt
  have readForeign : ¬ Ancestor read.tree watch source := by
    intro path
    apply foreign
    rw [same] at path
    exact ancestor_from_locations tree read.tree.locations watch source path
  have ready : EachByte read.tree.locations (fun (point : UInt64) row =>
      (point.toNat < (Size.ofBytes middle).bytes.toNat ∨
        ((Size.ofBytes middle).bytes+(Size.ofBytes count).bytes).toNat ≤ point.toNat) →
      outside point row) := by
    intro point pos valid lo hi _ condition
    apply readFrame.2.2.2.2.2 point pos valid lo hi _ condition
    change point.toNat < offset.bytes.toNat ∨ middle.toNat ≤ point.toNat
    omega
  have writeFrame := rangeKeepsWatch read.tree tags tag source watch root .Write (Size.ofBytes middle) (Size.ofBytes count)
    readCoherent readRoots node watchNode readKnown readWatch readFound second
    (bounded_slots read.tree tags source root .Write (Size.ofBytes middle) (Size.ofBytes count)
      readCoherent node readKnown readRoots second selected2)
    outLo outHi (.inl readForeign) readFrame.2.2.2.2.1 outside ready
  dsimp only
  refine ⟨writeFrame.2.2.2.2.1,?_⟩
  intro point position valid lo hi condition
  apply writeFrame.2.2.2.2.2 point position valid lo hi _ condition
  change point.toNat < middle.toNat ∨ (middle+count).toNat ≤ point.toNat
  omega

#print axioms adjacent
end DuplicatePrefix.AliasedCopyTree

import duplicate_prefix.SharedHolderRead
import duplicate_prefix.RetagReleaseFootprint

namespace DuplicatePrefix.ReleaseFromHolderRights

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open SourceDomain ArchiveForestProjection RetagReleaseRights RetagReleaseFootprint ActiveRelease
open GeneralBorrowExposure GeneralBorrowProjection BorrowRangeAccess
open GeneralRangeMapOrigins GeneralRangeMapState

set_option maxRecDepth 65536
set_option maxHeartbeats 1900000

private theorem row_owned (tree : BorrowTree) (child : UniIndex) (lower upper : UInt64)
    (coherent : CoherentForest tree) (materialized : MaterializedWithin tree child lower upper)
    (position : Nat) (inside : position < tree.locations.entries.size)
    (state : LocationState) (saved : tree.locations.entries[position].data.perms.get child = some state) :
    lower.toNat < upper.toNat ∧ tree.locations.entries[position].range.start.toNat < upper.toNat ∧
      lower.toNat < tree.locations.entries[position].range.stop.toNat := by
  let segment := tree.locations.entries[position]
  have nonempty : tree.locations.entries.size ≠ 0 := by omega
  have valid := coherent.ranges
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at valid
  have positive : segment.range.start < segment.range.stop := valid.2.1 position inside
  obtain ⟨lo, hi⟩ := materialized segment.range.start position inside
    (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) positive state saved
  exact ⟨Nat.lt_of_le_of_lt lo hi, hi, Nat.lt_of_le_of_lt lo (UInt64.lt_iff_toNat_lt.mp positive)⟩

/-- Convert a surviving mutable holder's structural range permission to the
per-slot authorization needed by its own active Return. -/
theorem releaseOwnership
    (tree : BorrowTree) (tags : ProtectedTags) (source root : UniIndex) (node : TreeNode)
    (found : tree.nodeAt source = some node)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (lower upper : UInt64) (extent : MaterializedWithin tree source lower upper) (vacant : VacantRows tree)
    (rights : OwnedOn (fun row => LocationRights tree row tags source) lower upper tree.locations) :
    ∀ position < tree.locations.entries.size, ∃ slot,
      tree.locations.index position = .ok slot ∧ ReleaseOwnership tree source root tags slot := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index data present parent edge
    obtain ⟨up, held⟩ := coherent.parentPresent index data parent present edge
    exact ⟨up, held, by first | exact decreases index data parent present edge | exact decreases index data parent edge⟩⟩
  have childData := forest_children tree coherent
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data present rootEdge
    simpa using (coherent.rootEdges index data present).mp rootEdge
  intro position inside
  let slot := tree.locations.entries[position]
  refine ⟨slot, index_exact _ _ inside, ?_⟩
  intro state kind saved _ _
  obtain ⟨positive, start, stop⟩ := row_owned tree source lower upper coherent extent position inside state saved
  have here := rights position inside positive start stop
  have own : LocationAccessRights tree slot.data tags source kind := by
    cases kind
    · exact LocationRights.readRights here
    · exact here
  let graph := forest tree slot.data tags coherent.indexFits depth childData
  have owner := normal_access_owned tree slot.data tags source kind depth node found coherent.indexFits
    (fun query absent => vacant query absent position inside) own
  let view := source_normal_projection tree slot.data tags
  let component : GeneralBorrowExposedScopedNormal.Component view.topology source.toNat :=
    ⟨fun _ => True, trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
  have path := GeneralBorrowTerminal.ancestor_root_present view.topology graph
    (GeneralBorrowGraph.Present tree) (GeneralBorrowGraph.parents_closed tree slot.data tags depth)
    source.toNat root.toNat owner.anchorValid ⟨source, node, rfl, found⟩
    (fun index _ => GeneralBorrowGraph.unique_root tree slot.data tags root roots covered index)
  refine ⟨graph, ⟨component, fun index _ bound => owner.permissions index bound⟩, ?_⟩
  rw [path]
  exact index_self root
#print axioms releaseOwnership
end DuplicatePrefix.ReleaseFromHolderRights

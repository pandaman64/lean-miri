import duplicate_prefix.CurrentSharedRetag
import duplicate_prefix.SharedHolderRead

namespace DuplicatePrefix.CurrentSharedRetag
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.DataStructures
open Miri.TreeBorrows.Tree
open ArchiveForestProjection SourceDomain GeneralRangeMapOrigins RetagSharedChild RetagReleaseFootprint

/-- The exact unprotected shared reference preserves its earlier mutable
holder's write grant and materialized scope in the resulting heap. -/
theorem Footprint.retainsHolder
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    {originalMemory : MemoryState Provenance BorrowTree MiriMemoryKind}
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (parentTag tag : BorTag) (parent root : UniIndex) (offset len : UInt64) (tags : ProtectedTags)
    (footprint : Footprint machine (originalMemory := originalMemory) entry id parentTag tag parent offset len tags)
    (node : TreeNode) (present : entry.allocation.extra.nodeAt parent = some node)
    (indexed : entry.allocation.extra.indexOfTag parentTag = some parent)
    (coherent : CoherentForest entry.allocation.extra) (roots : entry.allocation.extra.roots = #[root])
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (fresh : ∀ index data, entry.allocation.extra.nodeAt index = some data → data.tag ≠ tag)
    (unheld : tags.contains tag = false)
    (rights : OwnedOn (fun row => LocationRights entry.allocation.extra row tags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (materialized : MaterializedWithin entry.allocation.extra parent offset (offset+len))
    (vacant : VacantRows entry.allocation.extra) :
    let start := Size.ofBytes offset
    let length := Size.ofBytes len
    let original := entry.allocation.extra
    let read := original.performNormalAccessRange parentTag start length .Read tags .VisitChildrenOfAccessed
    let inside := DedupRangeMap.new length sharedState
    let after := (read.tree.newChild start (.concrete parentTag) tag inside .Frozen false).tree
    machine.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra after} ∧
      OwnedOn (fun row => LocationRights after row tags parent) offset (offset+len) after.locations ∧
      MaterializedWithin after parent offset (offset+len) ∧ VacantRows after ∧
      ∃ child, after.indexOfTag tag = some child ∧ SharedChildFrame original read.tree after parent child tag start length inside := by
  intro start length original read inside after
  obtain ⟨memory, child, selected, framed, _⟩ := footprint
  have readable : OwnedOn (fun row => LocationAccessRights original row tags parent .Read)
      offset (offset+len) original.locations := by
    intro i valid overlap left right
    exact LocationRights.readRights (rights i valid overlap left right)
  have writable : OwnedOn (fun row => LocationRights original row (tags.remove tag) parent)
      offset (offset+len) original.locations := by
    intro i valid overlap left right
    exact RetagReleaseRights.remove_preserves _ _ _ _ _ (rights i valid overlap left right)
  have around : OwnedOn (fun row => ∀ index, original.nodeAt index = none → row.perms.get index = none)
      offset (offset+len) original.locations := by
    intro i valid _ _ _ q absent
    exact vacant q absent i valid
  obtain ⟨_, _, _, _, writeRead, scopeRead⟩ :=
    SharedRelease.ranged_read_retains_holder_or_fresh original tags parentTag tag parent parent root node node
      present present indexed (.self parent) (Or.inr fresh)
      (fun _ _ _ path away => (away path).elim) (fun index data saved collision => (fresh index data saved collision).elim)
      coherent roots start length bounds readable writable around
  have oldPresent : read.tree.nodeAt parent = some node := by rw [framed.readMetadata]; exact present
  have different : parent ≠ child := by
    intro same
    have impossible : read.tree.nodeAt parent = none := same ▸ framed.attached.fresh
    rw [oldPresent] at impossible
    contradiction
  have protectorEq : ∀ i data, read.tree.nodeAt i = some data → tags.contains data.tag =
      (tags.remove tag).contains data.tag := by
    intro i data saved
    rw [framed.readMetadata] at saved
    exact (RetagReleaseRights.contains_remove_other tags tag data.tag (fresh i data saved)).symm
  have authorized := framed.holder parent (tags.remove tag) tags ⟨node, oldPresent⟩ unheld protectorEq writeRead
  have materialAfter := framed.holderMaterialization parent different offset (offset+len) (scopeRead parent materialized)
  have extent : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat := by
    intro segment member
    by_cases zero : length.bytes = 0
    · simp [inside, DedupRangeMap.new, DedupRangeMap.iterAll, zero] at member
    · simp [inside, DedupRangeMap.new, DedupRangeMap.iterAll, beq_iff_eq, zero] at member
      subst segment
      exact Nat.le_refl _
  exact ⟨memory, authorized, materialAfter, (framed.extent extent).2, child, selected, framed⟩

#print axioms Footprint.retainsHolder
end DuplicatePrefix.CurrentSharedRetag

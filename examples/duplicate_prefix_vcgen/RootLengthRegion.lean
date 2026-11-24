import RootLengthPrefix
import duplicate_prefix.ExclusiveTypedRetag
import duplicate_prefix.CopyHolderRights

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.MIR
open CanonicalConfigFacts PreparedArguments SourceDomain ArchiveForestProjection GeneralRangeMapOrigins MutableSliceRights

/-- Rebuild the initialized source and exclusive loan from the precise heap
returned by the length prefix. Physical byte and initialization fields come
from the original allocation witness. -/
theorem RootLengthState.sourceRegion
    {config : RootConfig} {older : Array CompilerFrameContext.ActualFrame}
    {outside initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : ActiveCaller older outside initialFrame initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthState config older outside initialFrame frame initial final root allocation offset len count tracker)
    (before : InitializedRegion (Storage.withCurrent (older.push outside) initialFrame initial) len)
    (sameId : before.id = root.id) (sameAllocation : before.entry = allocation)
    (sameStart : before.relativeStart.bytes = offset)
    (originalExtent : offset.toNat + len.toNat ≤ allocation.allocation.extra.locations.size.bytes.toNat)
    (initialKeys : RetagInsertionCapacity.Ready allocation.allocation.extra)
    (room : allocation.allocation.extra.nodes.size+2 < 2^32) :
    ∃ next : InitializedRegion (Storage.withCurrent (older.push outside) frame final) len,
      next.id = before.id ∧ next.relativeStart = before.relativeStart ∧ next.entry = post.branch.ready.entry ∧
      ∃ loan : ExclusiveRegion (Storage.withCurrent (older.push outside) frame final) len next post.branch.ready.tag,
        loan.source = post.branch.ready.source ∧ loan.tracker = post.branch.ready.tracker := by
  let after := Storage.withCurrent (older.push outside) frame final
  let tree := post.branch.ready.entry.allocation.extra
  let borrowing := post.branch.ready.tracker
  have live : after.machine.memory.live[before.id]? =
      some {before.entry with allocation := before.entry.allocation.setExtra tree} := by
    change final.memory.live[before.id]? = _
    rw [sameAllocation, sameId, ← post.branch.id]
    exact post.branch.ready.present.trans (congrArg some post.branch.allocationData)
  have preservedSize : before.relativeStart.bytes.toNat + len.toNat ≤ tree.locations.size.bytes.toNat := by
    change before.relativeStart.bytes.toNat + len.toNat ≤
      post.branch.ready.entry.allocation.extra.locations.size.bytes.toNat
    rw [sameStart, post.branch.rangeCapacity]
    exact originalExtent
  have keys := post.keys initialKeys room
  have tag := ready_tag_at tree keys post.branch.ready.source post.branch.ready.tag post.branch.ready.node
    post.branch.ready.indexed post.branch.ready.found
  have perByte (point : UInt64) (lower : offset.toNat ≤ point.toNat) (upper : point.toNat < (offset+len).toNat)
      (row : Miri.TreeBorrows.LocationTree) (located : ValueAt tree.locations point row) :
      LocationRights tree row borrowing.global.protectedTags post.branch.ready.source := by
    obtain ⟨position, valid, starts, stops, exact⟩ := located
    have starts' : post.branch.ready.entry.allocation.extra.locations.entries[position].range.start.toNat ≤ point.toNat := starts
    have stops' : point.toNat < post.branch.ready.entry.allocation.extra.locations.entries[position].range.stop.toNat := stops
    have owned := post.branch.writable position valid (by omega) (by omega) (by omega)
    have sameRow : post.branch.ready.entry.allocation.extra.locations.entries[position].data = row := exact
    rwa [sameRow] at owned
  obtain ⟨next, newId, newStart, nextEntry, ⟨loan⟩⟩ :=
    ExclusiveTypedRetag.region_from_cached_reborrow _ after len before tree post.branch.ready.tag
      post.branch.ready.source borrowing live post.branch.ready.tracked post.branch.coherence
      post.branch.ready.indexed ⟨post.branch.ready.node, post.branch.ready.found, tag⟩ preservedSize
      (fun point lower upper row located => by
        rw [sameStart] at lower upper
        intro index node present
        obtain ⟨current, value, write, foreign⟩ := perByte point lower upper row located index node present
        exact ⟨current, value, fun path => (localOwns_iff _ _).mp (write path),
          fun away => (foreignCompatible_iff _ _).mp (foreign away)⟩)
  have entryEq : next.entry = post.branch.ready.entry := by
    rw [nextEntry, sameAllocation, post.branch.allocationData]
  refine ⟨next, newId, newStart, entryEq, loan, ?_, ?_⟩
  · have recorded := loan.tagKnown
    rw [entryEq] at recorded
    exact Option.some.inj (recorded.symm.trans post.branch.ready.indexed)
  · exact Option.some.inj (loan.tracked.symm.trans post.branch.ready.tracked)

theorem RootLengthState.footprint
    {config : RootConfig} {older : Array CompilerFrameContext.ActualFrame}
    {outside initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : ActiveCaller older outside initialFrame initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthState config older outside initialFrame frame initial final root allocation offset len count tracker) :
    CopyHolderRights.Footprint post.branch.ready.entry.allocation.extra post.branch.ready.tracker.global.protectedTags
      post.branch.ready.source post.branch.ready.source offset (offset+len) :=
  ⟨post.branch.writable, post.branch.writable, post.branch.materialized, post.branch.vacant⟩

theorem RootLengthState.insertionCapacity
    {config : RootConfig} {older : Array CompilerFrameContext.ActualFrame}
    {outside initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : ActiveCaller older outside initialFrame initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthState config older outside initialFrame frame initial final root allocation offset len count tracker)
    (initialKeys : RetagInsertionCapacity.Ready allocation.allocation.extra)
    (room : allocation.allocation.extra.nodes.size+2 < 2^32) :
    CurrentTwoPhaseStructural.InsertionCapacity post.branch.ready.entry.allocation.extra post.branch.ready.source
      post.branch.ready.root post.branch.ready.tracker.global.nextPointerTag := by
  refine RetagInsertionCapacity.derive _ _ _ _ post.branch.coherence post.branch.ready.roots
    post.branch.ready.node post.branch.ready.found (post.keys initialKeys room) ?_
  intro index node found collision
  have age := post.tagAge index node found
  rw [collision] at age
  exact (Nat.lt_irrefl _) age

#print axioms RootLengthState.sourceRegion
#print axioms RootLengthState.footprint
end DuplicatePrefix.RootZeroShallowReturn

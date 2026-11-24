import CanonicalSourceControl
import CanonicalCallRelease
import RootZeroShallowReturn
import duplicate_prefix.ReleaseFromHolderRights

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows
open SourceDomain PreparedArguments ArchiveForestProjection GeneralRangeMapOrigins

/-- The exclusive slice grants imply ownership of every touched row. -/
theorem ExclusiveRegion.ownsRows {K U : Type} [DecidableEq K]
    {before : MachineHooks.State K U} {length : UInt64}
    {storage : InitializedRegion before length} {tag : BorTag}
    (region : ExclusiveRegion before length storage tag)
    (extent : ReleaseRange storage.entry.allocation.extra region.source storage.relativeStart length) :
    OwnedOn (fun row => LocationRights storage.entry.allocation.extra row region.tracker.global.protectedTags region.source)
      storage.relativeStart.bytes (storage.relativeStart.bytes + length) storage.entry.allocation.extra.locations := by
  let start := storage.relativeStart.bytes
  have fits : start.toNat + length.toNat < 2^64 :=
    Nat.lt_of_le_of_lt extent.extent storage.entry.allocation.extra.locations.size.bytes.toNat_lt
  have finish : (start + length).toNat = start.toNat + length.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  intro index valid positive lower upper
  let segment := storage.entry.allocation.extra.locations.entries[index]
  have member : segment ∈ storage.entry.allocation.extra.locations.entries :=
    Array.mem_iff_getElem.mpr ⟨index, valid, rfl⟩
  change start.toNat < (start + length).toNat at positive
  change segment.range.start.toNat < (start + length).toNat at lower
  change start.toNat < segment.range.stop.toNat at upper
  rw [finish] at positive lower
  let distance := segment.range.start.toNat - start.toNat
  have nonempty : storage.entry.allocation.extra.locations.entries.size ≠ 0 := by omega
  have formed := region.coherent.ranges
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at formed
  have ordered : segment.range.start.toNat < segment.range.stop.toNat :=
    UInt64.lt_iff_toNat_lt.mp (formed.2.1 index valid)
  exact region.exclusive distance (by dsimp [distance]; omega) segment member
    (by dsimp [distance, start] at *; omega) (by dsimp [distance, start] at *; omega)

/-- A nonempty admitted slice and its cached Boolean destination provide the
caller and active release facts used by the nested source return proof. -/
theorem Admitted.cachedActiveCaller
    {program options remaining headroom span before frame pointer length count}
    (admitted : Admitted program options remaining headroom span before frame pointer length count)
    (positive : length ≠ 0)
    (cached : CachedBoolDestination before frame)
    (ledger : ∃ owned, frame.extra.borrowTracker = some owned ∧ owned.protectedTags = argumentLedger pointer) :
    ∃ older caller, before.stack.frames = (older.push caller).push frame ∧
      Nonempty (RootZeroShallowReturn.ActiveCaller older caller frame before.machine) := by
  obtain ⟨older, caller, index, target, unwind, slot, value, stack, continuation, _, place,
    _, slotAt, slotLayout, live, clocks⟩ := cached.localSlot
  obtain ⟨valid, slotEqual⟩ := Array.getElem?_eq_some_iff.mp slotAt
  obtain ⟨storage, tag, _, region, borrowFrame, pointerEq, _, _, frameTracker, _, _, nodeWitness, extent⟩ :=
    admitted.sliceProtector positive
  obtain ⟨owned, ownedEq, actualLedger⟩ := ledger
  have sameFrame := Option.some.inj (ownedEq.symm.trans frameTracker)
  subst borrowFrame
  have singleton : owned.protectedTags = #[(storage.id, tag)] := by simp [actualLedger, argumentLedger, pointerEq]
  obtain ⟨node, found, hidden⟩ := nodeWitness
  obtain ⟨root, roots⟩ := extent.root positive
  obtain ⟨rank, bounded, decreases⟩ := region.coherent.parentDepth
  let depth : GeneralBorrowExposure.ParentDepth storage.entry.allocation.extra.nodes :=
    ⟨rank, bounded, by
      intro child childNode present parent relation
      obtain ⟨parentNode, parentPresent⟩ := region.coherent.parentPresent child childNode parent present relation
      exact ⟨parentNode, parentPresent, decreases child childNode parent present relation⟩⟩
  have children : GeneralBorrowGraph.ChildNodes storage.entry.allocation.extra := by
    intro query data present child member
    obtain ⟨childNode, childPresent, _⟩ :=
      (region.coherent.childEdges query data present).2.1 child (by simpa using member)
    exact ⟨childNode, childPresent⟩
  have authorized := ReleaseFromHolderRights.releaseOwnership storage.entry.allocation.extra
    region.tracker.global.protectedTags region.source root node found region.coherent roots
    storage.relativeStart.bytes (storage.relativeStart.bytes + length) extent.materializedWithin
    (fun _ missing _ inside => extent.vacantAt missing inside) (ExclusiveRegion.ownsRows region extent)
  obtain ⟨thread, active, _⟩ := admitted.stack.active
  have current : ∃ relevant,
      FrameRelevance.top ⟨(older.push caller).push frame⟩ thread.topUserRelevantFrame = some relevant := by
    cases thread.topUserRelevantFrame with
    | some value => exact ⟨value, by simp [FrameRelevance.top]⟩
    | none => exact ⟨older.size + 1, by simp [FrameRelevance.top]⟩
  obtain ⟨relevant, relevance⟩ := current
  refine ⟨older, caller, stack, ⟨{
    target := target
    unwind := unwind
    continuation := continuation
    destinationIndex := index
    destinationBound := valid
    destinationSlot := value
    destinationLive := by rw [slotEqual]; exact live
    destinationCached := by rw [slotEqual]; exact slotLayout
    destination := place
    callerClocks := clocks
    varargs := admitted.stack.noVarargs
    id := storage.id
    tag := tag
    entry := storage.entry
    present := storage.live
    tracker := region.tracker
    tracked := region.tracked
    owned := owned
    ownership := ownedEq
    ownedTags := singleton
    source := region.source
    root := root
    indexed := region.tagKnown
    roots := roots
    depth := depth
    children := children
    node := node
    found := found
    unexposed := hidden
    authorized := authorized
    thread := thread
    relevant := relevant
    active := active
    relevance := relevance }⟩⟩

/-- The cached return carrier owns no output protector. For an empty slice
the complete ordered release therefore preserves live memory. -/
theorem Admitted.emptyCachedRelease
    {program options remaining headroom span before frame pointer count}
    (admitted : Admitted program options remaining headroom span before frame pointer 0 count)
    (ledger : ∃ owned, frame.extra.borrowTracker = some owned ∧ owned.protectedTags = argumentLedger pointer) :
    ∃ tracker owned,
      before.machine.borrowTracker = some tracker ∧ frame.extra.borrowTracker = some owned ∧
      StackPopRelease.Plan tracker.global.protectedTags owned.protectedTags.toList
        before.machine.memory before.machine.memory := by
  obtain ⟨tracker, _, tracked, _⟩ := admitted.allocations.ledger
  obtain ⟨owned, frameTracker, protectorRows⟩ := ledger
  refine ⟨tracker, owned, tracked, frameTracker, ?_⟩
  simpa [protectorRows] using admitted.prependEmptyArgumentRelease tracker.global.protectedTags
    (.nil before.machine.memory)

#print axioms ExclusiveRegion.ownsRows
#print axioms Admitted.cachedActiveCaller
#print axioms Admitted.emptyCachedRelease
end DuplicatePrefix.CanonicalCallDomain

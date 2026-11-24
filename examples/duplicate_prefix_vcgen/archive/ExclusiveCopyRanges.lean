import Miri.Verification.RangeModifyLaw
import duplicate_prefix.ExclusiveConcreteRange
import duplicate_prefix.GeneralRangeMapState

namespace DuplicatePrefix.ArchiveForestProjection

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification.RangeModifyLaw
open Miri.Verification
open GeneralRangeMapState GeneralRangeMapOrigins SourceDomain PreparedArguments

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem replaced_preserves (predicate : A → Prop) (lower upper : UInt64)
    (map : DedupRangeMap A) (position : Nat) (valid : position < map.entries.size) (data : A)
    (updated : lower.toNat < upper.toNat →
      map.entries[position].range.start.toNat < upper.toNat →
      lower.toNat < map.entries[position].range.stop.toNat → predicate data)
    (owned : OwnedOn predicate lower upper map) :
    OwnedOn predicate lower upper (replaced map position valid data) := by
  intro index inside positive start stop
  have original : index < map.entries.size := by simpa only [replaced_length] using inside
  rw [replaced_range map position valid data index original] at start stop
  by_cases same : position = index
  · subst index
    simpa [replaced] using updated positive start stop
  · have prior := owned index original positive start stop
    simpa [replaced, Array.getElem_set, same] using prior

private theorem preserves_loop {A S : Type} (positions : List A)
    (step : A → S → Id (ForInStep S)) (ok : S → Prop)
    (preserves : ∀ i ∈ positions, ∀ current, ok current →
      ∃ updated, step i current = .yield updated ∧ ok updated)
    (initial : S) (ready : ok initial) :
    ok (forIn positions initial step : Id S) := by
  induction positions generalizing initial with
  | nil => exact ready
  | cons head tail inductionHyp =>
    obtain ⟨updated, run, valid⟩ := preserves head (by simp) initial ready
    rw [List.forIn_cons, run]
    change ok (forIn tail updated step : Id S)
    exact inductionHyp (fun i member => preserves i (.tail _ member)) updated valid

theorem replace_each_byte (property : UInt64 → LocationTree → Prop)
    (table : DedupRangeMap LocationTree) (position : Nat) (inside : position < table.entries.size)
    (next : LocationTree) (before : EachByte table property)
    (keeps : ∀ point, table.entries[position].range.start ≤ point → point < table.entries[position].range.stop →
      property point next) : EachByte (replaced table position inside next) property := by
  intro point index bounded lo hi
  have actual : index < table.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range table position inside next index actual] at lo hi
  by_cases equal : position = index
  · subst index
    simpa [replaced] using keeps point lo hi
  · simpa [replaced, Array.getElem_set, equal] using before point index actual lo hi

/-- An interval-local invariant survives range preparation and actual access
updates when the selected byte transitions preserve its predicate. -/
theorem preserve_range_property_with_byte_frame (tree : BorrowTree) (tag : BorTag) (source : UniIndex)
    (protectors : ProtectedTags) (kind : AccessKind) (mode : ChildrenVisitMode)
    (offset length : Size) (lower upper : UInt64) (predicate : LocationTree → Prop)
    (found : tree.indexOfTag tag = some source) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (ownership : OwnedOn predicate lower upper tree.locations)
    (stable : ∀ segment : RangeMapSegment LocationTree,
      segment.range.stop.toNat ≤ (offset.bytes + length.bytes).toNat →
      lower.toNat < upper.toNat → segment.range.start.toNat < upper.toNat →
      lower.toNat < segment.range.stop.toNat → predicate segment.data →
      predicate (tree.performTreeAccessAt segment.data (some source) kind protectors mode segment.range).location)
    (byteProperty : UInt64 → LocationTree → Prop)
    (byteFrame : EachByte tree.locations byteProperty)
    (byteStable : ∀ (segment : RangeMapSegment LocationTree) (point : UInt64),
      offset.bytes.toNat ≤ point.toNat → point.toNat < (offset.bytes + length.bytes).toNat →
      segment.range.start ≤ point → point < segment.range.stop → byteProperty point segment.data →
      byteProperty point (tree.performTreeAccessAt segment.data (some source) kind protectors mode segment.range).location)
    (authorized : TreeRangeAccess.SlotsAuthorized tree (tree.locations.iterMut offset length)
      (some source) kind protectors mode) :
    let run := tree.performBorrowAccessRange (.concrete tag) offset length kind protectors mode
    run.status = .Completed ∧ OwnedOn predicate lower upper run.tree.locations ∧
      run.tree.locations.WellFormed ∧ run.tree.locations.size = tree.locations.size ∧
      run.tree = {tree with locations := run.tree.locations} ∧ EachByte run.tree.locations byteProperty := by
  let prepared := tree.locations.iterMut offset length
  have info := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset length well bounds
  have initialOwned := refines_owned_on tree.locations prepared.state predicate lower upper
    info.1.wellFormed info.2.1 ownership
  have initialByte : EachByte prepared.state byteProperty := by
    intro point position valid lo hi
    obtain ⟨prior, bounded, start, stop, same⟩ := info.2.1 point prepared.state.entries[position].data
      ⟨position, valid, UInt64.le_iff_toNat_le.mp lo, UInt64.lt_iff_toNat_lt.mp hi, rfl⟩
    exact same ▸ byteFrame point prior bounded (UInt64.le_iff_toNat_le.mpr start) (UInt64.lt_iff_toNat_lt.mpr stop)
  let ok (current : BorrowTree.RangeVerification.Progress) : Prop :=
    current.2.2 = .Completed ∧
      current.1.entries.size = prepared.state.entries.size ∧
      current.1.entries.map (·.range) = prepared.state.entries.map (·.range) ∧
      OwnedOn predicate lower upper current.1 ∧
      current.1.WellFormed ∧ current.1.size = tree.locations.size ∧ EachByte current.1 byteProperty
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ current, ok current →
      ∃ next, (pure (ForInStep.yield (BorrowTree.RangeVerification.advance tree prepared
        (some source) kind protectors mode cursor current)) : Id _) = .yield next ∧ ok next := by
    intro cursor member current valid
    have inside : cursor < prepared.positions.size := by simpa [List.mem_range'] using member
    rcases current with ⟨table, visited, status⟩
    rcases valid with ⟨currentStatus, currentSize, currentRanges, currentOwned, currentWell, currentCapacity, currentByte⟩
    dsimp only at currentStatus currentSize currentRanges currentOwned currentWell currentCapacity currentByte
    subst status
    obtain ⟨position, segment, pos, slot, bounded, completed⟩ := authorized cursor inside
    change prepared.positions[cursor]? = some position at pos
    change prepared.segments[cursor]? = some segment at slot
    change position < prepared.state.entries.size at bounded
    have inTable : position < table.entries.size := by rwa [currentSize]
    have inSegments : cursor < prepared.segments.size := (Array.getElem?_eq_some_iff.mp slot).1
    have exactPosition : prepared.positions[cursor] = position := (Array.getElem?_eq_some_iff.mp pos).2
    have segmentExact : prepared.segments[cursor] = segment := (Array.getElem?_eq_some_iff.mp slot).2
    obtain ⟨storedBound, selected⟩ := info.1.selected cursor inside
    change prepared.segments[cursor]'inSegments = prepared.state.entries[prepared.positions[cursor]]'storedBound at selected
    have stored : prepared.state.entries[position] = segment := by
      simpa only [exactPosition, segmentExact] using selected.symm
    have sameRange : table.entries[position].range = segment.range := by
      have eq := congrArg (fun arr : Array ByteRange => arr[position]?) currentRanges
      have lookup : prepared.state.entries[position]? = some segment :=
        (Array.getElem?_eq_getElem bounded).trans (congrArg some stored)
      simpa only [Array.getElem?_map, Array.getElem?_eq_getElem inTable,
        lookup, Option.map_some, Option.some.injEq] using eq
    have selectedBounds := info.2.2 cursor inSegments
    rw [segmentExact] at selectedBounds
    have updateKeeps : lower.toNat < upper.toNat →
        table.entries[position].range.start.toNat < upper.toNat →
        lower.toNat < table.entries[position].range.stop.toNat →
        predicate (tree.performTreeAccessAt segment.data (some source) kind protectors mode segment.range).location := by
      rw [sameRange]
      intro positive start stop
      have before : predicate prepared.state.entries[position].data := by
        apply initialOwned position bounded positive <;> simpa only [stored] using ‹_›
      have owned : predicate segment.data := by simpa only [stored] using before
      exact stable segment selectedBounds.2 positive start stop owned
    have updatedByte : ∀ point, table.entries[position].range.start ≤ point → point < table.entries[position].range.stop →
        byteProperty point (tree.performTreeAccessAt segment.data (some source) kind protectors mode segment.range).location := by
      rw [sameRange]
      intro point start stop
      have prior := initialByte point position bounded (by simpa only [stored] using start)
        (by simpa only [stored] using stop)
      exact byteStable segment point
        (Nat.le_trans selectedBounds.1 (UInt64.le_iff_toNat_le.mp start))
        (Nat.lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp stop) selectedBounds.2)
        start stop (by simpa only [stored] using prior)
    have mutations := setAtPos_exact table position inTable
      (tree.performTreeAccessAt segment.data (some source) kind protectors mode segment.range).location
    refine ⟨_, rfl, ?_⟩
    simp only [BorrowTree.RangeVerification.advance, beq_self_eq_true, ↓reduceIte, pos, slot, mutations,
      completed, Option.getD_none, ok]
    exact ⟨True.intro, (replaced_length table position inTable _).trans currentSize,
      (replaced_ranges table position inTable _).trans currentRanges,
      replaced_preserves predicate lower upper table position inTable _ updateKeeps currentOwned,
      replaced_wellFormed table position inTable _ currentWell,
      (replaced_size table position inTable _).trans currentCapacity,
      replace_each_byte byteProperty table position inTable _ currentByte updatedByte⟩
  have initial : ok (prepared.state, #[], .Completed) :=
    ⟨rfl, rfl, rfl, initialOwned, info.1.wellFormed, congrArg Size.ofBytes info.1.capacity, initialByte⟩
  have final := preserves_loop (List.range' 0 prepared.positions.size)
    (fun cursor current => pure (.yield (BorrowTree.RangeVerification.advance tree prepared
        (some source) kind protectors mode cursor current))) ok step _ initial
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  simp only [Id.run, found, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, info.1.outcome,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, BorrowTree.RangeVerification.cursor_equation]
  exact ⟨final.1, final.2.2.2.1, final.2.2.2.2.1, final.2.2.2.2.2.1, rfl, final.2.2.2.2.2.2⟩

theorem preserve_range_property (tree : BorrowTree) (tag : BorTag) (source : UniIndex)
    (protectors : ProtectedTags) (kind : AccessKind) (mode : ChildrenVisitMode)
    (offset length : Size) (lower upper : UInt64) (predicate : LocationTree → Prop)
    (found : tree.indexOfTag tag = some source) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (ownership : OwnedOn predicate lower upper tree.locations)
    (stable : ∀ segment : RangeMapSegment LocationTree,
      segment.range.stop.toNat ≤ (offset.bytes + length.bytes).toNat →
      lower.toNat < upper.toNat → segment.range.start.toNat < upper.toNat →
      lower.toNat < segment.range.stop.toNat → predicate segment.data →
      predicate (tree.performTreeAccessAt segment.data (some source) kind protectors mode segment.range).location)
    (authorized : TreeRangeAccess.SlotsAuthorized tree (tree.locations.iterMut offset length)
      (some source) kind protectors mode) :
    let run := tree.performBorrowAccessRange (.concrete tag) offset length kind protectors mode
    run.status = .Completed ∧ OwnedOn predicate lower upper run.tree.locations ∧
      run.tree.locations.WellFormed ∧ run.tree.locations.size = tree.locations.size ∧
      run.tree = {tree with locations := run.tree.locations} := by
  have checked := preserve_range_property_with_byte_frame tree tag source protectors kind mode offset length
    lower upper predicate found well bounds ownership stable (fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) authorized
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1, checked.2.2.2.2.1⟩

/-- The actual access leaves source-independent ownership at later bytes. -/
theorem preserve_after_range (tree : BorrowTree) (tag : BorTag) (source : UniIndex)
    (protectors : ProtectedTags) (kind : AccessKind) (mode : ChildrenVisitMode)
    (offset length : Size) (lower upper : UInt64) (predicate : LocationTree → Prop)
    (found : tree.indexOfTag tag = some source) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (disjoint : (offset.bytes + length.bytes).toNat ≤ lower.toNat)
    (ownership : OwnedOn predicate lower upper tree.locations)
    (authorized : TreeRangeAccess.SlotsAuthorized tree (tree.locations.iterMut offset length)
      (some source) kind protectors mode) :
    let run := tree.performBorrowAccessRange (.concrete tag) offset length kind protectors mode
    run.status = .Completed ∧ OwnedOn predicate lower upper run.tree.locations ∧
      run.tree.locations.WellFormed ∧ run.tree.locations.size = tree.locations.size ∧
      run.tree = {tree with locations := run.tree.locations} := by
  apply preserve_range_property tree tag source protectors kind mode offset length lower upper predicate
    found well bounds ownership _ authorized
  intro segment selectedStop _ _ intersects _
  omega

private theorem ancestor_transport {before after : BorrowTree}
    (same : before.nodes = after.nodes) {root source : UniIndex}
    (path : Ancestor before root source) : Ancestor after root source := by
  induction path with
  | self => exact .self _
  | parent _ node found edge ih =>
    exact .parent ih node (by simpa only [BorrowTree.nodeAt, ← same] using found) edge

private theorem rights_transport {before after : BorrowTree}
    (same : before.nodes = after.nodes) (location : LocationTree) (protections : ProtectedTags)
    (source : UniIndex) (rights : LocationRights before location protections source) :
    LocationRights after location protections source := by
  intro index node found
  have original : before.nodeAt index = some node := by
    simpa only [BorrowTree.nodeAt, same] using found
  obtain ⟨state, stateFound, localUse, foreignUse⟩ := rights index node original
  refine ⟨state, ?_, fun path => localUse (ancestor_transport same.symm path),
    fun unrelated => foreignUse (fun path => unrelated (ancestor_transport same path))⟩
  simpa only [BorrowTree.locationStateAt, BorrowTree.nodeAt, ← same] using stateFound

/-- Actual source read and adjacent destination write complete for every
bounded count in the prepared slice's single-root allocation. The write
inherits ownership from the original caller's data across the read. -/
theorem exclusive_copy_permissions {K U : Type} {before : MachineHooks.State K U}
    {sliceLength : UInt64} (storage : InitializedRegion before sliceLength)
    {tag : BorTag} (exclusive : ExclusiveRegion before sliceLength storage tag)
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (count : UInt64) (within : count.toNat + count.toNat ≤ sliceLength.toNat)
    (capacity : storage.relativeStart.bytes.toNat + sliceLength.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat) :
    let tree := storage.entry.allocation.extra
    let protections := exclusive.tracker.global.protectedTags
    let read := tree.performBorrowAccessRange (.concrete tag) storage.relativeStart
      (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (storage.relativeStart.bytes + count))
      (Size.ofBytes count) .Write protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed := by
  let tree := storage.entry.allocation.extra
  let protections := exclusive.tracker.global.protectedTags
  let offset := storage.relativeStart
  let stop := offset.bytes + count
  let endWrite := stop + count
  have firstBound : offset.bytes.toNat + count.toNat ≤ tree.locations.size.bytes.toNat := by
    change offset.bytes.toNat + sliceLength.toNat ≤ tree.locations.size.bytes.toNat at capacity
    omega
  have firstFits := Nat.lt_of_le_of_lt firstBound (UInt64.toNat_lt _)
  have stopNat : stop.toNat = offset.bytes.toNat + count.toNat := by
    simp only [stop, UInt64.toNat_add, Nat.mod_eq_of_lt firstFits]
  have secondBound : stop.toNat + count.toNat ≤ tree.locations.size.bytes.toNat := by
    change offset.bytes.toNat + sliceLength.toNat ≤ tree.locations.size.bytes.toNat at capacity
    omega
  have secondFits := Nat.lt_of_le_of_lt secondBound (UInt64.toNat_lt _)
  have endNat : endWrite.toNat = stop.toNat + count.toNat := by
    simp only [endWrite, UInt64.toNat_add, Nat.mod_eq_of_lt secondFits]
  obtain ⟨node, sourcePresent, _⟩ := exclusive.sourcePresent
  have readRights := exclusive_subrange storage exclusive offset.bytes stop (Nat.le_refl _)
    (by change _ ≤ offset.bytes.toNat + sliceLength.toNat; omega)
  have writeRights := exclusive_subrange storage exclusive stop endWrite
    (by change offset.bytes.toNat ≤ _; omega)
    (by change _ ≤ offset.bytes.toNat + sliceLength.toNat; omega)
  have canRead := bounded_slots tree protections exclusive.source root .Read offset (Size.ofBytes count)
    exclusive.coherent node sourcePresent roots firstBound readRights
  have first := preserve_after_range tree tag exclusive.source protections .Read .VisitChildrenOfAccessed
    offset (Size.ofBytes count) stop endWrite
    (fun location => LocationRights tree location protections exclusive.source)
    exclusive.tagKnown exclusive.coherent.ranges firstBound (Nat.le_refl _) writeRights canRead
  let read := tree.performBorrowAccessRange (.concrete tag) offset (Size.ofBytes count)
    .Read protections .VisitChildrenOfAccessed
  change read.status = .Completed ∧ _
  refine ⟨first.1, ?_⟩
  have frame : read.tree = {tree with locations := read.tree.locations} := first.2.2.2.2
  have coherent : CoherentForest read.tree := by
    rw [frame]
    exact {exclusive.coherent with ranges := first.2.2.1}
  have same : tree.nodes = read.tree.nodes := by
    rw [frame]
  have presentAfter : read.tree.nodeAt exclusive.source = some node := by
    exact (congrArg (fun t : BorrowTree => t.nodeAt exclusive.source) frame).trans sourcePresent
  have rootsAfter : read.tree.roots = #[root] := by
    exact (congrArg BorrowTree.roots frame).trans roots
  have tagAfter : read.tree.indexOfTag tag = some exclusive.source := by
    exact (congrArg (fun t : BorrowTree => t.indexOfTag tag) frame).trans exclusive.tagKnown
  have ownersAfter : OwnedOn (fun location => LocationRights read.tree location protections exclusive.source)
      stop endWrite read.tree.locations := by
    intro position valid positive segmentStart segmentStop
    exact rights_transport same _ _ _ (first.2.1 position valid positive segmentStart segmentStop)
  apply bounded_range read.tree protections tag exclusive.source root .Write (Size.ofBytes stop)
    (Size.ofBytes count) coherent node presentAfter rootsAfter tagAfter
  · rw [first.2.2.2.1]
    exact secondBound
  · exact ownersAfter

#print axioms preserve_after_range
#print axioms exclusive_copy_permissions
end DuplicatePrefix.ArchiveForestProjection

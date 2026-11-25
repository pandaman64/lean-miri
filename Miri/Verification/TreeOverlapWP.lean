import Miri.Verification.TreeRangeCursorsWP
import Miri.Verification.TreeWildcardPairWP

/-! Byte-local checks for the safety of a read followed by a write. -/
namespace Miri.Verification.TreeOverlapWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree TreeRangeAccess
open BorrowTree.RangeVerification

private def source (tree : BorrowTree) : ProvenanceExtra → Option UniIndex
  | .concrete tag => tree.indexOfTag tag
  | .wildcard => none

private def resolved (tree : BorrowTree) (provenance : ProvenanceExtra) : Prop :=
  match provenance with
  | .concrete _ => (source tree provenance).isSome = true
  | .wildcard => True

/-- Run the local access with diagnostic bounds fixed. The actual byte range
only decorates errors, so success and successful location updates agree. -/
private def localAccess (tree : BorrowTree) (location : LocationTree) (provenance : ProvenanceExtra)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    TreeLocationAccessAtResult :=
  tree.performTreeAccessAt location (source tree provenance) kind tags mode ⟨0, 0⟩

private def runtimeReadWritePre (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readRange writeRange : ByteRange) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) : Prop :=
  resolved tree reader ∧ resolved tree writer ∧
    (∀ byte initial, tree.locations.MapAt byte initial → readRange.Contains byte →
      (localAccess tree initial reader .Read readTags readMode).status.getD .Completed = .Completed) ∧
    (∀ byte initial, tree.locations.MapAt byte initial → writeRange.Contains byte →
      (readRange.Contains byte →
        (localAccess tree (localAccess tree initial reader .Read readTags readMode).location
          writer .Write writeTags writeMode).status.getD .Completed = .Completed) ∧
      (¬ readRange.Contains byte →
        (localAccess tree initial writer .Write writeTags writeMode).status.getD .Completed = .Completed))

/-- Check the local permission and cache rules, retaining the resulting
location only on a successful transition. -/
def localPre (tree : BorrowTree) (location : LocationTree) (provenance : ProvenanceExtra)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : LocationTree → Prop) : Prop :=
  RangeVerification.locationContract tree location (source tree provenance) kind tags mode ⟨0, 0⟩
    (fun result => result.status.getD .Completed = .Completed ∧ post result.location)

/-- A wildcard byte access can use the direct initial-forest checks,
including all ordered roots and their permission and cache updates. -/
theorem localPre_wildcard_iff (tree : BorrowTree) (location : LocationTree)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : LocationTree → Prop) :
    localPre tree location .wildcard kind tags mode post ↔
      TreeWildcardPairWP.rootsPre tree kind tags post (List.range' 0 tree.roots.size) location := by
  unfold localPre
  rw [show (fun result : TreeLocationAccessAtResult =>
        result.status.getD .Completed = .Completed ∧ post result.location) =
      (fun result : TreeLocationAccessAtResult =>
        post result.location ∧ result.status.getD .Completed = .Completed) from
    funext fun _ => propext and_comm]
  exact TreeWildcardPairWP.completedLocation_iff tree location kind tags mode ⟨0, 0⟩ (fun result => post result.location)

private theorem localPre_iff (tree : BorrowTree) (location : LocationTree) (provenance : ProvenanceExtra)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (post : LocationTree → Prop) :
    localPre tree location provenance kind tags mode post ↔
      (localAccess tree location provenance kind tags mode).status.getD .Completed = .Completed ∧
        post (localAccess tree location provenance kind tags mode).location :=
  (RangeVerification.locationContract_iff tree location (source tree provenance) kind tags mode
    ⟨0, 0⟩ (fun result => result.status.getD .Completed = .Completed ∧ post result.location)).symm

/-- Initial byte locations supply the local read and write permission
contracts. On overlap, the writer consumes the local read's successful
permission and cache state. On write-only bytes it starts at the initial value. -/
def readWritePre (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readRange writeRange : ByteRange) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) : Prop :=
  resolved tree reader ∧ resolved tree writer ∧
    (∀ byte initial, tree.locations.MapAt byte initial → readRange.Contains byte →
      localPre tree initial reader .Read readTags readMode (fun _ => True)) ∧
    (∀ byte initial, tree.locations.MapAt byte initial → writeRange.Contains byte →
      (readRange.Contains byte → localPre tree initial reader .Read readTags readMode
        (fun updated => localPre tree updated writer .Write writeTags writeMode (fun _ => True))) ∧
      (¬ readRange.Contains byte → localPre tree initial writer .Write writeTags writeMode (fun _ => True)))

private theorem readWritePre_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readRange writeRange : ByteRange) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) :
    readWritePre tree reader writer readRange writeRange readTags writeTags readMode writeMode ↔
      runtimeReadWritePre tree reader writer readRange writeRange readTags writeTags readMode writeMode := by
  simp only [readWritePre, runtimeReadWritePre, localPre_iff, and_true]
  constructor
  · rintro ⟨readerResolved, writerResolved, reads, writes⟩
    exact ⟨readerResolved, writerResolved, reads, fun byte initial found inside =>
      ⟨fun overlap => ((writes byte initial found inside).1 overlap).2, (writes byte initial found inside).2⟩⟩
  · rintro ⟨readerResolved, writerResolved, reads, writes⟩
    exact ⟨readerResolved, writerResolved, reads, fun byte initial found inside =>
      ⟨fun overlap => ⟨reads byte initial found overlap, (writes byte initial found inside).1 overlap⟩,
        (writes byte initial found inside).2⟩⟩

private theorem slots_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (prepared : IterMutResult LocationTree) (range : ByteRange)
    (contents : UInt64 → LocationTree → Prop)
    (geometry : prepared.PreparedFor range contents)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    (∀ cursor, cursor < prepared.positions.size →
      SlotAuthorized tree prepared (source tree provenance) kind tags mode cursor) ↔
    ∀ byte data, contents byte data → range.Contains byte →
      (localAccess tree data provenance kind tags mode).status.getD .Completed = .Completed := by
  have localSlot (segment : RangeMapSegment LocationTree) :
      RangeVerification.locationContract tree segment.data (source tree provenance) kind tags mode
        segment.range (fun result => result.status.getD .Completed = .Completed) ↔
      (localAccess tree segment.data provenance kind tags mode).status.getD .Completed = .Completed := by
    rw [← RangeVerification.locationContract_iff]
    simpa only [localAccess, and_true] using
      RangeVerification.location_success_range_irrelevant tree segment.data (source tree provenance)
        kind tags mode segment.range ⟨0, 0⟩ (fun _ => True)
  constructor
  · intro allowed byte data content included
    obtain ⟨position, segment, entry, covers, rfl⟩ := (geometry.partition byte data).mpr content
    obtain ⟨cursor, inside, selected⟩ := geometry.coverage position segment byte entry covers included
    obtain ⟨position', segment', positionAt, segmentAt, backing, _, _⟩ := geometry.slot cursor inside
    obtain ⟨_, actual, _, actualSegment, _, check⟩ := allowed cursor inside
    have samePosition := Option.some.inj (positionAt.symm.trans selected)
    subst position'
    have sameSegment := Option.some.inj (backing.symm.trans entry)
    subst segment'
    have sameActual := Option.some.inj (actualSegment.symm.trans segmentAt)
    subst actual
    exact (localSlot segment).mp check
  · intro allowed cursor inside
    obtain ⟨position, segment, positionAt, segmentAt, entry, ⟨byte, covers⟩, within⟩ :=
      geometry.slot cursor inside
    exact ⟨position, segment, positionAt, segmentAt, (Array.getElem?_eq_some_iff.mp entry).choose,
      (localSlot segment).mpr
        (allowed byte segment.data ((geometry.partition byte segment.data).mp
          ⟨position, segment, entry, covers, rfl⟩) (within byte covers))⟩

private def retainedAccess (tree : BorrowTree) (provenance : ProvenanceExtra) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (prepared : IterMutResult LocationTree)
    (cursor : Nat) : TreeLocationAccessAtResult :=
  match prepared.segments[cursor]? with
  | none => ⟨default, none, none⟩
  | some segment =>
    tree.performTreeAccessAt segment.data (source tree provenance) kind tags mode segment.range

private theorem retained_iff (tree : BorrowTree) (provenance : ProvenanceExtra) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (prepared : IterMutResult LocationTree)
    (cursor : Nat) (result : TreeLocationAccessAtResult) :
    SnapshotAuthorized tree prepared (source tree provenance) kind tags mode cursor result ↔
    SlotAuthorized tree prepared (source tree provenance) kind tags mode cursor ∧
      retainedAccess tree provenance kind tags mode prepared cursor = result := by
  unfold SnapshotAuthorized SlotAuthorized
  simp only [← RangeVerification.locationContract_iff]
  constructor
  · rintro ⟨position, segment, atPosition, atSegment, bounded, equal, complete⟩
    exact ⟨⟨position, segment, atPosition, atSegment, bounded, complete⟩,
      by simpa only [retainedAccess, atSegment] using equal⟩
  · rintro ⟨⟨position, segment, atPosition, atSegment, bounded, complete⟩, equal⟩
    exact ⟨position, segment, atPosition, atSegment, bounded,
      by simpa only [retainedAccess, atSegment] using equal, complete⟩

private theorem accessLocations_entry (tree : BorrowTree) (provenance : ProvenanceExtra) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (prepared : IterMutResult LocationTree)
    (range : ByteRange) (contents : UInt64 → LocationTree → Prop)
    (geometry : prepared.PreparedFor range contents)
    (authorized : ∀ cursor, cursor < prepared.positions.size →
      SlotAuthorized tree prepared (source tree provenance) kind tags mode cursor)
    (position : Nat) (segment : RangeMapSegment LocationTree)
    (entry : prepared.state.entries[position]? = some segment)
    (byte : UInt64) (covered : segment.range.Contains byte) :
    (TreeRangePointwiseWP.readLocations prepared (retainedAccess tree provenance kind tags mode prepared)).entries[position]? =
      some { segment with data :=
        if range.start ≤ byte ∧ byte < range.stop then
          (localAccess tree segment.data provenance kind tags mode).location else segment.data } := by
  classical
  let retained := retainedAccess tree provenance kind tags mode prepared
  let cursors := (List.range' 0 prepared.positions.size).reverse
  let find := cursors.findSome? (snapshotLocationAt prepared retained position)
  have inCursor (cursor : Nat) : cursor ∈ cursors ↔ cursor < prepared.positions.size := by
    simp [cursors, List.mem_range']
  have evaluate (cursor : Nat) (member : cursor ∈ cursors) :
      snapshotLocationAt prepared retained position cursor =
        if prepared.positions[cursor]? = some position then
          some (localAccess tree segment.data provenance kind tags mode).location else none := by
    have bound := (Array.getElem?_eq_some_iff.mp entry).choose
    by_cases selected : prepared.positions[cursor]? = some position
    · obtain ⟨slotPosition, slot, positionAt, segmentAt, slotEntry, _, _⟩ :=
        geometry.slot cursor ((inCursor cursor).mp member)
      have samePosition := Option.some.inj (positionAt.symm.trans selected)
      subst slotPosition
      have sameSegment := Option.some.inj (slotEntry.symm.trans entry)
      subst slot
      obtain ⟨p, s, posAt, segAt, _, perm⟩ := authorized cursor ((inCursor cursor).mp member)
      have same := Option.some.inj (segAt.symm.trans segmentAt)
      subst s
      rw [← RangeVerification.locationContract_iff] at perm
      have result := (RangeVerification.location_success_range_irrelevant tree segment.data
        (source tree provenance) kind tags mode segment.range ⟨0, 0⟩
        (fun after => after = (tree.performTreeAccessAt segment.data (source tree provenance) kind tags mode
          segment.range).location)).mp ⟨perm, rfl⟩
      simp [snapshotLocationAt, selected, bound, segmentAt, retained, retainedAccess, localAccess, result.2]
    · simp [snapshotLocationAt, selected]
  have result :
      find = if range.start ≤ byte ∧ byte < range.stop then
        some (localAccess tree segment.data provenance kind tags mode).location else none := by
    by_cases inside : range.start ≤ byte ∧ byte < range.stop
    · rw [ite_eq_left inside]
      obtain ⟨cursor, bounded, found⟩ := geometry.coverage position segment byte entry covered inside
      have hit := evaluate cursor ((inCursor cursor).mpr bounded)
      simp only [found, ↓reduceIte] at hit
      cases answer : find with
      | none =>
        have missing := List.findSome?_eq_none_iff.mp answer cursor ((inCursor cursor).mpr bounded)
        rw [hit] at missing
        contradiction
      | some data =>
        obtain ⟨c, member, equal⟩ := List.exists_of_findSome?_eq_some answer
        rw [evaluate c member] at equal
        split at equal
        · exact equal.symm
        · contradiction
    · have missing : find = none := List.findSome?_eq_none_iff.mpr fun cursor member => by
        rw [evaluate cursor member]
        split
        · rename_i selected
          obtain ⟨slotPosition, slot, positionAt, _, slotEntry, _, within⟩ :=
            geometry.slot cursor ((inCursor cursor).mp member)
          have samePosition := Option.some.inj (positionAt.symm.trans selected)
          subst slotPosition
          have sameSegment := Option.some.inj (slotEntry.symm.trans entry)
          subst slot
          exact False.elim (inside (within byte covered))
        · rfl
      rwa [ite_eq_right inside]
  simp only [TreeRangePointwiseWP.readLocations, Array.getElem?_mapIdx, entry, Option.map_some]
  change some { segment with data := find.getD segment.data } = _
  rw [result]
  split <;> rfl

/-- The byte is unchanged outside the access, and inside it retains the local permission and cache update. -/
def afterAccessFrom (tree : BorrowTree) (provenance : ProvenanceExtra) (kind : AccessKind) (range : ByteRange)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (before : UInt64 → LocationTree → Prop)
    (byte : UInt64) (data : LocationTree) : Prop :=
  ∃ initial, before byte initial ∧
    (range.Contains byte → (localAccess tree initial provenance kind tags mode).location = data) ∧
    (¬ range.Contains byte → initial = data)

/-- Observe a single access starting from the tree's current byte partition. -/
abbrev afterAccess (tree : BorrowTree) (provenance : ProvenanceExtra) (kind : AccessKind) (range : ByteRange)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) : UInt64 → LocationTree → Prop :=
  afterAccessFrom tree provenance kind range tags mode tree.locations.MapAt

/-- Byte interpretation uses the supplied initial locations and the tree's
tag mapping and topology, independently of the tree's own location partition. -/
theorem afterAccessFrom_replaceLocations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (provenance : ProvenanceExtra) (kind : AccessKind) (range : ByteRange)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (before : UInt64 → LocationTree → Prop) :
    afterAccessFrom { tree with locations } provenance kind range tags mode before =
      afterAccessFrom tree provenance kind range tags mode before := by
  cases provenance <;> rfl

private theorem accessLocations_byte (tree : BorrowTree) (provenance : ProvenanceExtra) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (prepared : IterMutResult LocationTree)
    (range : ByteRange) (geometry : prepared.PreparedFor range tree.locations.MapAt)
    (authorized : ∀ cursor, cursor < prepared.positions.size →
      SlotAuthorized tree prepared (source tree provenance) kind tags mode cursor)
    (byte : UInt64) (data : LocationTree) :
    (TreeRangePointwiseWP.readLocations prepared (retainedAccess tree provenance kind tags mode prepared)).MapAt byte data ↔
      afterAccess tree provenance kind range tags mode byte data := by
  classical
  constructor
  · rintro ⟨position, segment, entry, within, rfl⟩
    have original : ∃ prior, prepared.state.entries[position]? = some prior ∧
        prior.range = segment.range := by
      simp only [TreeRangePointwiseWP.readLocations, Array.getElem?_mapIdx] at entry
      cases found : prepared.state.entries[position]? with
      | none => simp [found] at entry
      | some prior =>
        rw [found, Option.map_some] at entry
        have same := congrArg RangeMapSegment.range (Option.some.inj entry)
        exact ⟨prior, rfl, same⟩
    obtain ⟨prior, priorEntry, sameRange⟩ := original
    have priorContains : prior.range.Contains byte := sameRange ▸ within
    have updated := accessLocations_entry tree provenance kind tags mode prepared range _ geometry authorized
      position prior priorEntry byte priorContains
    rw [entry] at updated
    have value := congrArg RangeMapSegment.data (Option.some.inj updated)
    refine ⟨prior.data, (geometry.partition byte prior.data).mp
      ⟨position, prior, priorEntry, priorContains, rfl⟩, ?_, ?_⟩
    · intro inside
      change range.start ≤ byte ∧ byte < range.stop at inside
      simpa only [ite_eq_left inside] using value.symm
    · intro outside
      change ¬ (range.start ≤ byte ∧ byte < range.stop) at outside
      simpa only [ite_eq_right outside] using value.symm
  · rintro ⟨initial, initialAt, overlapped, outside⟩
    obtain ⟨position, segment, entry, covers, rfl⟩ := (geometry.partition byte initial).mpr initialAt
    refine ⟨position, { segment with data := data }, ?_, covers, rfl⟩
    have updated := accessLocations_entry tree provenance kind tags mode prepared range _ geometry authorized
      position segment entry byte covers
    rw [updated]
    have value : (if range.start ≤ byte ∧ byte < range.stop then
        (localAccess tree segment.data provenance kind tags mode).location else segment.data) = data := by
      split
      · exact overlapped ‹_›
      · exact outside ‹_›
    rw [value]

private theorem afterRead_write_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readRange writeRange : ByteRange) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) :
    (∀ byte data, afterAccess tree reader .Read readRange readTags readMode byte data →
      writeRange.Contains byte → (localAccess tree data writer .Write writeTags writeMode).status.getD .Completed = .Completed) ↔
    (∀ byte initial, tree.locations.MapAt byte initial → writeRange.Contains byte →
      (readRange.Contains byte →
        (localAccess tree (localAccess tree initial reader .Read readTags readMode).location
          writer .Write writeTags writeMode).status.getD .Completed = .Completed) ∧
      (¬ readRange.Contains byte →
        (localAccess tree initial writer .Write writeTags writeMode).status.getD .Completed = .Completed)) := by
  constructor
  · intro allowed byte initial found writes
    exact ⟨fun reads => allowed byte _ ⟨initial, found, fun _ => rfl, fun outside => (outside reads).elim⟩ writes,
      fun outside => allowed byte _ ⟨initial, found, fun reads => (outside reads).elim, fun _ => rfl⟩ writes⟩
  · rintro allowed byte data ⟨initial, found, overlapped, outside⟩ writes
    by_cases reads : readRange.Contains byte
    · rw [← overlapped reads]
      exact (allowed byte initial found writes).1 reads
    · rw [← outside reads]
      exact (allowed byte initial found writes).2 reads

/-- Exact safety for arbitrary read and write intervals when iterator preparation
has its byte-level geometry. The writer certificate can be provided uniformly for
maps with the partition's geometry, independently of the permission checks. -/
theorem wp_read_write_bytes_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size) (readRange writeRange : ByteRange)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (readGeometry : (tree.locations.iterMut readOffset readLength).PreparedFor readRange tree.locations.MapAt)
    (writeGeometry : ∀ map : DedupRangeMap LocationTree,
      map.entries.map (·.range) =
        (tree.locations.iterMut readOffset readLength).state.entries.map (·.range) →
      (map.iterMut writeOffset writeLength).PreparedFor writeRange map.MapAt) :
    wp ((do
      let reads ← TreeBorrowsWP.access reader readOffset readLength .Read readTags readMode
      let writes ← TreeBorrowsWP.access writer writeOffset writeLength .Write writeTags writeMode
      pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
        (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace)) (fun _ _ => True) (fun _ _ => False) tree ↔
    readWritePre tree reader writer readRange writeRange readTags writeTags readMode writeMode := by
  let prepared := tree.locations.iterMut readOffset readLength
  let retained := retainedAccess tree reader .Read readTags readMode prepared
  let readMap := TreeRangePointwiseWP.readLocations prepared retained
  have writes (readAllowed : ∀ cursor, cursor < prepared.positions.size →
      SlotAuthorized tree prepared (source tree reader) .Read readTags readMode cursor) :
      TreeRangePointwiseWP.writeAuthorized tree writer (readMap.iterMut writeOffset writeLength)
        writeTags writeMode ↔
      resolved tree writer ∧ ∀ byte data, afterAccess tree reader .Read readRange readTags readMode byte data →
        writeRange.Contains byte → (localAccess tree data writer .Write writeTags writeMode).status.getD .Completed = .Completed := by
    have byteMap := accessLocations_byte tree reader .Read readTags readMode prepared readRange readGeometry readAllowed
    have ranges : readMap.entries.map (·.range) = prepared.state.entries.map (·.range) := by
      unfold readMap TreeRangePointwiseWP.readLocations
      dsimp only
      apply Array.ext
      · simp
      · intro index leftBound rightBound
        simp only [Array.getElem_map, Array.getElem_mapIdx]
    have geometry := writeGeometry readMap ranges
    let preparedWrite := readMap.iterMut writeOffset writeLength
    change (resolved tree writer ∧ preparedWrite.outcome = .ok () ∧
      ∀ cursor, cursor < preparedWrite.positions.size →
        SlotAuthorized tree preparedWrite (source tree writer) .Write writeTags writeMode cursor) ↔ _
    rw [geometry.outcome, eq_self, true_and, slots_iff tree writer _ writeRange _ geometry .Write writeTags writeMode]
    constructor
    · rintro ⟨checkedTag, checked⟩
      exact ⟨checkedTag, fun byte data found inside => checked byte data ((byteMap byte data).mpr found) inside⟩
    · rintro ⟨checkedTag, checked⟩
      exact ⟨checkedTag, fun byte data found inside => checked byte data ((byteMap byte data).mp found) inside⟩
  have reads := slots_iff tree reader prepared readRange tree.locations.MapAt readGeometry
    .Read readTags readMode
  rw [TreeRangePointwiseWP.wp_read_write_pointwise_iff, readWritePre_iff]
  change (resolved tree reader ∧ prepared.outcome = .ok () ∧ ∃ chosen,
    (∀ cursor, cursor < prepared.positions.size →
      SnapshotAuthorized tree prepared (source tree reader) .Read readTags readMode cursor (chosen cursor)) ∧
      TreeRangePointwiseWP.writeAuthorized tree writer
        ((TreeRangePointwiseWP.readLocations prepared chosen).iterMut writeOffset writeLength)
        writeTags writeMode) ↔ _
  rw [readGeometry.outcome, eq_self, true_and]
  unfold runtimeReadWritePre
  constructor
  · rintro ⟨readerResolved, chosen, accepted, writerAllowed⟩
    have readAllowed cursor inside := ((retained_iff tree reader .Read readTags readMode prepared cursor
      (chosen cursor)).mp (accepted cursor inside)).1
    have same := TreeRangePointwiseWP.readLocations_congr prepared chosen retained fun cursor inside =>
      ((retained_iff tree reader .Read readTags readMode prepared cursor (chosen cursor)).mp
        (accepted cursor inside)).2.symm
    rw [same] at writerAllowed
    obtain ⟨writerResolved, checked⟩ := (writes readAllowed).mp writerAllowed
    exact ⟨readerResolved, writerResolved, reads.mp readAllowed,
      (afterRead_write_iff tree reader writer readRange writeRange readTags writeTags readMode writeMode).mp
        checked⟩
  · rintro ⟨readerResolved, writerResolved, checkedRead, checkedWrite⟩
    have readAllowed := reads.mpr checkedRead
    exact ⟨readerResolved, retained,
      (fun cursor inside => (retained_iff tree reader .Read readTags readMode prepared cursor
        (retained cursor)).mpr ⟨readAllowed cursor inside, rfl⟩),
      (writes readAllowed).mpr ⟨writerResolved,
        (afterRead_write_iff tree reader writer readRange writeRange readTags writeTags readMode writeMode).mpr
          checkedWrite⟩⟩

/-- The access continuation produced by VC generation uses the same initial
byte obligations as the raw paired-access WP. -/
theorem accessPre_read_write_bytes_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size) (readRange writeRange : ByteRange)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (readGeometry : (tree.locations.iterMut readOffset readLength).PreparedFor readRange tree.locations.MapAt)
    (writeGeometry : ∀ map : DedupRangeMap LocationTree,
      map.entries.map (·.range) =
        (tree.locations.iterMut readOffset readLength).state.entries.map (·.range) →
      (map.iterMut writeOffset writeLength).PreparedFor writeRange map.MapAt) :
    TreeBorrowsWP.accessPre tree reader readOffset readLength .Read readTags readMode (fun after _ =>
      TreeBorrowsWP.accessPre after writer writeOffset writeLength .Write writeTags writeMode
        (fun _ _ => True) (fun _ _ _ => False)) (fun _ _ _ => False) ↔
    readWritePre tree reader writer readRange writeRange readTags writeTags readMode writeMode := by
  rw [← wp_read_write_bytes_iff tree reader writer readOffset readLength writeOffset writeLength
    readRange writeRange readTags writeTags readMode writeMode readGeometry writeGeometry,
    wp_read_write_successPre_iff]
  simp only [accessPre_successPre_iff]

private theorem map_geometry (left right : DedupRangeMap LocationTree)
    (ranges : left.entries.map (·.range) = right.entries.map (·.range)) :
    (right.WellFormed → left.WellFormed) ∧ left.size = right.size := by
  have counts : left.entries.size = right.entries.size := by
    simpa using congrArg Array.size ranges
  have rangeAt (index : Nat) (l : index < left.entries.size) (r : index < right.entries.size) :
      left.entries[index].range = right.entries[index].range := by
    have projected := congrArg (fun entries : Array ByteRange => entries[index]?) ranges
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem l, Array.getElem?_eq_getElem r,
      Option.map_some, Option.some.injEq] using projected
  by_cases empty : left.entries.size = 0
  · have rightEmpty : right.entries.size = 0 := counts.symm.trans empty
    have leftBack : left.entries.back? = none := by
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_none_iff, empty]
      omega
    have rightBack : right.entries.back? = none := by
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_none_iff, rightEmpty]
      omega
    simp [DedupRangeMap.WellFormed, DedupRangeMap.size, empty, leftBack, rightBack]
  · have rightNonempty : right.entries.size ≠ 0 := fun zero => empty (counts.trans zero)
    have last : left.entries.size - 1 = right.entries.size - 1 := by omega
    have leftLast : left.entries.size - 1 < left.entries.size := by omega
    have rightLast : right.entries.size - 1 < right.entries.size := by omega
    have extent := congrArg ByteRange.stop (rangeAt (left.entries.size - 1) leftLast (by omega))
    refine ⟨?_, ?_⟩
    · unfold DedupRangeMap.WellFormed
      rw [dite_eq_right empty, dite_eq_right rightNonempty]
      rintro ⟨start, positive, adjacent⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [rangeAt 0 (by omega) (by omega), start]
      · intro i inside
        rw [rangeAt i inside (by omega)]
        exact positive i (by omega)
      · intro i inside
        rw [rangeAt i (by omega) (by omega), rangeAt (i + 1) inside (by omega)]
        exact adjacent i (by omega)
    · simp only [DedupRangeMap.size, Array.back?_eq_getElem?,
        Array.getElem?_eq_getElem leftLast, Array.getElem?_eq_getElem rightLast]
      simpa only [last] using congrArg Size.ofBytes extent


/-- Resolve provenance and check a range using only the supplied byte locations. -/
def byteChecks (tree : BorrowTree) (provenance : ProvenanceExtra)
    (range : ByteRange) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (before : UInt64 → LocationTree → Prop) : Prop :=
  resolved tree provenance ∧ (∀ byte initial, before byte initial → range.Contains byte →
    localPre tree initial provenance kind tags mode (fun _ => True))

theorem byteChecks_replaceLocations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (provenance : ProvenanceExtra) (range : ByteRange) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (before : UInt64 → LocationTree → Prop) :
    byteChecks { tree with locations } provenance range kind tags mode before ↔
      byteChecks tree provenance range kind tags mode before := by
  simp only [byteChecks, localPre_iff, and_true]
  unfold resolved
  cases provenance <;> rfl

/-- Exact safety for one prepared range with a continuation on its resulting tree and trace. -/
def accessBytePre (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (range : ByteRange) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : TreeRangeOutcomeWP.Trace → BorrowTree → Prop) : Prop :=
  let prepared := tree.locations.iterMut offset length
  byteChecks tree provenance range kind tags mode tree.locations.MapAt ∧
    let final := snapshotSuccessor tree prepared (retainedAccess tree provenance kind tags mode prepared)
    post final.2 final.1

/-- A successful access changes only the locations, preserves partition well-formedness
and extent, and has an exact byte-local interpretation. -/
theorem accessBytePre_observe (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length finish : Size) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (wellFormed : tree.locations.WellFormed)
    (checkedEnd : offset.add length = .ok finish) (bound : finish.bytes ≤ tree.locations.size.bytes)
    (post : TreeRangeOutcomeWP.Trace → BorrowTree → Prop) :
    accessBytePre tree provenance offset length ⟨offset.bytes, finish.bytes⟩ kind tags mode post ↔
      accessBytePre tree provenance offset length ⟨offset.bytes, finish.bytes⟩ kind tags mode
        (fun trace after =>
          after = { tree with locations := after.locations } ∧
          after.locations.WellFormed ∧ after.locations.size = tree.locations.size ∧
          (∀ byte data, after.locations.MapAt byte data ↔
            afterAccess tree provenance kind ⟨offset.bytes, finish.bytes⟩ tags mode byte data) ∧
          post trace after) := by
  classical
  obtain ⟨geometry, preparedFormed, preparedSize⟩ :=
    DedupRangeMap.iterMut_preparedFor tree.locations offset length finish wellFormed checkedEnd bound
  let prepared := tree.locations.iterMut offset length
  let retained := retainedAccess tree provenance kind tags mode prepared
  let after := (snapshotSuccessor tree prepared retained).1
  have readMap := TreeRangePointwiseWP.readLocations_eq tree prepared retained
  have ranges : after.locations.entries.map (·.range) = prepared.state.entries.map (·.range) := by
    change (snapshotSuccessor tree prepared retained).1.locations.entries.map (·.range) = _
    rw [← readMap]
    unfold TreeRangePointwiseWP.readLocations
    apply Array.ext
    · simp
    · intro index leftBound rightBound
      simp only [Array.getElem_map, Array.getElem_mapIdx]
  have ⟨formed, extent⟩ := map_geometry after.locations prepared.state ranges
  unfold accessBytePre byteChecks
  constructor
  · rintro ⟨⟨known, localChecks⟩, done⟩
    have checks := (slots_iff tree provenance prepared _ _ geometry kind tags mode).mpr
      (fun byte initial found within => ((localPre_iff tree initial provenance kind tags mode
        (fun _ => True)).mp (localChecks byte initial found within)).1)
    refine ⟨⟨known, localChecks⟩, rfl, formed preparedFormed, extent.trans preparedSize, ?_, done⟩
    intro byte data
    change after.locations.MapAt byte data ↔ _
    change (snapshotSuccessor tree prepared retained).1.locations.MapAt byte data ↔ _
    rw [← readMap]
    exact accessLocations_byte tree provenance kind tags mode prepared _ geometry checks byte data
  · rintro ⟨⟨known, localChecks⟩, _, _, _, _, done⟩
    exact ⟨⟨known, localChecks⟩, done⟩

/-- The single-access WP under checked byte-range geometry uses exactly the
local checks and the successful state and trace supplied by those checks. -/
theorem wp_access_bytes_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length finish : Size) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (wellFormed : tree.locations.WellFormed)
    (checkedEnd : offset.add length = .ok finish) (bound : finish.bytes ≤ tree.locations.size.bytes)
    (post : TreeRangeOutcomeWP.Trace → BorrowTree → Prop) :
    wp (TreeBorrowsWP.access provenance offset length kind tags mode) post (fun _ _ => False) tree ↔
      accessBytePre tree provenance offset length ⟨offset.bytes, finish.bytes⟩ kind tags mode post := by
  classical
  have geometry := (DedupRangeMap.iterMut_preparedFor tree.locations offset length finish
    wellFormed checkedEnd bound).1
  let prepared := tree.locations.iterMut offset length
  let retained := retainedAccess tree provenance kind tags mode prepared
  have checks := slots_iff tree provenance prepared _ _ geometry kind tags mode
  rw [wp_access_snapshotPre_iff]
  change (resolved tree provenance ∧ prepared.outcome = .ok () ∧ ∃ chosen,
    (∀ cursor, cursor < prepared.positions.size →
      SnapshotAuthorized tree prepared (source tree provenance) kind tags mode cursor (chosen cursor)) ∧
    let final := snapshotSuccessor tree prepared chosen
    post final.2 final.1) ↔ _
  rw [geometry.outcome, eq_self, true_and]
  unfold accessBytePre byteChecks
  constructor
  · rintro ⟨known, chosen, accepted, done⟩
    have authorized cursor inside := (retained_iff tree provenance kind tags mode prepared cursor
      (chosen cursor)).mp (accepted cursor inside)
    have commitSame (cursors : List Nat) (bounded : ∀ cursor ∈ cursors, cursor < prepared.positions.size)
        (current : DedupRangeMap LocationTree × TreeRangeOutcomeWP.Trace) :
        cursors.foldl (commitSnapshot prepared chosen) current =
          cursors.foldl (commitSnapshot prepared retained) current := by
      induction cursors generalizing current with
      | nil => rfl
      | cons cursor rest ih =>
        have same := (authorized cursor (bounded cursor (.head _))).2.symm
        change chosen cursor = retained cursor at same
        have step : commitSnapshot prepared chosen current cursor =
          commitSnapshot prepared retained current cursor := by simp only [commitSnapshot, same]
        rw [List.foldl_cons, List.foldl_cons, step]
        exact ih (fun later member => bounded later (.tail _ member)) _
    refine ⟨⟨known, ?_⟩, ?_⟩
    · intro byte initial found within
      exact (localPre_iff tree initial provenance kind tags mode (fun _ => True)).mpr
        ⟨checks.mp (fun cursor inside => (authorized cursor inside).1) byte initial found within, trivial⟩
    · have same := commitSame (List.range' 0 prepared.positions.size)
        (fun cursor included => by simpa [List.mem_range'] using included) (prepared.state, #[])
      simpa only [snapshotSuccessor, same] using done
  · rintro ⟨⟨known, localChecks⟩, done⟩
    have authorized := checks.mpr (fun byte initial found within =>
      ((localPre_iff tree initial provenance kind tags mode (fun _ => True)).mp
        (localChecks byte initial found within)).1)
    exact ⟨known, retained, fun cursor inside =>
      (retained_iff tree provenance kind tags mode prepared cursor (retained cursor)).mpr
        ⟨authorized cursor inside, rfl⟩, done⟩

/-- An access with a postcondition on byte locations needs only initial byte
checks and the local byte interpretation. It does not reconstruct a range map. -/
theorem wp_access_byteObservation_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length finish : Size) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (wellFormed : tree.locations.WellFormed)
    (checkedEnd : offset.add length = .ok finish) (bound : finish.bytes ≤ tree.locations.size.bytes)
    (post : (UInt64 → LocationTree → Prop) → Prop) :
    wp (TreeBorrowsWP.access provenance offset length kind tags mode)
      (fun _ after => post after.locations.MapAt) (fun _ _ => False) tree ↔
    byteChecks tree provenance ⟨offset.bytes, finish.bytes⟩ kind tags mode tree.locations.MapAt ∧
      post (afterAccess tree provenance kind ⟨offset.bytes, finish.bytes⟩ tags mode) := by
  rw [wp_access_bytes_iff _ _ _ _ _ _ _ _ wellFormed checkedEnd bound]
  have observe := accessBytePre_observe tree provenance offset length finish kind tags mode wellFormed
    checkedEnd bound (fun _ _ => True)
  unfold accessBytePre at *
  constructor
  · rintro ⟨checks, done⟩
    obtain ⟨_, _, _, _, maps, _⟩ := observe.mp ⟨checks, trivial⟩
    have same := funext fun byte => funext fun data => propext (maps byte data)
    exact ⟨checks, same ▸ done⟩
  · rintro ⟨checks, done⟩
    obtain ⟨_, _, _, _, maps, _⟩ := observe.mp ⟨checks, trivial⟩
    have same := funext fun byte => funext fun data => propext (maps byte data)
    refine ⟨checks, ?_⟩
    dsimp only
    rw [same]
    exact done

/-- The access continuation emitted by VCs has the same byte-only rule. -/
theorem accessPre_byteObservation_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length finish : Size) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (wellFormed : tree.locations.WellFormed)
    (checkedEnd : offset.add length = .ok finish) (bound : finish.bytes ≤ tree.locations.size.bytes)
    (post : (UInt64 → LocationTree → Prop) → Prop) :
    TreeBorrowsWP.accessPre tree provenance offset length kind tags mode
      (fun after _ => post after.locations.MapAt) (fun _ _ _ => False) ↔
    byteChecks tree provenance ⟨offset.bytes, finish.bytes⟩ kind tags mode tree.locations.MapAt ∧
      post (afterAccess tree provenance kind ⟨offset.bytes, finish.bytes⟩ tags mode) := by
  exact (TreeRangeOutcomeWP.wp_access_outcomePre_iff tree provenance offset length kind tags mode
    (fun _ after => post after.locations.MapAt) (fun _ _ => False)).symm.trans
      (wp_access_byteObservation_iff tree provenance offset length finish kind tags mode
        wellFormed checkedEnd bound post)

private theorem read_write_geometry (tree : BorrowTree)
    (readOffset readLength readFinish writeOffset writeLength writeFinish : Size)
    (wellFormed : tree.locations.WellFormed)
    (readEnd : readOffset.add readLength = .ok readFinish)
    (writeEnd : writeOffset.add writeLength = .ok writeFinish)
    (readBound : readFinish.bytes ≤ tree.locations.size.bytes)
    (writeBound : writeFinish.bytes ≤ tree.locations.size.bytes) :
    (tree.locations.iterMut readOffset readLength).PreparedFor
      ⟨readOffset.bytes, readFinish.bytes⟩ tree.locations.MapAt ∧
    ∀ map : DedupRangeMap LocationTree,
      map.entries.map (·.range) = (tree.locations.iterMut readOffset readLength).state.entries.map (·.range) →
      (map.iterMut writeOffset writeLength).PreparedFor ⟨writeOffset.bytes, writeFinish.bytes⟩ map.MapAt := by
  obtain ⟨readGeometry, readWellFormed, preserved⟩ :=
    DedupRangeMap.iterMut_preparedFor tree.locations readOffset readLength readFinish wellFormed readEnd readBound
  refine ⟨readGeometry, fun map ranges => ?_⟩
  have ⟨formed, extent⟩ := map_geometry map (tree.locations.iterMut readOffset readLength).state ranges
  exact (DedupRangeMap.iterMut_preparedFor map writeOffset writeLength writeFinish (formed readWellFormed) writeEnd
    (by rwa [extent, preserved])).1

/-- Rewrite a paired read/write goal using two iterator geometry proofs. -/
macro "miri_tree_range_wp" &"bytes" "using" readProof:term "and" writeProof:term : tactic =>
  `(tactic| first
    | rw [wp_read_write_bytes_iff _ _ _ _ _ _ _ _ _ _ _ _ _ $readProof $writeProof]
    | simp only [binderNameHint, TreeRangeCursorsWP.wp_write_return_succeeds_iff]
      rw [accessPre_read_write_bytes_iff _ _ _ _ _ _ _ _ _ _ _ _ _ $readProof $writeProof])


/-- Exact byte-local safety for two checked in-bounds accesses on an initially
well-formed location partition. The endpoints can differ and partially overlap. -/
theorem wp_read_write_wellFormed_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength readFinish writeOffset writeLength writeFinish : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (wellFormed : tree.locations.WellFormed)
    (readEnd : readOffset.add readLength = .ok readFinish)
    (writeEnd : writeOffset.add writeLength = .ok writeFinish)
    (readBound : readFinish.bytes ≤ tree.locations.size.bytes)
    (writeBound : writeFinish.bytes ≤ tree.locations.size.bytes) :
    wp ((do
      let reads ← TreeBorrowsWP.access reader readOffset readLength .Read readTags readMode
      let writes ← TreeBorrowsWP.access writer writeOffset writeLength .Write writeTags writeMode
      pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
        (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace)) (fun _ _ => True) (fun _ _ => False) tree ↔
    readWritePre tree reader writer ⟨readOffset.bytes, readFinish.bytes⟩ ⟨writeOffset.bytes, writeFinish.bytes⟩
      readTags writeTags readMode writeMode := by
  obtain ⟨readGeometry, writeGeometry⟩ := read_write_geometry tree
    readOffset readLength readFinish writeOffset writeLength writeFinish wellFormed readEnd writeEnd
    readBound writeBound
  exact wp_read_write_bytes_iff tree reader writer readOffset readLength writeOffset writeLength
    _ _ readTags writeTags readMode writeMode readGeometry writeGeometry

/-- The generated access continuation has the same byte-local safety
condition under the checked bounds and partition invariant. -/
theorem accessPre_read_write_wellFormed_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength readFinish writeOffset writeLength writeFinish : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (wellFormed : tree.locations.WellFormed)
    (readEnd : readOffset.add readLength = .ok readFinish)
    (writeEnd : writeOffset.add writeLength = .ok writeFinish)
    (readBound : readFinish.bytes ≤ tree.locations.size.bytes)
    (writeBound : writeFinish.bytes ≤ tree.locations.size.bytes) :
    TreeBorrowsWP.accessPre tree reader readOffset readLength .Read readTags readMode (fun after _ =>
      TreeBorrowsWP.accessPre after writer writeOffset writeLength .Write writeTags writeMode
        (fun _ _ => True) (fun _ _ _ => False)) (fun _ _ _ => False) ↔
    readWritePre tree reader writer ⟨readOffset.bytes, readFinish.bytes⟩ ⟨writeOffset.bytes, writeFinish.bytes⟩
      readTags writeTags readMode writeMode := by
  rw [← wp_read_write_wellFormed_iff tree reader writer
    readOffset readLength readFinish writeOffset writeLength writeFinish readTags writeTags readMode writeMode
    wellFormed readEnd writeEnd readBound writeBound, wp_read_write_successPre_iff]
  simp only [accessPre_successPre_iff]

/-- Lower a pair of checked ranged accesses using the initial partition and
the checked endpoints in the local context. -/
macro "miri_tree_range_wp" &"bytes" : tactic =>
  `(tactic| simp (disch := assumption) only [binderNameHint,
    TreeRangeCursorsWP.wp_write_return_succeeds_iff, wp_read_write_wellFormed_iff,
    accessPre_read_write_wellFormed_iff])

/-- Lower a pair using specified proofs of the partition invariant and the
checked endpoints and bounds. -/
macro "miri_tree_range_wp" &"bytes" "using" formed:term "," readEnd:term "," writeEnd:term ","
    readBound:term "," writeBound:term : tactic =>
  `(tactic| first
    | rw [wp_read_write_wellFormed_iff _ _ _ _ _ _ _ _ _ _ _ _ _
        $formed $readEnd $writeEnd $readBound $writeBound]
    | simp only [binderNameHint, TreeRangeCursorsWP.wp_write_return_succeeds_iff]
      rw [accessPre_read_write_wellFormed_iff _ _ _ _ _ _ _ _ _ _ _ _ _
        $formed $readEnd $writeEnd $readBound $writeBound])

end Miri.Verification.TreeOverlapWP

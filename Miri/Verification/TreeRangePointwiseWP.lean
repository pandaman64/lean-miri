import Miri.Verification.TreeRangeAccess

namespace Miri.Verification.TreeRangePointwiseWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree TreeRangeAccess

private theorem replace_ranges (map : DedupRangeMap LocationTree) (position : Nat)
    (value : LocationTree) :
    (map.setAtPos position value).state.entries.map (·.range) = map.entries.map (·.range) := by
  rw [setAtPos_eq]
  by_cases found : position < map.entries.size
  · simp only [found, ↓reduceDIte]
    apply Array.ext
    · simp
    · intro index bounded₁ bounded₂
      simp only [Array.getElem_map]
      by_cases same : position = index
      · subst index
        simp
      · simp [Array.getElem_set, same]
  · simp [found]

private theorem snapshot_ranges (prepared : IterMutResult LocationTree)
    (retained : Nat → TreeLocationAccessAtResult) (cursors : List Nat)
    (current : DedupRangeMap LocationTree × TreeRangeOutcomeWP.Trace) :
    (cursors.foldl (commitSnapshot prepared retained) current).1.entries.map (·.range) =
      current.1.entries.map (·.range) := by
  induction cursors generalizing current with
  | nil => rfl
  | cons cursor rest ih =>
    simp only [List.foldl_cons, ih, commitSnapshot]
    cases prepared.positions[cursor]? <;> cases prepared.segments[cursor]? <;> simp [replace_ranges]

/-- The write iterator needs the result of the read at each stored position.
The ranges come from read preparation. For the data, use the last read
cursor that writes the position, or the prepared value if none does. -/
def readLocations (prepared : IterMutResult LocationTree)
    (retained : Nat → TreeLocationAccessAtResult) : DedupRangeMap LocationTree :=
  ⟨prepared.state.entries.mapIdx fun position segment =>
    let updated := (List.range' 0 prepared.positions.size).reverse.findSome?
      (snapshotLocationAt prepared retained position)
    { segment with data := updated.getD segment.data }⟩

theorem readLocations_eq (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (retained : Nat → TreeLocationAccessAtResult) :
    readLocations prepared retained = (snapshotSuccessor tree prepared retained).1.locations := by
  have ranges :
      (snapshotSuccessor tree prepared retained).1.locations.entries.map (·.range) =
        prepared.state.entries.map (·.range) :=
    snapshot_ranges prepared retained _ (prepared.state, #[])
  have sizes := congrArg Array.size ranges
  simp only [Array.size_map] at sizes
  apply congrArg DedupRangeMap.mk
  apply Array.ext
  · rw [Array.size_mapIdx]
    exact sizes.symm
  · intro position boundLeft boundRight
    have boundFinal : position < (snapshotSuccessor tree prepared retained).1.locations.entries.size :=
      boundRight
    have inside : position < prepared.state.entries.size := sizes ▸ boundFinal
    have sameRange := congrArg (fun entries : Array ByteRange => entries[position]?) ranges
    have sameData := snapshotSuccessor_locationAt tree prepared retained position
    cases updated : (List.range' 0 prepared.positions.size).reverse.findSome?
        (snapshotLocationAt prepared retained position) <;>
      simp [updated, Array.getElem?_eq_getElem boundFinal,
        Array.getElem?_eq_getElem inside, Option.or] at sameData
    all_goals
      simp only [Array.getElem_mapIdx, updated, Option.getD]
      let final := (snapshotSuccessor tree prepared retained).1.locations.entries[position]
      change RangeMapSegment.mk _ _ = RangeMapSegment.mk final.range final.data
      congr 1
      · simpa [final, Array.getElem?_eq_getElem boundFinal, Array.getElem?_eq_getElem inside]
          using sameRange.symm
      · exact sameData.symm

private theorem result_replace_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (source : Option UniIndex) (kind : AccessKind)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange) :
    ({ tree with locations }).performTreeAccessAt location source kind tags mode range =
      tree.performTreeAccessAt location source kind tags mode range := by
  rfl

/-- Check the writer's prepared snapshots using the initial borrow tree's tag
mapping and topology. Each write segment supplies its own post-read location. -/
def writeAuthorized (tree : BorrowTree) (writer : ProvenanceExtra)
    (prepared : IterMutResult LocationTree) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) : Prop :=
  let source := match writer with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  (match writer with
    | .concrete _ => source.isSome = true
    | .wildcard => True) ∧
    prepared.outcome = .ok () ∧
      ∀ cursor, cursor < prepared.positions.size →
        SlotAuthorized tree prepared source .Write tags mode cursor

private theorem writeAuthorized_iff (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (writer : ProvenanceExtra) (offset length : Size) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :
    AccessAuthorized { tree with locations } writer offset length .Write tags mode ↔
      writeAuthorized tree writer (locations.iterMut offset length) tags mode := by
  simp only [AccessAuthorized, writeAuthorized, indexOfTag, SlotAuthorized,
    ← RangeVerification.locationContract_iff, result_replace_locations] <;> rfl

private theorem snapshot_writeAuthorized_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (retained : Nat → TreeLocationAccessAtResult) (writer : ProvenanceExtra) (offset length : Size)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) :
    AccessAuthorized (snapshotSuccessor tree prepared retained).1 writer offset length .Write tags mode ↔
      writeAuthorized tree writer ((readLocations prepared retained).iterMut offset length) tags mode := by
  rw [readLocations_eq tree]
  change AccessAuthorized { tree with locations := (snapshotSuccessor tree prepared retained).1.locations }
    writer offset length .Write tags mode ↔ _
  exact writeAuthorized_iff tree _ writer offset length tags mode

/-- Check the read's initial snapshots, then prepare the writer from their
pointwise retained locations. The writer's preparation may split or merge
them. Both sets of location contracts use the initial tag mapping and topology. -/
def readWritePre (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) : Prop :=
  let prepared := tree.locations.iterMut readOffset readLength
  let source := match reader with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  (match reader with
    | .concrete _ => source.isSome = true
    | .wildcard => True) ∧
    prepared.outcome = .ok () ∧
    ∃ retained : Nat → TreeLocationAccessAtResult,
      (∀ cursor, cursor < prepared.positions.size →
        SnapshotAuthorized tree prepared source .Read readTags readMode cursor (retained cursor)) ∧
      writeAuthorized tree writer ((readLocations prepared retained).iterMut writeOffset writeLength)
        writeTags writeMode

/-- The paired access safety WP can use the initial borrow tree and the
independent read snapshots, without constructing an intermediate borrow tree. -/
theorem wp_read_write_pointwise_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) :
    wp ((do
      let reads ← TreeBorrowsWP.access reader readOffset readLength .Read readTags readMode
      let writes ← TreeBorrowsWP.access writer writeOffset writeLength .Write writeTags writeMode
      pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
        (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace)) (fun _ _ => True) (fun _ _ => False) tree ↔
    readWritePre tree reader writer readOffset readLength writeOffset writeLength
      readTags writeTags readMode writeMode := by
  rw [wp_read_write_snapshotPre_iff]
  change accessSnapshotPre tree reader readOffset readLength .Read readTags readMode
    (fun _ after => accessSnapshotPre after writer writeOffset writeLength .Write writeTags writeMode
      (fun _ _ => True)) ↔ _
  simp only [accessSnapshotPre_true_iff]
  simp only [accessSnapshotPre, readWritePre, snapshot_writeAuthorized_iff] <;> rfl

/-- Use the initial topology and retained read locations to check both accesses. -/
macro "miri_tree_range_wp" "pointwise" : tactic =>
  `(tactic| simp only [wp_read_write_pointwise_iff])

end Miri.Verification.TreeRangePointwiseWP

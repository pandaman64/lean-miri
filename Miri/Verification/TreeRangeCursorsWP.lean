import Miri.Verification.TreeRangePointwiseWP

/-! Compose the contracts of the independent read snapshots in cursor order. -/

namespace Miri.Verification.TreeRangeCursorsWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree TreeRangeAccess TreeRangePointwiseWP

local notation "Retained" => Nat → TreeLocationAccessAtResult

/-- A prepared read cursor supplies its retained location to the continuation
only when the slot is valid and the access completed. -/
def readCursorPre (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (cursor : Nat) (finish : TreeLocationAccessAtResult → Prop) : Prop :=
  match prepared.positions[cursor]?, prepared.segments[cursor]? with
  | some position, some segment =>
    position < prepared.state.entries.size ∧
      RangeVerification.locationContract tree segment.data source .Read tags mode segment.range
        (fun result => result.status.getD .Completed = .Completed ∧ finish result)
  | _, _ => False

private theorem readCursorPre_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (cursor : Nat)
    (finish : TreeLocationAccessAtResult → Prop) :
    readCursorPre tree prepared source tags mode cursor finish ↔
      ∃ result, SnapshotAuthorized tree prepared source .Read tags mode cursor result ∧ finish result := by
  unfold readCursorPre SnapshotAuthorized
  cases position : prepared.positions[cursor]? <;>
    cases segment : prepared.segments[cursor]? <;>
    simp
  rw [← RangeVerification.locationContract_iff]
  simp only [← RangeVerification.locationContract_iff]
  constructor
  · rintro ⟨inside, complete, finished⟩
    exact ⟨_, ⟨inside, rfl, complete⟩, finished⟩
  · rintro ⟨result, ⟨inside, rfl, complete⟩, finished⟩
    exact ⟨inside, complete, finished⟩

private def remember (retained : Retained) (cursor : Nat) (result : TreeLocationAccessAtResult) : Retained :=
  fun atCursor => if atCursor = cursor then result else retained atCursor

/-- Visit each initial read snapshot and retain its output by cursor. The
continuation can form the map of read locations once all cursors complete. -/
def readCursorsPre (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (finish : Retained → Prop) : List Nat → Retained → Prop
  | [], retained => finish retained
  | cursor :: rest, retained =>
    readCursorPre tree prepared source tags mode cursor fun result =>
      readCursorsPre tree prepared source tags mode finish rest (remember retained cursor result)

private theorem readCursorsPre_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (finish : Retained → Prop) (cursors : List Nat) (distinct : cursors.Nodup) (initial : Retained) :
    readCursorsPre tree prepared source tags mode finish cursors initial ↔
      ∃ chosen : Retained,
        (∀ cursor ∈ cursors, SnapshotAuthorized tree prepared source .Read tags mode cursor (chosen cursor)) ∧
        finish (fun cursor => if cursor ∈ cursors then chosen cursor else initial cursor) := by
  induction cursors generalizing initial with
  | nil =>
    simpa [readCursorsPre] using
      (show finish initial ↔ ∃ _ : Retained, finish initial from
        ⟨fun valid => ⟨initial, valid⟩, fun ⟨_, valid⟩ => valid⟩)
  | cons cursor rest ih =>
    obtain ⟨outside, distinct⟩ := List.nodup_cons.mp distinct
    simp only [readCursorsPre, readCursorPre_iff, ih distinct]
    constructor
    · rintro ⟨head, accepted, tail, subsequent, finished⟩
      refine ⟨remember tail cursor head, ?_, ?_⟩
      · intro index included
        rcases List.mem_cons.mp included with rfl | later
        · simpa [remember] using accepted
        · have other : index ≠ cursor := fun same => outside (same ▸ later)
          simpa [remember, other] using subsequent index later
      · have sameRetained :
            (fun index => if index ∈ cursor :: rest then remember tail cursor head index else initial index) =
              (fun index => if index ∈ rest then tail index else remember initial cursor head index) := by
          funext index
          by_cases same : index = cursor
          · subst index
            simp [remember, outside]
          · simp [remember, same]
        rw [sameRetained]
        exact finished
    · rintro ⟨chosen, accepted, finished⟩
      refine ⟨chosen cursor, accepted cursor (.head _), chosen,
        fun index later => accepted index (.tail _ later), ?_⟩
      have sameRetained :
          (fun index => if index ∈ rest then chosen index else remember initial cursor (chosen cursor) index) =
            (fun index => if index ∈ cursor :: rest then chosen index else initial index) := by
        funext index
        by_cases same : index = cursor
        · subst index
          simp [remember, outside]
        · simp [remember, same]
      rw [sameRetained]
      exact finished

private theorem readLocations_congr (prepared : IterMutResult LocationTree)
    (left right : Retained) (same : ∀ cursor, cursor < prepared.positions.size → left cursor = right cursor) :
    readLocations prepared left = readLocations prepared right := by
  have findSame (position : Nat) (cursors : List Nat)
      (bounded : ∀ cursor ∈ cursors, cursor < prepared.positions.size) :
      cursors.findSome? (snapshotLocationAt prepared left position) =
        cursors.findSome? (snapshotLocationAt prepared right position) := by
    induction cursors with
    | nil => rfl
    | cons cursor rest ih =>
      have atHead := same cursor (bounded cursor (.head _))
      have atTail := ih (fun index later => bounded index (.tail _ later))
      have headResult : snapshotLocationAt prepared left position cursor =
          snapshotLocationAt prepared right position cursor := by
        simp only [snapshotLocationAt, atHead]
      simp only [List.findSome?_cons, headResult, atTail]
  unfold readLocations
  congr 1
  apply congrArg (prepared.state.entries.mapIdx)
  funext position segment
  rw [findSame]
  intro cursor included
  simpa [List.mem_range'] using included

/-- Pair a read and write by passing each retained read result into the next
cursor's continuation. The writer uses the resulting location map and checks
its own prepared snapshots with the original tag mapping and topology. -/
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
    readCursorsPre tree prepared source readTags readMode
      (fun retained => writeAuthorized tree writer ((readLocations prepared retained).iterMut writeOffset writeLength)
        writeTags writeMode)
      (List.range' 0 prepared.positions.size) (fun _ => ⟨default, none, none⟩)

theorem readWritePre_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) :
    readWritePre tree reader writer readOffset readLength writeOffset writeLength
        readTags writeTags readMode writeMode ↔
      TreeRangePointwiseWP.readWritePre tree reader writer readOffset readLength writeOffset writeLength
        readTags writeTags readMode writeMode := by
  let prepared := tree.locations.iterMut readOffset readLength
  let cursors := List.range' 0 prepared.positions.size
  have distinct : cursors.Nodup := List.nodup_range'
  have bounded (cursor : Nat) : cursor ∈ cursors ↔ cursor < prepared.positions.size := by
    simp [cursors, List.mem_range']
  unfold readWritePre TreeRangePointwiseWP.readWritePre
  dsimp only
  rw [readCursorsPre_iff _ _ _ _ _ _ _ distinct]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply exists_congr
  intro chosen
  have same : readLocations prepared (fun cursor =>
      if cursor ∈ cursors then chosen cursor else ⟨default, none, none⟩) = readLocations prepared chosen :=
    readLocations_congr prepared _ _ fun cursor inside => by simp [(bounded cursor).mpr inside]
  change ((∀ cursor ∈ cursors, _) ∧ writeAuthorized tree writer
      ((readLocations prepared (fun cursor => if cursor ∈ cursors then chosen cursor else ⟨default, none, none⟩)).iterMut
        writeOffset writeLength) writeTags writeMode) ↔ _
  rw [same]
  simp only [bounded, prepared]
  rfl

/-- Exact safety rule with a cursor continuation that determines the retained
locations from the initial read contracts. -/
theorem wp_read_write_cursors_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) :
    wp ((do
      let reads ← TreeBorrowsWP.access reader readOffset readLength .Read readTags readMode
      let writes ← TreeBorrowsWP.access writer writeOffset writeLength .Write writeTags writeMode
      pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
        (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace)) (fun _ _ => True) (fun _ _ => False) tree ↔
    readWritePre tree reader writer readOffset readLength writeOffset writeLength
      readTags writeTags readMode writeMode := by
  rw [wp_read_write_pointwise_iff, readWritePre_iff]

/-- The nested continuation emitted by VC generation reduces to the same
cursor rule as the raw state-monad WP. -/
theorem accessPre_read_write_cursors_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) :
    TreeBorrowsWP.accessPre tree reader readOffset readLength .Read readTags readMode (fun after _ =>
      TreeBorrowsWP.accessPre after writer writeOffset writeLength .Write writeTags writeMode
        (fun _ _ => True) (fun _ _ _ => False)) (fun _ _ _ => False) ↔
    readWritePre tree reader writer readOffset readLength writeOffset writeLength
      readTags writeTags readMode writeMode := by
  rw [← wp_read_write_cursors_iff, wp_read_write_successPre_iff]
  simp only [accessPre_successPre_iff]

private theorem wp_write_return_succeeds_iff (tree : BorrowTree) (writer : ProvenanceExtra)
    (offset length : Size) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (reads : TreeRangeOutcomeWP.Trace) :
    wp (do
      let writes ← TreeBorrowsWP.access writer offset length .Write tags mode
      pure (reads, writes)) (fun _ _ => True) (fun _ _ => False) tree ↔
    TreeBorrowsWP.accessPre tree writer offset length .Write tags mode
      (fun _ _ => True) (fun _ _ _ => False) := by
  rw [accessPre_succeeds_iff, ← wp_access_succeeds_iff]
  simp only [wp, WP.wpTrans, bind, Bind.bind, EStateM.bind]
  cases TreeBorrowsWP.access writer offset length .Write tags mode tree <;> rfl

/-- Reduce a paired-range safety check in a raw WP or in a generated VC. -/
macro "miri_tree_range_wp" "safety" : tactic =>
  `(tactic| simp only [binderNameHint, wp_read_write_cursors_iff, wp_write_return_succeeds_iff,
    accessPre_read_write_cursors_iff])

end Miri.Verification.TreeRangeCursorsWP

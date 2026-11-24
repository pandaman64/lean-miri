import Miri.Verification.TreeBorrowsWP

/-! Recover the whole ranged access from permission facts at each iterator
position. The commits preserve the number of slots for the next cursor. -/
namespace Miri.Verification.TreeRangeAccess

open Miri.DataStructures Miri.TreeBorrows Miri.Memory Miri.ABI Std.WP

private theorem setAtPos_eq {A : Type} (table : DedupRangeMap A) (position : Nat) (data : A) :
    table.setAtPos position data =
      if inside : position < table.entries.size then
        ⟨⟨table.entries.set position {table.entries[position] with data} inside⟩, .ok ()⟩
      else ⟨table, .error (.indexOutOfBounds position table.entries.size)⟩ := by
  unfold DedupRangeMap.setAtPos
  change ((match (if ok : position < table.entries.size then some table.entries[position] else none) with
    | none => ⟨table, .error (.indexOutOfBounds position table.entries.size)⟩
    | some segment =>
      match (if ok : position < table.entries.size then
                Except.ok (table.entries.set position {segment with data} ok)
              else Except.error (.indexOutOfBounds position table.entries.size)) with
      | .error error => ⟨table, .error error⟩
      | .ok entries => ⟨⟨entries⟩, .ok ()⟩) : DedupMutationResult (DedupRangeMap A)) = _
  by_cases inside : position < table.entries.size <;> simp [inside]

open BorrowTree
/-- A successful normal access discharges a copy slot in a single-root tree. -/
theorem slotCompleteForSingleRoot (tree : BorrowTree) (location : LocationTree) (source root : UniIndex)
    (kind : AccessKind) (protectors : ProtectedTags) (range : ByteRange)
    (roots : tree.roots = #[root])
    (outcome : (tree.performNormalAccessAt location source kind protectors .VisitChildrenOfAccessed).outcome =
      .ok ())
    (normal : (tree.performNormalAccessAt location source kind protectors .VisitChildrenOfAccessed).access.status =
      .Completed)
    (rootIndex : UniIndex.ofNat?
      (tree.performNormalAccessAt location source kind protectors .VisitChildrenOfAccessed).access.root =
        some root) :
    (tree.performTreeAccessAt location (some source) kind protectors .VisitChildrenOfAccessed range).status =
      none := by
  unfold BorrowTree.performTreeAccessAt
  simp only [Id.run, outcome, normal, rootIndex, roots, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Array.size_singleton, List.range',
    List.forIn_cons, List.forIn_nil, Array.getElem?_singleton, bind, Bind.bind, pure, Pure.pure]
  simp [beq_iff_eq]

/-- A wildcard slot succeeds exactly when the ordered checks starting from
its prepared permissions and cache all succeed. -/
theorem wildcardRootsComplete_iff (tree : BorrowTree) (location : LocationTree)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange) :
    RangeVerification.locationContract tree location none kind tags mode range
        (fun result => result.status.getD .Completed = .Completed) ↔
      RangeVerification.otherRootsContract tree none kind tags mode range none none
        (fun _ => True) (fun _ _ => False) (List.range' 0 tree.roots.size) location := by
  rw [RangeVerification.locationContract_wildcard_eq]
  -- The failure branch receives only wildcard errors from the ordered roots.
  generalize List.range' 0 tree.roots.size = positions
  induction positions generalizing location with
  | nil => simp
  | cons position rest ih =>
    simp only [RangeVerification.otherRootsContract]
    split
    · exact ih location
    · exact iff_true_intro rfl
    · apply Iff.of_eq
      congr 1
      funext result
      by_cases complete : result.status = .Completed
      · simp only [complete, ↓reduceIte]
        exact propext (ih result.location)
      · simp [complete]

/-- With two wildcard roots, success checks the first root and then the
second root on its updated location. Neither root receives a concrete tag bound. -/
theorem wildcardTwoRootsComplete_iff (tree : BorrowTree) (location : LocationTree)
    (first second : UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange) (roots : tree.roots = #[first, second]) :
    RangeVerification.locationContract tree location none kind tags mode range
        (fun result => result.status.getD .Completed = .Completed) ↔
      RangeVerification.wildcardPre tree location first none kind tags false (fun initial =>
        initial.status = .Completed ∧
          RangeVerification.wildcardPre tree initial.location second none kind tags true
            (fun last => last.status = .Completed)) := by
  simp only [← RangeVerification.locationContract_iff, ← RangeVerification.wildcardPre_iff]
  unfold performTreeAccessAt
  simp only [Id.run, roots, Array.size, List.length, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  cases firstResult : tree.performWildcardAccessAt location first none kind tags false
  rename_i intermediate status
  cases status <;> simp [List.range', List.forIn_cons, List.forIn_nil, firstResult,
    bind, Bind.bind, pure, Pure.pure]
  cases lastResult : tree.performWildcardAccessAt intermediate second none kind tags true
  rename_i final status
  cases status <;> simp

/-- Authorization is checked at each actual prepared snapshot, with its
concrete or wildcard source and its checked write-back position. -/
def SlotsAuthorized (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : Prop :=
  ∀ cursor, cursor < prepared.positions.size →
    ∃ position segment, prepared.positions[cursor]? = some position ∧
      prepared.segments[cursor]? = some segment ∧ position < prepared.state.entries.size ∧
      (tree.performTreeAccessAt segment.data source kind protectors mode segment.range).status = none

/-- Build the slot invariant from ordinary tree transitions and checked
positions when every location belongs to one root. -/
theorem SlotsAuthorized.ofSingleRoot (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source root : UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (roots : tree.roots = #[root])
    (owned : ∀ cursor, cursor < prepared.positions.size →
      ∃ position segment, prepared.positions[cursor]? = some position ∧
        prepared.segments[cursor]? = some segment ∧ position < prepared.state.entries.size ∧
        let access := tree.performNormalAccessAt segment.data source kind protectors .VisitChildrenOfAccessed
        access.outcome = .ok () ∧ access.access.status = .Completed ∧
          UniIndex.ofNat? access.access.root = some root) :
    SlotsAuthorized tree prepared (some source) kind protectors .VisitChildrenOfAccessed := by
  intro cursor within
  obtain ⟨position, segment, pos, slot, valid, outcome, complete, rootIndex⟩ := owned cursor within
  exact ⟨position, segment, pos, slot, valid,
    slotCompleteForSingleRoot tree segment.data source root kind protectors segment.range
      roots outcome complete rootIndex⟩

private def runSlots (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursors : List Nat) (current : RangeVerification.Progress) :
    RangeVerification.Progress :=
  cursors.foldl (fun progress cursor =>
    RangeVerification.advance tree prepared source kind protectors mode cursor progress) current

private theorem runSlots_stopped (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursors : List Nat) (current : RangeVerification.Progress)
    (failed : current.2.2 ≠ .Completed) :
    runSlots tree prepared source kind protectors mode cursors current = current := by
  induction cursors with
  | nil => rfl
  | cons cursor rest ih =>
    simpa [runSlots, RangeVerification.advance, failed]
      using ih

/-- The per-cursor condition checks the original snapshot, even if an
earlier cursor writes to the same position. -/
def SlotAuthorized (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) : Prop :=
  ∃ position segment, prepared.positions[cursor]? = some position ∧
    prepared.segments[cursor]? = some segment ∧ position < prepared.state.entries.size ∧
    RangeVerification.locationContract tree segment.data source kind protectors mode segment.range
      (fun result => result.status.getD .Completed = .Completed)

private theorem advance_complete_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) (current : RangeVerification.Progress)
    (ready : current.2.2 = .Completed) (size : current.1.entries.size = prepared.state.entries.size) :
    let next := RangeVerification.advance tree prepared source kind protectors mode cursor current
    (next.2.2 = .Completed ↔ SlotAuthorized tree prepared source kind protectors mode cursor) ∧
      (next.2.2 = .Completed → next.1.entries.size = prepared.state.entries.size) := by
  simp only [RangeVerification.advance, ready, beq_self_eq_true, ↓reduceIte, SlotAuthorized]
  cases positionAt : prepared.positions[cursor]? with
  | none => simp
  | some position =>
    cases segmentAt : prepared.segments[cursor]? with
    | none => simp
    | some segment =>
      simp only [Option.some.injEq]
      simp
      rw [← RangeVerification.locationContract_iff]
      rw [setAtPos_eq]
      by_cases within : position < prepared.state.entries.size <;> simp [within, size]

private theorem runSlots_complete_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursors : List Nat) (current : RangeVerification.Progress)
    (ready : current.2.2 = .Completed) (size : current.1.entries.size = prepared.state.entries.size) :
    (runSlots tree prepared source kind protectors mode cursors current).2.2 = .Completed ↔
      ∀ cursor ∈ cursors, SlotAuthorized tree prepared source kind protectors mode cursor := by
  induction cursors generalizing current with
  | nil => simpa [runSlots] using ready
  | cons cursor rest ih =>
    let next := RangeVerification.advance tree prepared source kind protectors mode cursor current
    change (runSlots tree prepared source kind protectors mode rest next).2.2 = .Completed ↔ _
    rw [List.forall_mem_cons]
    obtain ⟨authorized, sameSize⟩ :=
      advance_complete_iff tree prepared source kind protectors mode cursor current ready size
    by_cases complete : next.2.2 = .Completed
    · rw [ih next complete (sameSize complete), ← authorized, and_iff_right complete]
    · rw [runSlots_stopped _ _ _ _ _ _ _ _ complete, ← authorized]
      exact ⟨fun impossible => (complete impossible).elim, fun both => (complete both.1).elim⟩

private theorem rangeResult_eq_runSlots (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex)
    (selected : match provenance with
      | .concrete tag => ∃ index, source = some index ∧ tree.indexOfTag tag = some index
      | .wildcard => source = none)
    (prepare : tree.locations.iterMut offset length = prepared)
    (okay : prepared.outcome = .ok ()) :
    tree.performBorrowAccessRange provenance offset length kind protectors mode =
      let final := runSlots tree prepared source kind protectors mode
        (List.range' 0 prepared.positions.size) (prepared.state, #[], .Completed)
      ⟨{ tree with locations := final.1 }, final.2.1, final.2.2⟩ := by
  have foldSlots (source : Option UniIndex) :
      (forIn (List.range' 0 prepared.positions.size) (prepared.state, #[], .Completed)
        (fun cursor current => .yield (RangeVerification.advance tree prepared source kind protectors mode
          cursor current)) : Id RangeVerification.Progress) =
      runSlots tree prepared source kind protectors mode (List.range' 0 prepared.positions.size)
        (prepared.state, #[], .Completed) :=
    List.idRun_forIn_yield_eq_foldl _ _ _
  unfold performBorrowAccessRange
  cases provenance with
  | concrete tag =>
    obtain ⟨index, rfl, found⟩ := selected
    simp only [Id.run, found, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, prepare, okay,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, RangeVerification.cursor_equation]
    simp only [bind, Bind.bind, pure, Pure.pure, foldSlots]
  | wildcard =>
    subst source
    simp only [Id.run, prepare, okay, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, RangeVerification.cursor_equation]
    simp only [bind, Bind.bind, pure, Pure.pure, foldSlots]

/-- Every prepared slot is authorized exactly when the ranged operation succeeds.
This rule applies equally to concrete and wildcard sources and includes the
ordered wildcard traversal of other roots in each slot's location contract. -/
theorem rangeComplete_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex)
    (selected : match provenance with
      | .concrete tag => ∃ index, source = some index ∧ tree.indexOfTag tag = some index
      | .wildcard => source = none)
    (prepare : tree.locations.iterMut offset length = prepared)
    (okay : prepared.outcome = .ok ()) :
    (tree.performBorrowAccessRange provenance offset length kind protectors mode).status = .Completed ↔
      ∀ cursor, cursor < prepared.positions.size →
        SlotAuthorized tree prepared source kind protectors mode cursor := by
  rw [rangeResult_eq_runSlots tree provenance offset length kind protectors mode prepared source
    selected prepare okay]
  simpa [List.mem_range'] using
    runSlots_complete_iff tree prepared source kind protectors mode
      (List.range' 0 prepared.positions.size) (prepared.state, #[], .Completed) rfl rfl

/-- Resolve provenance and prepare the iterator before checking each original
snapshot. Missing concrete tags and preparation failures make this condition false. -/
def AccessAuthorized (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : Prop :=
  let source := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  let prepared := tree.locations.iterMut offset length
  (match provenance with
  | .concrete _ => source.isSome = true
  | .wildcard => True) ∧
    prepared.outcome = .ok () ∧
    ∀ cursor, cursor < prepared.positions.size →
      SlotAuthorized tree prepared source kind protectors mode cursor

/-- The unconditional safety precondition uses only source resolution,
successful iterator preparation and per-cursor obligations. -/
theorem rangeComplete_iff_authorized (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :
    (tree.performBorrowAccessRange provenance offset length kind protectors mode).status = .Completed ↔
      AccessAuthorized tree provenance offset length kind protectors mode := by
  let prepared := tree.locations.iterMut offset length
  cases provenance with
  | concrete tag =>
    cases found : tree.indexOfTag tag with
    | none => simp [AccessAuthorized, performBorrowAccessRange, found, Id.run, pure, Pure.pure]
    | some index =>
      cases checked : prepared.outcome with
      | error error =>
        have rejected : (tree.locations.iterMut offset length).outcome = .error error := checked
        simp [AccessAuthorized, performBorrowAccessRange, found, rejected, Id.run, pure, Pure.pure]
      | ok value =>
        cases value
        simpa [AccessAuthorized, found, checked, prepared] using
          rangeComplete_iff tree (.concrete tag) offset length kind protectors mode prepared (some index)
            ⟨index, rfl, found⟩ rfl checked
  | wildcard =>
    cases checked : prepared.outcome with
    | error error =>
      have rejected : (tree.locations.iterMut offset length).outcome = .error error := checked
      simp [AccessAuthorized, performBorrowAccessRange, rejected, Id.run, pure, Pure.pure]
    | ok value =>
      cases value
      simpa [AccessAuthorized, checked, prepared] using
        rangeComplete_iff tree .wildcard offset length kind protectors mode prepared none rfl rfl checked

/-- Commit one prepared snapshot's local successor and append its trace.
Successful range proofs establish the cursor's lookups and write-back bounds. -/
def commitPreparedSlot (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult)
    (cursor : Nat) : DedupRangeMap LocationTree × Array BorrowTreeLocationResult :=
  match prepared.positions[cursor]?, prepared.segments[cursor]? with
  | some position, some segment =>
    let access := tree.performTreeAccessAt segment.data source kind protectors mode segment.range
    ((current.1.setAtPos position access.location).state,
      current.2.push ⟨segment.range, access.normalAccess⟩)
  | _, _ => current

/-- The location a cursor writes to the given map position, if it writes
there. The permission transition uses that cursor's prepared snapshot. -/
def preparedSlotLocationAt (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (position cursor : Nat) : Option LocationTree :=
  if position < prepared.state.entries.size ∧ prepared.positions[cursor]? = some position then
    prepared.segments[cursor]?.map fun segment =>
      (tree.performTreeAccessAt segment.data source kind protectors mode segment.range).location
  else none

private theorem commitPreparedSlot_locationAt (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult)
    (size : current.1.entries.size = prepared.state.entries.size) (position cursor : Nat) :
    let next := commitPreparedSlot tree prepared source kind protectors mode current cursor
    next.1.entries.size = prepared.state.entries.size ∧
      next.1.entries[position]?.map (·.data) =
        (preparedSlotLocationAt tree prepared source kind protectors mode position cursor).or
          (current.1.entries[position]?.map (·.data)) := by
  unfold commitPreparedSlot preparedSlotLocationAt
  cases positionAt : prepared.positions[cursor]? with
  | none => simp [size]
  | some written =>
    cases segmentAt : prepared.segments[cursor]? with
    | none => simp [size]
    | some segment =>
      simp only []
      rw [setAtPos_eq]
      by_cases same : written = position
      · subst written
        by_cases inside : position < prepared.state.entries.size <;> simp [size, inside, Option.or]
      · by_cases inside : written < prepared.state.entries.size <;> simp [size, inside, same, Option.or]

private theorem committed_locationAt (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult)
    (size : current.1.entries.size = prepared.state.entries.size)
    (position : Nat) (cursors : List Nat) :
    let final := cursors.foldl (commitPreparedSlot tree prepared source kind protectors mode) current
    final.1.entries[position]?.map (·.data) =
      (cursors.reverse.findSome? (preparedSlotLocationAt tree prepared source kind protectors mode position)).or
        (current.1.entries[position]?.map (·.data)) := by
  induction cursors generalizing current with
  | nil => rfl
  | cons cursor rest ih =>
    obtain ⟨sameSize, updated⟩ := commitPreparedSlot_locationAt tree prepared source kind protectors mode
      current size position cursor
    simp only [List.foldl_cons, ih _ sameSize, updated, List.reverse_cons, List.findSome?_append,
      List.findSome?_cons, List.findSome?_nil]
    rw [Option.or_assoc]
    cases preparedSlotLocationAt tree prepared source kind protectors mode position cursor <;> rfl

private theorem runSlots_eq_commit (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursors : List Nat)
    (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult)
    (size : current.1.entries.size = prepared.state.entries.size)
    (allowed : ∀ cursor ∈ cursors, SlotAuthorized tree prepared source kind protectors mode cursor) :
    runSlots tree prepared source kind protectors mode cursors (current.1, current.2, .Completed) =
      let final := cursors.foldl (commitPreparedSlot tree prepared source kind protectors mode) current
      (final.1, final.2, .Completed) := by
  induction cursors generalizing current with
  | nil => rfl
  | cons cursor rest ih =>
    let next := commitPreparedSlot tree prepared source kind protectors mode current cursor
    have authorized := allowed cursor (.head _)
    obtain ⟨done, sameSize⟩ := advance_complete_iff tree prepared source kind protectors mode cursor
      (current.1, current.2, .Completed) rfl size
    have completed := done.mpr authorized
    obtain ⟨position, segment, positionAt, segmentAt, inside, _⟩ := authorized
    have step : RangeVerification.advance tree prepared source kind protectors mode cursor
        (current.1, current.2, .Completed) = (next.1, next.2, .Completed) := by
      apply Prod.ext
      · simp [RangeVerification.advance, next, commitPreparedSlot, positionAt, segmentAt]
      · apply Prod.ext
        · simp [RangeVerification.advance, next, commitPreparedSlot, positionAt, segmentAt]
        · exact completed
    have sizeNext : next.1.entries.size = prepared.state.entries.size := by
      simpa only [step] using sameSize completed
    change runSlots tree prepared source kind protectors mode rest
      (RangeVerification.advance tree prepared source kind protectors mode cursor
        (current.1, current.2, .Completed)) = _
    rw [step]
    exact ih next sizeNext (fun later mem => allowed later (.tail _ mem))

/-- Once authorization is established, form the updated map and diagnostics
by committing each initial snapshot's local result. A later cursor writing
the same position supersedes the earlier write, and the trace retains both. -/
def accessSuccessor (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) : BorrowTree × Array BorrowTreeLocationResult :=
  let source := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  let prepared := tree.locations.iterMut offset length
  let final := (List.range' 0 prepared.positions.size).foldl
    (commitPreparedSlot tree prepared source kind protectors mode) (prepared.state, #[])
  ({ tree with locations := final.1 }, final.2)

/-- The last cursor that writes a location determines its value. If no cursor
writes the position, the iterator's prepared map provides its value. -/
theorem accessSuccessor_locationAt (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (position : Nat) :
    let source := match provenance with
      | .concrete tag => tree.indexOfTag tag
      | .wildcard => none
    let prepared := tree.locations.iterMut offset length
    let final := accessSuccessor tree provenance offset length kind protectors mode
    final.1.locations.entries[position]?.map (·.data) =
      ((List.range' 0 prepared.positions.size).reverse.findSome?
        (preparedSlotLocationAt tree prepared source kind protectors mode position)).or
        (prepared.state.entries[position]?.map (·.data)) := by
  exact committed_locationAt tree _ _ kind protectors mode (_, #[]) rfl position _

theorem accessSuccessor_eq (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode)
    (allowed : AccessAuthorized tree provenance offset length kind protectors mode) :
    tree.performBorrowAccessRange provenance offset length kind protectors mode =
      let final := accessSuccessor tree provenance offset length kind protectors mode
      ⟨final.1, final.2, .Completed⟩ := by
  let source := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  let prepared := tree.locations.iterMut offset length
  have selectedSource : match (generalizing := false) provenance with
      | .concrete tag => ∃ index, source = some index ∧ tree.indexOfTag tag = some index
      | .wildcard => source = none := by
    have found := allowed.1
    cases provenance with
    | concrete tag =>
      cases indexed : tree.indexOfTag tag with
      | none => simp [indexed] at found
      | some index => exact ⟨index, indexed, indexed⟩
    | wildcard => rfl
  rw [rangeResult_eq_runSlots tree provenance offset length kind protectors mode prepared source
    selectedSource rfl allowed.2.1]
  rw [runSlots_eq_commit tree prepared source kind protectors mode _ (prepared.state, #[]) rfl]
  · rfl
  · intro cursor within
    exact allowed.2.2 cursor (by simpa [List.mem_range'] using within)

/-- A success postcondition is checked on the map and trace assembled from the
independent byte-range snapshots. -/
def accessSuccessPre (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : Array BorrowTreeLocationResult → BorrowTree → Prop) : Prop :=
  AccessAuthorized tree provenance offset length kind protectors mode ∧
    let final := accessSuccessor tree provenance offset length kind protectors mode
    post final.2 final.1

theorem accessSuccessPre_true_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :
    accessSuccessPre tree provenance offset length kind protectors mode (fun _ _ => True) ↔
      AccessAuthorized tree provenance offset length kind protectors mode := by
  simp [accessSuccessPre]

theorem wp_access_successPre_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : Array BorrowTreeLocationResult → BorrowTree → Prop) :
    wp (TreeBorrowsWP.access provenance offset length kind protectors mode) post (fun _ _ => False) tree ↔
      accessSuccessPre tree provenance offset length kind protectors mode post := by
  unfold accessSuccessPre
  simp only [wp, WP.wpTrans, TreeBorrowsWP.access]
  by_cases allowed : AccessAuthorized tree provenance offset length kind protectors mode
  · rw [accessSuccessor_eq tree provenance offset length kind protectors mode allowed]
    simp [allowed]
  · have failed : (tree.performBorrowAccessRange provenance offset length kind protectors mode).status ≠
        .Completed := fun complete => allowed
      ((rangeComplete_iff_authorized tree provenance offset length kind protectors mode).mp complete)
    generalize tree.performBorrowAccessRange provenance offset length kind protectors mode = result at failed ⊢
    rcases result with ⟨after, trace, status⟩
    cases status <;> simp_all

private theorem wp_pair_bind_iff {E S A B : Type} (read : EStateM E S A) (write : EStateM E S B) (tree : S)
    (post : A × B → S → Prop) :
    wp ((do
        let reads ← read
        let writes ← write
        pure (reads, writes)) : EStateM E S (A × B))
      post (fun _ _ => False) tree ↔
    wp read (fun reads after => wp write (fun writes => post (reads, writes))
      (fun _ _ => False) after) (fun _ _ => False) tree := by
  simp only [wp, WP.wpTrans, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases read tree with
  | error => rfl
  | ok a next =>
    simp only []
    cases write next <;> rfl

/-- A read followed by a write of arbitrary ranges uses the read's successful
snapshot commits to check the write. Both traces remain available to the post. -/
theorem wp_read_write_successPre_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (post : (Array BorrowTreeLocationResult × Array BorrowTreeLocationResult) → BorrowTree → Prop) :
    wp ((do
        let reads ← TreeBorrowsWP.access reader readOffset readLength .Read readTags readMode
        let writes ← TreeBorrowsWP.access writer writeOffset writeLength .Write writeTags writeMode
        pure (reads, writes)) :
        EStateM (BorrowTreeAccessStatus × Array BorrowTreeLocationResult)
          BorrowTree (Array BorrowTreeLocationResult × Array BorrowTreeLocationResult))
      post (fun _ _ => False) tree ↔
    accessSuccessPre tree reader readOffset readLength .Read readTags readMode (fun reads after =>
      accessSuccessPre after writer writeOffset writeLength .Write writeTags writeMode
        (fun writes => post (reads, writes))) := by
  simp only [wp_pair_bind_iff, wp_access_successPre_iff]

/-- The VC generated for an access with an arbitrary success postcondition
uses the same assembled successor and trace. -/
theorem accessPre_successPre_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : Array BorrowTreeLocationResult → BorrowTree → Prop) :
    TreeBorrowsWP.accessPre tree provenance offset length kind protectors mode
        (fun after trace => post trace after) (fun _ _ _ => False) ↔
      accessSuccessPre tree provenance offset length kind protectors mode post := by
  rw [← wp_access_successPre_iff, TreeBorrowsWP.accessPre_iff]
  simp only [wp, WP.wpTrans, TreeBorrowsWP.access]
  generalize tree.performBorrowAccessRange provenance offset length kind protectors mode = result
  rcases result with ⟨after, trace, status⟩
  cases status <;> rfl

/-- VC generation can discharge a whole ranged safety check by proving
authorization on the initial borrow tree. -/
theorem accessPre_succeeds_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :
    TreeBorrowsWP.accessPre tree provenance offset length kind protectors mode
        (fun _ _ => True) (fun _ _ _ => False) ↔
      AccessAuthorized tree provenance offset length kind protectors mode := by
  simpa [accessSuccessPre] using
    accessPre_successPre_iff tree provenance offset length kind protectors mode (fun _ _ => True)

/-- The same initial-tree condition rewrites the actual state-monad WP,
including when the access appears in another command's continuation. -/
theorem wp_access_succeeds_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :
    wp (TreeBorrowsWP.access provenance offset length kind protectors mode)
        (fun _ _ => True) (fun _ _ => False) tree ↔
      AccessAuthorized tree provenance offset length kind protectors mode := by
  simpa [accessSuccessPre] using
    wp_access_successPre_iff tree provenance offset length kind protectors mode (fun _ _ => True)

/-- Successful iterator preparation and authorization at each prepared slot
give a successful concrete or wildcard ranged access. -/
theorem rangeComplete (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex)
    (selected : match provenance with
      | .concrete tag => ∃ index, source = some index ∧ tree.indexOfTag tag = some index
      | .wildcard => source = none)
    (prepare : tree.locations.iterMut offset length = prepared)
    (okay : prepared.outcome = .ok ())
    (owned : SlotsAuthorized tree prepared source kind protectors mode) :
    (tree.performBorrowAccessRange provenance offset length kind protectors mode).status = .Completed := by
  apply (rangeComplete_iff tree provenance offset length kind protectors mode prepared source
    selected prepare okay).mpr
  intro cursor within
  obtain ⟨position, segment, positionAt, segmentAt, valid, complete⟩ := owned cursor within
  exact ⟨position, segment, positionAt, segmentAt, valid,
    (RangeVerification.locationContract_iff _ _ _ _ _ _ _ _).mp (by simp [complete])⟩

/-- Simplify ranged Tree Borrows success preconditions and location lookups.
The ordered commit fold remains available through the successor lemmas. -/
macro "miri_tree_range_wp" : tactic =>
  `(tactic| simp only [rangeComplete_iff_authorized, accessSuccessor_locationAt,
    accessSuccessPre_true_iff, accessPre_successPre_iff, wp_access_successPre_iff,
    wp_read_write_successPre_iff, wildcardRootsComplete_iff])

end Miri.Verification.TreeRangeAccess

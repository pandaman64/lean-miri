import Miri.Verification.TreeRangeOutcomeWP
import Miri.Verification.TreeReadWriteWP

/-! Recover the whole ranged access from permission facts at each iterator
position. The commits preserve the number of slots for the next cursor. -/
namespace Miri.Verification.TreeRangeAccess

open Miri.DataStructures Miri.TreeBorrows Miri.Memory Miri.ABI Std.WP

/-- Updating an existing position replaces only the stored data. -/
theorem setAtPos_eq {A : Type} (table : DedupRangeMap A) (position : Nat) (data : A) :
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
private theorem locationResultForSingleRoot (tree : BorrowTree) (location : LocationTree) (source root : UniIndex)
    (kind : AccessKind) (protectors : ProtectedTags) (range : ByteRange)
    (roots : tree.roots = #[root])
    (outcome : (tree.performNormalAccessAt location source kind protectors .VisitChildrenOfAccessed).outcome =
      .ok ())
    (normal : (tree.performNormalAccessAt location source kind protectors .VisitChildrenOfAccessed).access.status =
      .Completed)
    (rootIndex : UniIndex.ofNat?
      (tree.performNormalAccessAt location source kind protectors .VisitChildrenOfAccessed).access.root =
        some root) :
    tree.performTreeAccessAt location (some source) kind protectors .VisitChildrenOfAccessed range =
      let result := tree.performNormalAccessAt location source kind protectors .VisitChildrenOfAccessed
      ⟨result.location, some result.access, none⟩ := by
  unfold BorrowTree.performTreeAccessAt
  simp only [Id.run, outcome, normal, rootIndex, roots, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Array.size_singleton, List.range',
    List.forIn_cons, List.forIn_nil, Array.getElem?_singleton, bind, Bind.bind, pure, Pure.pure]
  simp [beq_iff_eq]

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
  rw [locationResultForSingleRoot tree location source root kind protectors range roots outcome normal rootIndex]

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
def commitSnapshot (prepared : IterMutResult LocationTree)
    (result : Nat → TreeLocationAccessAtResult) (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult)
    (cursor : Nat) : DedupRangeMap LocationTree × Array BorrowTreeLocationResult :=
  match prepared.positions[cursor]?, prepared.segments[cursor]? with
  | some position, some segment =>
    let access := result cursor
    ((current.1.setAtPos position access.location).state,
      current.2.push ⟨segment.range, access.normalAccess⟩)
  | _, _ => current

/-- The location a cursor writes to the given map position, if it writes
there. The permission transition uses that cursor's prepared snapshot. -/
def snapshotLocationAt (prepared : IterMutResult LocationTree)
    (result : Nat → TreeLocationAccessAtResult) (position cursor : Nat) : Option LocationTree :=
  if position < prepared.state.entries.size ∧ prepared.positions[cursor]? = some position then
    prepared.segments[cursor]?.map fun _ => (result cursor).location
  else none

private theorem commitSnapshot_locationAt (prepared : IterMutResult LocationTree)
    (result : Nat → TreeLocationAccessAtResult) (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult)
    (size : current.1.entries.size = prepared.state.entries.size) (position cursor : Nat) :
    let next := commitSnapshot prepared result current cursor
    next.1.entries.size = prepared.state.entries.size ∧
      next.1.entries[position]?.map (·.data) =
        (snapshotLocationAt prepared result position cursor).or
          (current.1.entries[position]?.map (·.data)) := by
  unfold commitSnapshot snapshotLocationAt
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

private theorem committedSnapshots_locationAt (prepared : IterMutResult LocationTree)
    (result : Nat → TreeLocationAccessAtResult) (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult)
    (size : current.1.entries.size = prepared.state.entries.size)
    (position : Nat) (cursors : List Nat) :
    let final := cursors.foldl (commitSnapshot prepared result) current
    final.1.entries[position]?.map (·.data) =
      (cursors.reverse.findSome? (snapshotLocationAt prepared result position)).or
        (current.1.entries[position]?.map (·.data)) := by
  induction cursors generalizing current with
  | nil => rfl
  | cons cursor rest ih =>
    obtain ⟨sameSize, updated⟩ := commitSnapshot_locationAt prepared result
      current size position cursor
    simp only [List.foldl_cons, ih _ sameSize, updated, List.reverse_cons, List.findSome?_append,
      List.findSome?_cons, List.findSome?_nil]
    rw [Option.or_assoc]
    cases snapshotLocationAt prepared result position cursor <;> rfl

private def runtimeSlotResult (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) : TreeLocationAccessAtResult :=
  match prepared.segments[cursor]? with
  | some segment => tree.performTreeAccessAt segment.data source kind protectors mode segment.range
  | none => ⟨default, none, none⟩

/-- Commit one prepared snapshot's local successor and append its trace. -/
def commitPreparedSlot (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :=
  commitSnapshot prepared (runtimeSlotResult tree prepared source kind protectors mode)

/-- The location a runtime cursor writes to the given map position, if any. -/
def preparedSlotLocationAt (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :=
  snapshotLocationAt prepared (runtimeSlotResult tree prepared source kind protectors mode)

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
      · simp [RangeVerification.advance, next, commitPreparedSlot, commitSnapshot, runtimeSlotResult, positionAt, segmentAt]
      · apply Prod.ext
        · simp [RangeVerification.advance, next, commitPreparedSlot, commitSnapshot, runtimeSlotResult, positionAt, segmentAt]
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
  exact committedSnapshots_locationAt _ _ (_, #[]) rfl position _

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

/-- A successful cursor retains the location, including cache updates, and the
normal traversal diagnostics supplied by its initial snapshot. -/
def SnapshotAuthorized (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (cursor : Nat) (retained : TreeLocationAccessAtResult) : Prop :=
  ∃ position segment, prepared.positions[cursor]? = some position ∧
    prepared.segments[cursor]? = some segment ∧ position < prepared.state.entries.size ∧
    RangeVerification.locationContract tree segment.data source kind protectors mode segment.range
      (fun result => result = retained ∧ result.status.getD .Completed = .Completed)

/-- Rebuild the range map and diagnostics from supplied, independently retained
cursor results. Range preparation still supplies all boundaries and positions. -/
def snapshotSuccessor (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (retained : Nat → TreeLocationAccessAtResult) : BorrowTree × Array BorrowTreeLocationResult :=
  let final := (List.range' 0 prepared.positions.size).foldl (commitSnapshot prepared retained)
    (prepared.state, #[])
  ({ tree with locations := final.1 }, final.2)

/-- Read just one committed location. If no cursor writes it, the lookup uses
the prepared map. Duplicate writes use the last matching cursor. -/
theorem snapshotSuccessor_locationAt (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (retained : Nat → TreeLocationAccessAtResult) (position : Nat) :
    (snapshotSuccessor tree prepared retained).1.locations.entries[position]?.map (·.data) =
      ((List.range' 0 prepared.positions.size).reverse.findSome?
        (snapshotLocationAt prepared retained position)).or
        (prepared.state.entries[position]?.map (·.data)) :=
  committedSnapshots_locationAt prepared retained (_, #[]) rfl position _

/-- Resolve provenance once and check the local contract on each initial
snapshot before using its retained state in the success postcondition. -/
def accessSnapshotPre (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : Array BorrowTreeLocationResult → BorrowTree → Prop) : Prop :=
  let source := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  let prepared := tree.locations.iterMut offset length
  (match provenance with
  | .concrete _ => source.isSome = true
  | .wildcard => True) ∧
    prepared.outcome = .ok () ∧
    ∃ retained, (∀ cursor, cursor < prepared.positions.size →
        SnapshotAuthorized tree prepared source kind protectors mode cursor (retained cursor)) ∧
      let final := snapshotSuccessor tree prepared retained
      post final.2 final.1

private theorem commitSnapshots_congr (prepared : IterMutResult LocationTree)
    (left right : Nat → TreeLocationAccessAtResult) (cursors : List Nat)
    (same : ∀ cursor ∈ cursors, left cursor = right cursor)
    (current : DedupRangeMap LocationTree × Array BorrowTreeLocationResult) :
    cursors.foldl (commitSnapshot prepared left) current =
      cursors.foldl (commitSnapshot prepared right) current := by
  induction cursors generalizing current with
  | nil => rfl
  | cons cursor rest ih =>
    simp only [List.foldl_cons]
    have step : commitSnapshot prepared left current cursor =
        commitSnapshot prepared right current cursor := by
      unfold commitSnapshot
      rw [same cursor (.head _)]
    rw [step]
    exact ih (fun i mem => same i (.tail _ mem)) _

theorem accessSnapshotPre_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : Array BorrowTreeLocationResult → BorrowTree → Prop) :
    accessSnapshotPre tree provenance offset length kind protectors mode post ↔
      accessSuccessPre tree provenance offset length kind protectors mode post := by
  let source := match provenance with
    | .concrete tag => tree.indexOfTag tag
    | .wildcard => none
  let prepared := tree.locations.iterMut offset length
  let runtime := runtimeSlotResult tree prepared source kind protectors mode
  constructor
  · rintro ⟨resolved, preparedOK, retained, accepted, postOK⟩
    change ∀ cursor, cursor < prepared.positions.size →
      SnapshotAuthorized tree prepared source kind protectors mode cursor (retained cursor) at accepted
    have localFacts (cursor : Nat) (inside : cursor < prepared.positions.size) :
        SlotAuthorized tree prepared source kind protectors mode cursor ∧
          runtime cursor = retained cursor := by
      obtain ⟨position, segment, atPosition, atSegment, within, contract⟩ := accepted cursor inside
      rw [← RangeVerification.locationContract_iff] at contract
      refine ⟨⟨position, segment, atPosition, atSegment, within, ?_⟩, ?_⟩
      · exact (RangeVerification.locationContract_iff ..).mp contract.2
      · simpa only [runtime, runtimeSlotResult, atSegment] using contract.1
    refine ⟨⟨resolved, preparedOK, fun cursor inside => (localFacts cursor inside).1⟩, ?_⟩
    change post (snapshotSuccessor tree prepared runtime).2 (snapshotSuccessor tree prepared runtime).1
    have same := commitSnapshots_congr prepared runtime retained (List.range' 0 prepared.positions.size)
      (fun i mem => (localFacts i (by simpa [List.mem_range'] using mem)).2) (prepared.state, #[])
    simpa only [snapshotSuccessor, same] using postOK
  · rintro ⟨⟨resolved, preparedOK, accepted⟩, postOK⟩
    change ∀ cursor, cursor < prepared.positions.size →
      SlotAuthorized tree prepared source kind protectors mode cursor at accepted
    refine ⟨resolved, preparedOK, runtime, ?_, postOK⟩
    change ∀ cursor, cursor < prepared.positions.size →
      SnapshotAuthorized tree prepared source kind protectors mode cursor (runtime cursor)
    intro cursor inside
    obtain ⟨position, segment, atPosition, atSegment, within, contract⟩ := accepted cursor inside
    refine ⟨position, segment, atPosition, atSegment, within, ?_⟩
    rw [← RangeVerification.locationContract_iff] at contract ⊢
    exact ⟨by simp only [runtime, runtimeSlotResult, atSegment], contract⟩

/-- Authorized retained snapshots determine the exact successful range result. -/
theorem snapshotSuccessor_eq (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (retained : Nat → TreeLocationAccessAtResult)
    (resolved : match provenance with
      | .concrete tag => (tree.indexOfTag tag).isSome = true
      | .wildcard => True)
    (preparedOK : (tree.locations.iterMut offset length).outcome = .ok ())
    (accepted : let source := match provenance with
      | .concrete tag => tree.indexOfTag tag
      | .wildcard => none
      let prepared := tree.locations.iterMut offset length
      ∀ cursor, cursor < prepared.positions.size →
        SnapshotAuthorized tree prepared source kind protectors mode cursor (retained cursor)) :
    tree.performBorrowAccessRange provenance offset length kind protectors mode =
      let final := snapshotSuccessor tree (tree.locations.iterMut offset length) retained
      ⟨final.1, final.2, .Completed⟩ := by
  let final := snapshotSuccessor tree (tree.locations.iterMut offset length) retained
  obtain ⟨allowed, sameTree, sameTrace⟩ := (accessSnapshotPre_iff tree provenance offset length
    kind protectors mode (fun trace state => state = final.1 ∧ trace = final.2)).mp
      ⟨by cases provenance <;> exact resolved, preparedOK, retained, by cases provenance <;> exact accepted, rfl, rfl⟩
  rw [accessSuccessor_eq tree provenance offset length kind protectors mode allowed]
  simp only [sameTree, sameTrace, final]

/-- A single success-only access can expose the same retained snapshot facts. -/
theorem wp_access_snapshotPre_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (post : Array BorrowTreeLocationResult → BorrowTree → Prop) :
    wp (TreeBorrowsWP.access provenance offset length kind protectors mode) post (fun _ _ => False) tree ↔
      accessSnapshotPre tree provenance offset length kind protectors mode post := by
  rw [wp_access_successPre_iff, accessSnapshotPre_iff]

/-- A range whose postcondition discards its resulting state only needs the
independent authorization facts for its prepared snapshots. -/
theorem accessSnapshotPre_true_iff (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length : Size) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) :
    accessSnapshotPre tree provenance offset length kind protectors mode (fun _ _ => True) ↔
      AccessAuthorized tree provenance offset length kind protectors mode := by
  rw [accessSnapshotPre_iff, accessSuccessPre_true_iff]

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
  simp only [TreeRangeOutcomeWP.wp_pair_bind_iff, wp_access_successPre_iff]

/-- The read's initial cursor contracts supply the locations used to prepare
the write, and the write's own cursor contracts supply its final state. -/
def readWriteSnapshotPre (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readOffset readLength writeOffset writeLength : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode)
    (post : (Array BorrowTreeLocationResult × Array BorrowTreeLocationResult) → BorrowTree → Prop) : Prop :=
  accessSnapshotPre tree reader readOffset readLength .Read readTags readMode (fun reads after =>
    accessSnapshotPre after writer writeOffset writeLength .Write writeTags writeMode
      (fun writes => post (reads, writes)))

theorem wp_read_write_snapshotPre_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
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
    readWriteSnapshotPre tree reader writer readOffset readLength writeOffset writeLength readTags writeTags
      readMode writeMode post := by
  rw [wp_read_write_successPre_iff, readWriteSnapshotPre, accessSnapshotPre_iff]
  simp only [accessSnapshotPre_iff]

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

private theorem uniformAccess_eq (tree : BorrowTree) (location : LocationTree)
    (size : Size) (positive : size.bytes ≠ 0)
    (uniform : tree.locations = DedupRangeMap.new size location)
    (tag : BorTag) (index : UniIndex) (found : tree.indexOfTag tag = some index)
    (kind : AccessKind) (tags : ProtectedTags) :
    tree.performBorrowAccessRange (.concrete tag) Size.ZERO size kind tags .VisitChildrenOfAccessed =
      let range : ByteRange := ⟨0, size.bytes⟩
      let result := tree.performTreeAccessAt location (some index) kind tags .VisitChildrenOfAccessed range
      ⟨{ tree with locations := DedupRangeMap.new size result.location }, #[⟨range, result.normalAccess⟩],
        result.status.getD .Completed⟩ := by
  let prepared := tree.locations.iterMut Size.ZERO size
  have prep : prepared = ⟨DedupRangeMap.new size location, #[0], #[⟨⟨0, size.bytes⟩, location⟩], .ok ()⟩ := by
    rw [show prepared = tree.locations.iterMut Size.ZERO size from rfl, uniform,
      DedupRangeMap.iterMut_new_full size location positive]
  have okay : prepared.outcome = .ok () := by simp only [prep]
  rw [rangeResult_eq_runSlots tree (.concrete tag) Size.ZERO size kind tags .VisitChildrenOfAccessed
    prepared (some index) ⟨index, rfl, found⟩ rfl okay]
  simp [prep, runSlots, RangeVerification.advance, setAtPos_eq, DedupRangeMap.new, positive]

private theorem localComplete_requires_normal (tree : BorrowTree) (location : LocationTree)
    (source : UniIndex) (kind : AccessKind) (tags : ProtectedTags) (range : ByteRange)
    (done : (tree.performTreeAccessAt location (some source) kind tags .VisitChildrenOfAccessed range).status.getD
      .Completed = .Completed) :
    (tree.performNormalAccessAt location source kind tags .VisitChildrenOfAccessed).access.status = .Completed := by
  by_cases complete : (tree.performNormalAccessAt location source kind tags
      .VisitChildrenOfAccessed).access.status = .Completed
  · exact complete
  · unfold performTreeAccessAt at done
    cases outcome : (tree.performNormalAccessAt location source kind tags .VisitChildrenOfAccessed).outcome
    · simp [Id.run, outcome, pure, Pure.pure] at done
    · simp [Id.run, outcome, complete, pure, Pure.pure] at done

private theorem processEvents_root (view : Tree.NormalTreeState) (root : Nat) (kind : AccessKind)
    (events : List Tree.TraversalEvent) : (view.processEvents root kind events).root = root := by
  induction events generalizing view with
  | nil => rfl
  | cons event rest ih =>
    simp only [Tree.NormalTreeState.processEvents]
    repeat' first | rfl | exact ih _ | split

/-- A normal location access selects its root from the source's ancestor
path. Permission and cache changes have no effect on this selection. -/
theorem normalLocationAccess_root (tree : BorrowTree) (location : LocationTree)
    (source : UniIndex) (kind : AccessKind) (tags : ProtectedTags) :
    (tree.performNormalAccessAt location source kind tags .VisitChildrenOfAccessed).access.root =
      ((tree.normalView location tags).topology.ancestorPath source.toNat).getLast! := by
  rw [TreeVisitWP.normal_access_result]
  exact processEvents_root _ _ _ _

/-- For a nonempty uniform location in a single-root tree, a full-range read
and write with the same protector map can be reduced to initial normal events.
The sources must reach the unique root. Cache checks are required only
for a completed normal visitor. The read writeback must preserve its normal
projection for the write. -/
theorem wp_uniform_read_write_normal_iff (tree : BorrowTree) (location : LocationTree)
    (size : Size) (positive : size.bytes ≠ 0)
    (uniform : tree.locations = DedupRangeMap.new size location)
    (reader writer : BorTag) (readIndex writeIndex root : UniIndex)
    (readerAt : tree.indexOfTag reader = some readIndex)
    (writerAt : tree.indexOfTag writer = some writeIndex)
    (roots : tree.roots = #[root]) (tags : ProtectedTags)
    (readerRoot : UniIndex.ofNat?
      (((tree.normalView location tags).topology.ancestorPath readIndex.toNat).getLast!) = some root)
    (writerRoot : UniIndex.ofNat?
      (((tree.normalView location tags).topology.ancestorPath writeIndex.toNat).getLast!) = some root)
    (readCache :
      let read := tree.performNormalAccessAt location readIndex .Read tags .VisitChildrenOfAccessed
      read.access.status = .Completed → read.outcome = .ok ())
    (writeCache :
      let read := tree.performNormalAccessAt location readIndex .Read tags .VisitChildrenOfAccessed
      let write := tree.performNormalAccessAt read.location writeIndex .Write tags .VisitChildrenOfAccessed
      write.access.status = .Completed → write.outcome = .ok ())
    (readProjection :
      let read := tree.performNormalAccessAt location readIndex .Read tags .VisitChildrenOfAccessed
      read.access.status = .Completed → tree.normalView read.location tags = read.access.tree)
    (readOnce : let view := tree.normalView location tags
      ((view.topology.traverseWithSkip readIndex.toNat .VisitChildrenOfAccessed
        (view.shouldSkipForeignNode .Read)).2.map (·.node)).Nodup)
    (writeOnce : let view := tree.normalView location tags
      let reads := (view.topology.traverseWithSkip readIndex.toNat .VisitChildrenOfAccessed
        (view.shouldSkipForeignNode .Read)).2
      ((TreeVisitWP.writeScheduleAfterRead view reads writeIndex.toNat
        .VisitChildrenOfAccessed).2.map (·.node)).Nodup) :
    wp ((do
        let reads ← TreeBorrowsWP.access (.concrete reader) Size.ZERO size .Read tags .VisitChildrenOfAccessed
        let writes ← TreeBorrowsWP.access (.concrete writer) Size.ZERO size .Write tags .VisitChildrenOfAccessed
        pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
          (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace))
      (fun _ _ => True) (fun _ _ => False) tree ↔
    let view := tree.normalView location tags
    let reads := (view.topology.traverseWithSkip readIndex.toNat .VisitChildrenOfAccessed
      (view.shouldSkipForeignNode .Read)).2
    TreeVisitWP.EventsReadWriteAllowed view reads
      (TreeVisitWP.writeScheduleAfterRead view reads writeIndex.toNat .VisitChildrenOfAccessed).2 := by
  let reads := tree.performNormalAccessAt location readIndex .Read tags .VisitChildrenOfAccessed
  rw [← TreeVisitWP.normal_read_write_pre_iff _ _ _ _ _ readOnce writeOnce, TreeRangeOutcomeWP.wp_pair_bind_iff]
  simp only [Tree.NormalTreeState.accessPre_iff, wp, WP.wpTrans, TreeBorrowsWP.access,
    uniformAccess_eq tree location size positive uniform reader readIndex readerAt]
  have readAccess : reads.access = (tree.normalView location tags).performAccess readIndex.toNat
      .Read .VisitChildrenOfAccessed := rfl
  rw [← readAccess]
  by_cases complete : reads.access.status = .Completed
  · have rootAt : UniIndex.ofNat? reads.access.root = some root :=
      (congrArg UniIndex.ofNat? (normalLocationAccess_root tree location readIndex .Read tags)).trans readerRoot
    rw [locationResultForSingleRoot tree location readIndex root .Read tags ⟨0, size.bytes⟩
      roots (readCache complete) complete rootAt]
    let after := { tree with locations := DedupRangeMap.new size reads.location }
    have writerAfter : after.indexOfTag writer = some writeIndex := writerAt
    have projection : after.normalView reads.location tags = reads.access.tree := readProjection complete
    simp only [Option.getD_none, complete, true_and]
    rw [uniformAccess_eq after reads.location size positive rfl writer writeIndex writerAfter]
    dsimp only
    let writes := after.performNormalAccessAt reads.location writeIndex .Write tags .VisitChildrenOfAccessed
    have writeStatus : writes.access =
        reads.access.tree.performAccess writeIndex.toNat .Write .VisitChildrenOfAccessed := by
      rw [TreeVisitWP.normal_access_result, projection]
    rw [← writeStatus]
    by_cases writeDone : writes.access.status = .Completed
    · have writeRoot : UniIndex.ofNat? writes.access.root = some root :=
        (congrArg UniIndex.ofNat? (normalLocationAccess_root after reads.location writeIndex .Write tags)).trans
          writerRoot
      rw [locationResultForSingleRoot after reads.location writeIndex root .Write tags ⟨0, size.bytes⟩
        roots (writeCache writeDone) writeDone writeRoot]
      simp only [Option.getD_none, writeDone]
    · have failed : (after.performTreeAccessAt reads.location (some writeIndex) .Write tags
          .VisitChildrenOfAccessed ⟨0, size.bytes⟩).status.getD .Completed ≠ .Completed :=
        fun done => writeDone (localComplete_requires_normal after reads.location writeIndex .Write tags ⟨0, size.bytes⟩ done)
      generalize (after.performTreeAccessAt reads.location (some writeIndex) .Write tags
        .VisitChildrenOfAccessed ⟨0, size.bytes⟩).status.getD .Completed = status at failed ⊢
      cases status <;> simp_all
  · have failed : (tree.performTreeAccessAt location (some readIndex) .Read tags
        .VisitChildrenOfAccessed ⟨0, size.bytes⟩).status.getD .Completed ≠ .Completed :=
      fun done => complete (localComplete_requires_normal tree location readIndex .Read tags ⟨0, size.bytes⟩ done)
    generalize (tree.performTreeAccessAt location (some readIndex) .Read tags
      .VisitChildrenOfAccessed ⟨0, size.bytes⟩).status.getD .Completed = status at failed ⊢
    cases status <;> simp_all

/-- Reduce paired ranged accesses through their exact ordered location contracts. -/
macro "miri_tree_range_wp" : tactic =>
  `(tactic| simp only [TreeRangeOutcomeWP.wp_read_write_outcomePre_iff,
    rangeComplete_iff_authorized, accessPre_succeeds_iff,
    wp_access_succeeds_iff, accessPre_successPre_iff, wp_access_successPre_iff,
    wildcardRootsComplete_iff])

/-- Use the executable successor formulation for compatibility with existing proofs. -/
macro "miri_tree_range_wp" "successor" : tactic =>
  `(tactic| simp only [rangeComplete_iff_authorized, accessSuccessor_locationAt,
    accessPre_succeeds_iff, wp_access_succeeds_iff, accessPre_successPre_iff, wp_access_successPre_iff,
    wp_read_write_successPre_iff, wildcardRootsComplete_iff])

/-- Expose independent cursor results for pointwise successor proofs. -/
macro "miri_tree_range_wp" "snapshots" : tactic =>
  `(tactic| simp only [wp_read_write_snapshotPre_iff, wp_access_snapshotPre_iff, snapshotSuccessor_locationAt,
    readWriteSnapshotPre, accessSnapshotPre_true_iff])

end Miri.Verification.TreeRangeAccess

import Miri.Verification.TreeBorrowsWP

/-! Recover the whole ranged access from permission facts at each iterator
position. The commits preserve the number of slots for the next cursor. -/
namespace Miri.Verification.TreeRangeAccess

open Miri.DataStructures Miri.TreeBorrows Miri.Memory Miri.ABI

private theorem setAtPos_ok {A : Type} (table : DedupRangeMap A) (position : Nat) (data : A)
    (inside : position < table.entries.size) :
    (table.setAtPos position data).outcome = .ok () ∧
      (table.setAtPos position data).state.entries.size = table.entries.size := by
  have changed : table.setAtPos position data =
      ⟨⟨table.entries.set position {table.entries[position] with data} inside⟩, .ok ()⟩ := by
    unfold DedupRangeMap.setAtPos
    change ((match (if ok : position < table.entries.size then some table.entries[position] else none) with
      | none => ⟨table, .error (.indexOutOfBounds position table.entries.size)⟩
      | some segment =>
        match (if ok : position < table.entries.size then
                  Except.ok (table.entries.set position {segment with data} ok)
                else Except.error (.indexOutOfBounds position table.entries.size)) with
        | .error error => ⟨table, .error error⟩
        | .ok entries => ⟨⟨entries⟩, .ok ()⟩) : DedupMutationResult (DedupRangeMap A)) = _
    simp [inside]
  simp [changed]

open BorrowTree
private theorem run_preserves {A S : Type} (items : List A)
    (action : A → S → Id (ForInStep S)) (keep : S → Prop)
    (step : ∀ item ∈ items, ∀ state, keep state →
      ∃ next, action item state = .yield next ∧ keep next)
    (initial : S) (ready : keep initial) :
    keep (forIn items initial action : Id S) := by
  induction items generalizing initial with
  | nil => exact ready
  | cons head tail ih =>
    obtain ⟨next, taken, valid⟩ := step head (by simp) initial ready
    rw [List.forIn_cons, taken]
    change keep (forIn tail next action : Id S)
    exact ih (fun item mem => step item (.tail head mem)) next valid


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

private theorem runSlots (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protectors : ProtectedTags)
    (mode : Tree.ChildrenVisitMode)
    (owned : SlotsAuthorized tree prepared source kind protectors mode) :
    (forIn (List.range' 0 prepared.positions.size) (prepared.state, #[], .Completed)
      (fun cursor progress => pure (ForInStep.yield
        (RangeVerification.advance tree prepared source kind protectors mode cursor progress))) :
      Id RangeVerification.Progress).2.2 = .Completed := by
  let keep (progress : RangeVerification.Progress) := progress.2.2 = .Completed ∧
    progress.1.entries.size = prepared.state.entries.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ progress, keep progress →
      ∃ actual, (pure (ForInStep.yield
        (RangeVerification.advance tree prepared source kind protectors mode cursor progress)) :
        Id (ForInStep RangeVerification.Progress)) = .yield actual ∧ keep actual := by
    intro cursor member progress valid
    have atCursor : cursor < prepared.positions.size := by
      simpa [List.mem_range'] using member
    obtain ⟨position, segment, positionAt, segmentAt, validPosition, complete⟩ := owned cursor atCursor
    have checked : position < progress.1.entries.size := by
      rw [valid.2]
      exact validPosition
    have placed := setAtPos_ok progress.1 position
      (tree.performTreeAccessAt segment.data source kind protectors mode segment.range).location checked
    refine ⟨_, rfl, ?_⟩
    simpa only [keep, RangeVerification.advance, valid.1, beq_self_eq_true, ↓reduceIte,
      positionAt, segmentAt, placed.1, complete, Option.getD_none, true_and] using
      placed.2.trans valid.2
  have result := run_preserves (List.range' 0 prepared.positions.size)
    (fun cursor progress => pure (ForInStep.yield
      (RangeVerification.advance tree prepared source kind protectors mode cursor progress)))
    keep step (prepared.state, #[], .Completed) ⟨rfl, rfl⟩
  exact result.1


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
  have complete := runSlots tree prepared source kind protectors mode owned
  unfold performBorrowAccessRange
  cases provenance with
  | concrete tag =>
    obtain ⟨index, rfl, found⟩ := selected
    simp only [Id.run, found, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, prepare, okay,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one, RangeVerification.cursor_equation]
    exact complete
  | wildcard =>
    subst source
    simp only [Id.run, prepare, okay, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, RangeVerification.cursor_equation]
    exact complete

end Miri.Verification.TreeRangeAccess

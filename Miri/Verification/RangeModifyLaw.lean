import Miri.DataStructures.DedupRangeMap
import Lean

namespace Miri.Verification.RangeModifyLaw

open Miri.ABI Miri.DataStructures
open Lean Elab Tactic

/-- A range map carries the relation at each represented byte, independent of
how equal adjacent values have been deduplicated. -/
def EachByte {A : Type} (map : DedupRangeMap A) (holds : UInt64 → A → Prop) : Prop :=
  ∀ point position (within : position < map.entries.size),
    map.entries[position].range.start ≤ point → point < map.entries[position].range.stop →
      holds point map.entries[position].data

private theorem replace_preserves {A : Type} (map : DedupRangeMap A) (holds : UInt64 → A → Prop)
    (position : Nat) (within : position < map.entries.size) (modify : ByteRange → A → A)
    (preserve : ∀ point value, map.entries[position].range.start ≤ point →
      point < map.entries[position].range.stop → holds point value →
      holds point (modify map.entries[position].range value))
    (ready : EachByte map holds) :
    let next := ⟨map.entries.set position
      {map.entries[position] with data := modify map.entries[position].range map.entries[position].data} within⟩
    EachByte next holds := by
  dsimp only
  intro point query valid lo hi
  have oldBound : query < map.entries.size := by simpa using valid
  by_cases same : position = query
  · subst query
    simp only [Array.getElem_set_self] at lo hi ⊢
    exact preserve _ _ lo hi (ready point position within lo hi)
  · simp only [Array.getElem_set, same] at lo hi ⊢
    exact ready point query oldBound lo hi

private theorem replace_ranges {A : Type} (map : DedupRangeMap A)
    (position : Nat) (within : position < map.entries.size) (data : A) :
    let changed := map.entries.set position { map.entries[position] with data } within
    changed.map (·.range) = map.entries.map (·.range) := by
  apply Array.ext
  · simp
  · intro query left right
    simp only [Array.getElem_map]
    by_cases same : position = query
    · subst query
      simp
    · simp [Array.getElem_set, same]

private theorem loop_invariant {A S : Type} (items : List A) (scan : A → S → Id (ForInStep S))
    (keep : S → Prop) (initial : S) (ready : keep initial)
    (advance : ∀ item ∈ items, ∀ state, keep state →
      ∃ next, scan item state = .yield next ∧ keep next) :
    keep (forIn items initial scan : Id S) := by
  induction items generalizing initial with
  | nil => exact ready
  | cons item rest ih =>
    obtain ⟨next, step, still⟩ := advance item List.mem_cons_self initial ready
    rw [List.forIn_cons, step]
    exact ih next still (fun item member => advance item (.tail _ member))

elab "abstract_range_modifier" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn.forIn)
      | throwError "range modifier loop not found"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan, goal) ← goal.intro1P
    let target ← goal.getType
    return [← goal.change (target.replace fun expr => if expr == body then some (mkFVar scan) else none)]

/-- Once iterator preparation has supplied the checked positions and byte
origins, actual `modifyRange` preserves a pointwise invariant whenever its
pure callback preserves that invariant. -/
theorem modifier_preserves_where {A : Type} [DecidableEq A]
    (map : DedupRangeMap A) (offset length : Size) (modify : ByteRange → A → A)
    (holds : UInt64 → A → Prop)
    (prepared : IterMutResult A) (prepare : map.iterMut offset length = prepared)
    (okay : prepared.outcome = .ok ())
    (positions : ∀ position ∈ prepared.positions.toList, position < prepared.state.entries.size)
    (scope : ByteRange → Prop)
    (selected : ∀ position (member : position ∈ prepared.positions.toList),
      scope (prepared.state.entries[position]'(positions position member)).range)
    (ready : EachByte prepared.state holds)
    (preserve : ∀ range point value, scope range → range.start ≤ point → point < range.stop →
      holds point value → holds point (modify range value)) :
    (map.modifyRange offset length modify).outcome = .ok () ∧
      EachByte (map.modifyRange offset length modify).state holds ∧
      (map.modifyRange offset length modify).state.entries.map (·.range) =
        prepared.state.entries.map (·.range) := by
  have prepare' : map.iterMutWithClone offset length id = prepared := prepare
  unfold DedupRangeMap.modifyRange DedupRangeMap.modifyRangeWithClone
  simp only [Id.run, prepare', okay, Bind.bind, Pure.pure, ← Array.forIn_toList]
  abstract_range_modifier
  let keep (state : Option (IterMutResult A) × DedupRangeMap A × Array (RangeMapSegment A)) :=
    state.1 = none ∧ state.2.1.entries.size = prepared.state.entries.size ∧ EachByte state.2.1 holds ∧
      state.2.1.entries.map (·.range) = prepared.state.entries.map (·.range)
  have step : ∀ position ∈ prepared.positions.toList, ∀ state, keep state →
      ∃ next, scan position state = .yield next ∧ keep next := by
    intro position member state stable
    obtain ⟨returned, current, segments⟩ := state
    obtain ⟨untouched, size, valid, ranges⟩ := stable
    simp only at untouched size valid ranges
    subst returned
    have within : position < current.entries.size := size.symm ▸ positions position member
    let segment := current.entries[position]
    let updated : RangeMapSegment A := {segment with data := modify segment.range segment.data}
    let next : DedupRangeMap A := ⟨current.entries.set position updated within⟩
    refine ⟨(none, next, segments.push updated), ?_, ?_⟩
    · simp only [scan]
      -- The bounds are shared by the source's segment read and checked write-back.
      change ((match (if found : position < current.entries.size then some current.entries[position] else none) with
        | none => .done (some ⟨current, prepared.positions, segments,
            .error (.indexOutOfBounds position current.entries.size)⟩, current, segments)
        | some entry =>
          match (if found : position < current.entries.size then
            Except.ok (current.entries.set position {entry with data := modify entry.range entry.data} found)
            else Except.error (.indexOutOfBounds position current.entries.size)) with
            | .error error => .done (some ⟨current, prepared.positions, segments, .error error⟩, current, segments)
            | .ok entries => .yield (none, ⟨entries⟩, segments.push {entry with data := modify entry.range entry.data})) :
          Id (ForInStep (Option (IterMutResult A) × DedupRangeMap A × Array (RangeMapSegment A)))) = _
      simp only [within, ↓reduceDIte, segment, updated, next]
    · have same : current.entries[position].range =
          (prepared.state.entries[position]'(positions position member)).range := by
        have matched := congrArg (fun entries : Array ByteRange => entries[position]?) ranges
        simpa only [Array.getElem?_map, Array.getElem?_eq_getElem within,
          Array.getElem?_eq_getElem (positions position member), Option.map_some, Option.some.injEq] using matched
      have inScope := same.symm ▸ selected position member
      exact ⟨rfl, by simpa [next] using size,
        replace_preserves current holds position within modify
          (fun point value start stop right => preserve _ point value inScope start stop right) valid,
        (replace_ranges current position within updated.data).trans ranges⟩
  have kept := loop_invariant prepared.positions.toList scan keep (none, prepared.state, #[])
    ⟨rfl, rfl, ready, rfl⟩ step
  dsimp only [keep] at kept
  rw [kept.1]
  exact ⟨rfl, kept.2.2⟩

/-- A callback law that applies to every range is a special case of the
law restricted to the iterator's selected ranges. -/
theorem modifier_preserves {A : Type} [DecidableEq A]
    (map : DedupRangeMap A) (offset length : Size) (modify : ByteRange → A → A)
    (holds : UInt64 → A → Prop)
    (prepared : IterMutResult A) (prepare : map.iterMut offset length = prepared)
    (okay : prepared.outcome = .ok ())
    (positions : ∀ position ∈ prepared.positions.toList, position < prepared.state.entries.size)
    (ready : EachByte prepared.state holds)
    (preserve : ∀ range point value, range.start ≤ point → point < range.stop →
      holds point value → holds point (modify range value)) :
    (map.modifyRange offset length modify).outcome = .ok () ∧
      EachByte (map.modifyRange offset length modify).state holds ∧
      (map.modifyRange offset length modify).state.entries.map (·.range) =
        prepared.state.entries.map (·.range) :=
  modifier_preserves_where map offset length modify holds prepared prepare okay positions
    (fun _ => True) (fun _ _ => trivial) ready
    (fun range point value _ => preserve range point value)

end Miri.Verification.RangeModifyLaw

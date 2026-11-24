import Lean
import Miri.ABI.Size

/-! A checked port of Miri's `DedupRangeMap<T>` range partition. -/

namespace Miri.DataStructures
open Miri.ABI

/-- A half-open byte interval, matching `ops::Range<u64>`. -/
structure ByteRange where
  start : UInt64
  stop : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- One range and its associated value. -/
structure RangeMapSegment (α : Type) where
  range : ByteRange
  data : α
  deriving DecidableEq, Repr

/-- Explicit equivalents of the source's checked-size failures and panics. -/
inductive DedupRangeMapError where
  | sizeError (error : SizeError)
  | offsetNotCovered (offset mapSize : UInt64)
  | iterationPastMap (endOffset mapSize : UInt64)
  | indexOutOfBounds (index length : Nat)
  | splitOutsideSegment (index : Nat) (offset start stop : UInt64)
  | mergeRequiresAdjacent (previousEnd nextStart : UInt64)
  deriving DecidableEq, Repr

instance : ToString DedupRangeMapError where
  toString
    | .sizeError error => toString error
    | .offsetNotCovered offset mapSize =>
        s!"DedupRangeMap offset {offset} is not covered by map of size {mapSize}"
    | .iterationPastMap endOffset mapSize =>
        s!"DedupRangeMap iteration ends at {endOffset}, beyond map size {mapSize}"
    | .indexOutOfBounds index length =>
        s!"DedupRangeMap index {index} is outside {length} segments"
    | .splitOutsideSegment index offset start stop =>
        s!"DedupRangeMap split at {offset} is outside segment {index} [{start}..{stop})"
    | .mergeRequiresAdjacent previousEnd nextStart =>
        s!"DedupRangeMap cannot merge nonadjacent segments ending at {previousEnd} and starting at {nextStart}"

/-- The source's ordered vector of half-open intervals. -/
structure DedupRangeMap (α : Type) where
  entries : Array (RangeMapSegment α) := #[]
  deriving DecidableEq, Repr, Inhabited

/-- Mutations carry state even on failure, preserving operations performed before
the corresponding Rust panic. -/
structure DedupMutationResult (α : Type) where
  state : α
  outcome : Except DedupRangeMapError Unit

/-- Result of preparing a source `iter_mut` call. The map already contains the
source's start/end splits and opportunistic merges; positions identify exactly
the entries borrowed by the returned Rust iterator. -/
structure IterMutResult (α : Type) where
  state : DedupRangeMap α
  positions : Array Nat
  segments : Array (RangeMapSegment α)
  outcome : Except DedupRangeMapError Unit

/-- Membership in a half-open stored or requested interval. -/
def ByteRange.Contains (range : ByteRange) (byte : UInt64) : Prop :=
  range.start ≤ byte ∧ byte < range.stop

/-- The map carries this value at the given byte. -/
def DedupRangeMap.MapAt (map : DedupRangeMap α) (byte : UInt64) (data : α) : Prop :=
  ∃ (position : Nat) (segment : RangeMapSegment α), map.entries[position]? = some segment ∧
    segment.range.Contains byte ∧ segment.data = data

/-- A byte-level description of iterator preparation. Each returned cursor
names a valid entry within the request, and every entry covering a requested
byte is selected. Splitting and merging preserve the represented byte values. -/
structure IterMutResult.PreparedFor (prepared : IterMutResult α) (range : ByteRange)
    (contents : UInt64 → α → Prop) : Prop where
  outcome : prepared.outcome = .ok ()
  partition : ∀ byte data, prepared.state.MapAt byte data ↔ contents byte data
  slot : ∀ cursor, cursor < prepared.positions.size →
    ∃ (position : Nat) (segment : RangeMapSegment α), prepared.positions[cursor]? = some position ∧
      prepared.segments[cursor]? = some segment ∧ prepared.state.entries[position]? = some segment ∧
      (∃ byte, segment.range.Contains byte) ∧
      (∀ byte, segment.range.Contains byte → range.Contains byte)
  coverage : ∀ (position : Nat) (segment : RangeMapSegment α) (byte : UInt64), prepared.state.entries[position]? = some segment →
    segment.range.Contains byte → range.Contains byte →
    ∃ cursor, cursor < prepared.positions.size ∧ prepared.positions[cursor]? = some position

namespace DedupRangeMap

private def segmentAt? (entries : Array (RangeMapSegment α)) (index : Nat) :
    Option (RangeMapSegment α) :=
  if h : index < entries.size then some entries[index] else none

private def updateAt (entries : Array (RangeMapSegment α)) (index : Nat)
    (segment : RangeMapSegment α) : Except DedupRangeMapError (Array (RangeMapSegment α)) :=
  if h : index < entries.size then
    return entries.set index segment h
  else
    throw (.indexOutOfBounds index entries.size)

private def checkedEnd (offset length : UInt64) : Except DedupRangeMapError UInt64 := do
  let finish ← (Size.add (.ofBytes offset) (.ofBytes length)).mapError DedupRangeMapError.sizeError
  return finish.bytes

def new (size : Size) (initial : α) : DedupRangeMap α :=
  if size.bytes == 0 then
    ⟨#[]⟩
  else
    ⟨#[⟨⟨0, size.bytes⟩, initial⟩]⟩

/-- The source reports the last interval's end, or zero for an empty map. -/
def size (map : DedupRangeMap α) : Size :=
  match map.entries.back? with
  | none => Size.ZERO
  | some segment => Size.ofBytes segment.range.stop

def isEmpty (map : DedupRangeMap α) : Bool := map.entries.isEmpty

def length (map : DedupRangeMap α) : Nat := map.entries.size

/-- Binary search using the source's ordering comparator; unlike
`RangeObjectMap.findOffset`, the source unwraps the result and panics if the
offset is not covered. -/
private def findOffset (map : DedupRangeMap α) (offset : UInt64) :
    Except DedupRangeMapError Nat := Id.run do
  let mut low := 0
  let mut high := map.entries.size
  let mut answer : Option (Except DedupRangeMapError Nat) := none
  while low < high && answer.isNone do
    let middle := low + (high - low) / 2
    match segmentAt? map.entries middle with
    | none => answer := some (.error (.indexOutOfBounds middle map.entries.size))
    | some segment =>
        if offset < segment.range.start then
          high := middle
        else if offset ≥ segment.range.stop then
          low := middle + 1
        else
          answer := some (.ok middle)
  match answer with
  | some result => return result
  | none => return .error (.offsetNotCovered offset map.size.bytes)

/-- Read-only iteration returns complete stored segments intersecting the
requested interval; edge segments are not split or clipped. -/
def iter (map : DedupRangeMap α) (offset len : Size) :
    Except DedupRangeMapError (Array (RangeMapSegment α)) := do
  let offsetBytes := offset.bytes
  let lenBytes := len.bytes
  let first ←
    if lenBytes == 0 then pure 0 else findOffset map offsetBytes
  let finish ← checkedEnd offsetBytes lenBytes
  if finish > (map.size).bytes then
    throw (.iterationPastMap finish (map.size).bytes)
  if lenBytes == 0 then
    return #[]
  let mut selected := #[]
  let mut index := first
  let mut running := true
  while running do
    match segmentAt? map.entries index with
    | none => running := false
    | some segment =>
        if segment.range.start < finish then
          selected := selected.push segment
          index := index + 1
        else
          running := false
  return selected

def iterAll (map : DedupRangeMap α) : Array (RangeMapSegment α) := map.entries

/-- Read a stored segment by vector position. -/
def index (map : DedupRangeMap α) (position : Nat) :
    Except DedupRangeMapError (RangeMapSegment α) := do
  match segmentAt? map.entries position with
  | some segment => pure segment
  | none => throw (.indexOutOfBounds position map.entries.size)

/-- Replace a stored segment's value, corresponding to mutation through a
returned mutable iterator reference. -/
def setAtPos (map : DedupRangeMap α) (position : Nat) (data : α) :
    DedupMutationResult (DedupRangeMap α) := Id.run do
  match segmentAt? map.entries position with
  | none => return { state := map, outcome := .error (.indexOutOfBounds position map.entries.size) }
  | some segment =>
      match updateAt map.entries position { segment with data := data } with
      | .error error => return { state := map, outcome := .error error }
      | .ok entries => return { state := { map with entries }, outcome := .ok () }

/-- Split one segment at an interior byte offset. -/
private def splitIndex (entries : Array (RangeMapSegment α)) (index : Nat)
    (splitOffset : UInt64) (cloneData : α → α) :
    Except DedupRangeMapError (Array (RangeMapSegment α) × Bool) := do
  if h : index < entries.size then
    let segment := entries[index]
    if splitOffset == segment.range.start || splitOffset == segment.range.stop then
      return (entries, false)
    if splitOffset < segment.range.start || splitOffset ≥ segment.range.stop then
      throw (.splitOutsideSegment index splitOffset segment.range.start segment.range.stop)
    let first := { segment with range := { segment.range with stop := splitOffset } }
    let second := { segment with
      range := { segment.range with start := splitOffset }
      data := cloneData segment.data }
    let updated := entries.set index first h
    have insertBound : index + 1 ≤ updated.size := by
      change index + 1 ≤ (entries.set index first h).size
      rw [Array.size_set h]
      omega
    return (updated.insertIdx (index + 1) second insertBound, true)
  else
    throw (.indexOutOfBounds index entries.size)

private def removeInterval (entries : Array α) (first stop : Nat) : Array α :=
  entries.extract 0 first ++ entries.extract stop entries.size

/-- Merge an equal run `[first, stop)` into its first entry, preserving the
source's original data value and interval endpoints. -/
private def mergeRun (entries : Array (RangeMapSegment α)) (first stop : Nat) :
    Except DedupRangeMapError (Array (RangeMapSegment α)) := do
  let initial ← match segmentAt? entries first with
    | some segment => pure segment
    | none => throw (.indexOutOfBounds first entries.size)
  let last ← match segmentAt? entries (stop - 1) with
    | some segment => pure segment
    | none => throw (.indexOutOfBounds (stop - 1) entries.size)
  let initial := { initial with range := { initial.range with stop := last.range.stop } }
  let entries ← updateAt entries first initial
  return removeInterval entries (first + 1) stop

private def selectedSlice (entries : Array (RangeMapSegment α)) (first stop : Nat) :
    Except DedupRangeMapError (Array (RangeMapSegment α)) := do
  if first > stop || stop > entries.size then
    throw (.indexOutOfBounds stop entries.size)
  return entries.extract first stop

/-- Perform source `iter_mut`'s eager start split, bounded duplicate merge
scan, and end split. The returned position list represents the mutable slice;
callers can update those entries using `setAtPos`. -/
def iterMutWithClone (map : DedupRangeMap α) (offset len : Size)
    [DecidableEq α] (cloneData : α → α) :
    IterMutResult α := Id.run do
  let offsetBytes := offset.bytes
  let lenBytes := len.bytes
  if lenBytes == 0 then
    return { state := map, positions := #[], segments := #[], outcome := .ok () }
  let firstSearch := findOffset map offsetBytes
  let mut firstIndex ← match firstSearch with
    | .ok index => pure index
    | .error error =>
        return { state := map, positions := #[], segments := #[], outcome := .error error }
  let mut current := map
  match splitIndex current.entries firstIndex offsetBytes cloneData with
  | .error sourceError =>
      return { state := current, positions := #[], segments := #[], outcome := .error sourceError }
  | .ok (entries, didSplit) =>
      current := { current with entries }
      if didSplit then firstIndex := firstIndex + 1
  let finish ← match checkedEnd offsetBytes lenBytes with
    | .ok finish => pure finish
    | .error error =>
        return { state := current, positions := #[], segments := #[], outcome := .error error }
  let mut equalSinceIndex := firstIndex
  let mut successfulMergeCount := 3
  let mut endIndex := firstIndex
  let mut done := false
  let mut failure : Option DedupRangeMapError := none
  while !done && failure.isNone do
    match segmentAt? current.entries endIndex with
    | none =>
        failure := some (.indexOutOfBounds endIndex current.entries.size)
    | some segment =>
        let complete := segment.range.stop ≥ finish
        endIndex := endIndex + 1
        if !complete && endIndex ≥ current.entries.size then
          failure := some (.iterationPastMap finish current.size.bytes)
        else
          if successfulMergeCount > 0 then
            let shouldMerge ←
              if complete then pure true
              else
                match segmentAt? current.entries endIndex with
                | none =>
                    failure := some (.indexOutOfBounds endIndex current.entries.size)
                    pure false
                | some next =>
                    match segmentAt? current.entries equalSinceIndex with
                    | none =>
                        failure := some (.indexOutOfBounds equalSinceIndex current.entries.size)
                        pure false
                    | some firstEqual => pure (next.data != firstEqual.data)
            if shouldMerge && failure.isNone then
              let removedCount := endIndex - equalSinceIndex - 1
              if removedCount > 0 then
                match mergeRun current.entries equalSinceIndex endIndex with
                | .error error => failure := some error
                | .ok entries =>
                    current := { current with entries }
                    endIndex := endIndex - removedCount
                    successfulMergeCount := successfulMergeCount + removedCount
              else
                successfulMergeCount := successfulMergeCount - 1
              equalSinceIndex := endIndex
          if complete && failure.isNone then done := true
  match failure with
  | some error =>
      return { state := current, positions := #[], segments := #[], outcome := .error error }
  | none =>
      let lastIndex := endIndex - 1
      match splitIndex current.entries lastIndex finish cloneData with
      | .error error =>
          return { state := current, positions := #[], segments := #[], outcome := .error error }
      | .ok (entries, _) =>
          current := { current with entries }
          let selectedStop := lastIndex + 1
          match selectedSlice current.entries firstIndex selectedStop with
          | .error error =>
              return { state := current, positions := #[], segments := #[], outcome := .error error }
          | .ok segments =>
              let positions := (List.range (selectedStop - firstIndex)).toArray.map (· + firstIndex)
              return { state := current, positions, segments, outcome := .ok () }

/-- Prepare a mutable range using value-preserving copies on splits. This is the
usual instance for value-like Lean state and is exact when the Rust `Clone`
implementation returns the same value. Use `iterMutWithClone` when a modeled
clone operation produces a different value. -/
def iterMut (map : DedupRangeMap α) (offset len : Size) [DecidableEq α] :
    IterMutResult α :=
  map.iterMutWithClone offset len id

/-- Apply one pure update to every segment selected by `iter_mut`. Splitting and
merging happen first, before the callback updates values, as in Rust. -/
def modifyRangeWithClone (map : DedupRangeMap α) (offset len : Size)
    [DecidableEq α] (cloneData : α → α) (modify : ByteRange → α → α) :
    IterMutResult α := Id.run do
  let prepared := map.iterMutWithClone offset len cloneData
  match prepared.outcome with
  | .error _ => return prepared
  | .ok _ =>
      let mut current := prepared.state
      let mut segments := #[]
      for position in prepared.positions do
        match segmentAt? current.entries position with
        | none =>
            return ({ state := current, positions := prepared.positions, segments := segments, outcome := .error (.indexOutOfBounds position current.entries.size) } : IterMutResult α)
        | some segment =>
            let updated := { segment with data := modify segment.range segment.data }
            match updateAt current.entries position updated with
            | .error error =>
                return ({ state := current, positions := prepared.positions, segments := segments, outcome := .error error } : IterMutResult α)
            | .ok entries =>
                current := { current with entries }
                segments := segments.push updated
      return { state := current, positions := prepared.positions, segments, outcome := .ok () }

/-- Apply a pure update after source `iter_mut` splitting and merging. The
default split copy preserves the immutable Lean value. -/
def modifyRange (map : DedupRangeMap α) (offset len : Size)
    [DecidableEq α] (modify : ByteRange → α → α) : IterMutResult α :=
  map.modifyRangeWithClone offset len id modify

/-- Apply an update to every element without splitting or merging, matching
`iter_mut_all`. -/
def modifyAll (map : DedupRangeMap α) (modify : ByteRange → α → α) : DedupRangeMap α :=
  { map with entries := map.entries.map fun segment =>
      { segment with data := modify segment.range segment.data } }

/-- Coalesce every adjacent equal run, with the same adjacency assertion as the
source. On a failed assertion the vector contains only the already-built prefix. -/
def mergeAdjacentThorough (map : DedupRangeMap α) [DecidableEq α] :
    DedupMutationResult (DedupRangeMap α) := Id.run do
  let mut accumulated : Array (RangeMapSegment α) := #[]
  for segment in map.entries do
    match accumulated.back? with
    | none => accumulated := accumulated.push segment
    | some previous =>
        if previous.data = segment.data then
          if previous.range.stop != segment.range.start then
            return ({ state := { map with entries := accumulated }, outcome := .error (.mergeRequiresAdjacent previous.range.stop segment.range.start) } : DedupMutationResult (DedupRangeMap α))
          let position := accumulated.size - 1
          match segmentAt? accumulated position with
          | none =>
              return ({ state := { map with entries := accumulated }, outcome := .error (.indexOutOfBounds position accumulated.size) } : DedupMutationResult (DedupRangeMap α))
          | some first =>
              match updateAt accumulated position
                  { first with range := { first.range with stop := segment.range.stop } } with
              | .error error =>
                  return { state := { map with entries := accumulated }, outcome := .error error }
              | .ok next => accumulated := next
        else
          accumulated := accumulated.push segment
  return { state := { map with entries := accumulated }, outcome := .ok () }

/-- Sorted, gapless, nonempty intervals beginning at zero. -/
def WellFormed (map : DedupRangeMap α) : Prop :=
  if h : map.entries.size = 0 then True
  else
    map.entries[0].range.start = 0 ∧
    (∀ i (hi : i < map.entries.size), map.entries[i].range.start < map.entries[i].range.stop) ∧
    (∀ i (hi : i + 1 < map.entries.size),
      map.entries[i].range.stop = map.entries[i + 1].range.start)

private theorem mergeRun_layout (entries : Array (RangeMapSegment α)) (first stop : Nat)
    (nonempty : first < stop) (bounded : stop ≤ entries.size) :
    ∃ out : Array (RangeMapSegment α),
      mergeRun entries first stop = .ok out ∧
      ∃ outSize : out.size = entries.size - (stop - first - 1),
      ∀ (index : Nat) (valid : index < out.size),
        out[index] =
          if before : index < first then entries[index]'(by omega)
          else if same : index = first then
            { entries[first]'(by omega) with range.stop := entries[stop - 1]'(by omega) |>.range.stop }
          else entries[index + (stop - first - 1)]'(by omega) := by
  have atFirst : first < entries.size := by omega
  have atLast : stop - 1 < entries.size := by omega
  let elem := { entries[first] with range.stop := entries[stop - 1] |>.range.stop }
  let updated := entries.set first elem atFirst
  let out := removeInterval updated (first + 1) stop
  have outcome : mergeRun entries first stop = .ok out := by
    simp [mergeRun, segmentAt?, atFirst, atLast, updateAt, elem, updated, out,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
  have outSize : out.size = entries.size - (stop - first - 1) := by
    simp [out, removeInterval, updated]
    omega
  exact ⟨out, outcome, outSize, by
    intro index valid
    have valid' : index < (updated.extract 0 (first + 1) ++ updated.extract stop updated.size).size := by
      simpa only [out, removeInterval] using valid
    have prefixSize : (updated.extract 0 (first + 1)).size = first + 1 := by
      simp [updated]
      omega
    by_cases before : index < first
    · have inPrefix : index < (updated.extract 0 (first + 1)).size := by omega
      simp only [before, ↓reduceDIte]
      change (updated.extract 0 (first + 1) ++ updated.extract stop updated.size)[index]'valid' = _
      rw [Array.getElem_append_left inPrefix]
      simp [updated, Array.getElem_set, show first ≠ index by omega]
    · by_cases same : index = first
      · subst index
        have inPrefix : first < (updated.extract 0 (first + 1)).size := by omega
        simp only [before, ↓reduceDIte]
        change (updated.extract 0 (first + 1) ++ updated.extract stop updated.size)[first]'valid' = _
        rw [Array.getElem_append_left inPrefix]
        simp [updated, elem]
      · have afterPrefix : (updated.extract 0 (first + 1)).size ≤ index := by omega
        simp only [before, same, ↓reduceDIte]
        change (updated.extract 0 (first + 1) ++ updated.extract stop updated.size)[index]'valid' = _
        rw [Array.getElem_append_right afterPrefix]
        simp only [Array.getElem_extract, prefixSize, updated, Array.getElem_set]
        have shift : stop + (index - (first + 1)) = index + (stop - first - 1) := by omega
        have distinct : first ≠ index + (stop - first - 1) := by omega
        simp [distinct, shift]⟩

private theorem mapAt_indexed (map : DedupRangeMap α) (byte : UInt64) (data : α) :
    map.MapAt byte data ↔ ∃ (index : Nat) (bound : index < map.entries.size),
      map.entries[index].range.Contains byte ∧ map.entries[index].data = data := by
  constructor
  · rintro ⟨index, segment, entry, contains, value⟩
    obtain ⟨bound, rfl⟩ := Array.getElem?_eq_some_iff.mp entry
    exact ⟨index, bound, contains, value⟩
  · rintro ⟨index, bound, contains, value⟩
    exact ⟨index, _, Array.getElem?_eq_getElem bound, contains, value⟩

private theorem mergeRun_valid (map : DedupRangeMap α) (first stop : Nat)
    (formed : map.WellFormed) (nonempty : first < stop) (bounded : stop ≤ map.entries.size)
    (equal : ∀ (i : Nat) (hi : i < map.entries.size), first ≤ i → i < stop →
      map.entries[i].data = (map.entries[first]'(by omega)).data) :
    ∃ out : DedupRangeMap α,
      mergeRun map.entries first stop = .ok out.entries ∧ out.WellFormed ∧
      out.size = map.size ∧ (∀ byte data, out.MapAt byte data ↔ map.MapAt byte data) ∧
      ∃ outSize : out.entries.size = map.entries.size - (stop - first - 1),
        ∀ (index : Nat) (valid : index < out.entries.size),
          out.entries[index] =
            if before : index < first then map.entries[index]'(by omega)
            else if same : index = first then
              { map.entries[first]'(by omega) with range.stop := (map.entries[stop - 1]'(by omega)).range.stop }
            else map.entries[index + (stop - first - 1)]'(by omega) := by
  have nonzero : map.entries.size ≠ 0 := by omega
  rw [WellFormed, dite_eq_right nonzero] at formed
  obtain ⟨origin, positive, consecutive⟩ := formed
  obtain ⟨actual, outcome, outSize, layout⟩ := mergeRun_layout map.entries first stop nonempty bounded
  let out : DedupRangeMap α := ⟨actual⟩
  let shift := stop - first - 1
  have left (i : Nat) (before : i < first) :
      actual[i]'(by omega) = map.entries[i]'(by omega) := by
    simpa only [before, ↓reduceDIte] using layout i (by omega)
  have middle :
      actual[first]'(by omega) =
        { map.entries[first]'(by omega) with range.stop := (map.entries[stop - 1]'(by omega)).range.stop } := by
    simpa only [Nat.lt_irrefl, ↓reduceDIte] using layout first (by omega)
  have right (i : Nat) (later : first < i) (bound : i < actual.size) :
      actual[i] = map.entries[i + shift]'(by dsimp [shift]; omega) := by
    simpa only [show ¬ i < first by omega, show i ≠ first by omega, ↓reduceDIte, shift] using layout i bound
  have starts (j : Nat) (hj : j < map.entries.size) :
      ∀ i (hi : i < map.entries.size), i ≤ j → map.entries[i].range.start ≤ map.entries[j].range.start := by
    induction j with
    | zero =>
      intro i hi le
      have same : i = 0 := by omega
      subst i
      exact UInt64.le_refl _
    | succ j ih =>
      intro i hi le
      by_cases same : i = j + 1
      · subst i
        exact UInt64.le_refl _
      · exact UInt64.le_trans (ih (by omega) i hi (by omega))
          (UInt64.le_of_lt ((consecutive j hj) ▸ positive j (by omega)))
  have stops (j : Nat) (hj : j < map.entries.size) :
      ∀ i (hi : i < map.entries.size), i ≤ j → map.entries[i].range.stop ≤ map.entries[j].range.stop := by
    induction j with
    | zero =>
      intro i hi le
      have same : i = 0 := by omega
      subst i
      exact UInt64.le_refl _
    | succ j ih =>
      intro i hi le
      by_cases same : i = j + 1
      · subst i
        exact UInt64.le_refl _
      · exact UInt64.le_trans (ih (by omega) i hi (by omega))
          (UInt64.le_of_lt ((consecutive j hj).symm ▸ positive (j + 1) hj))
  have covers (j : Nat) (hj : j < map.entries.size) (firstLe : first ≤ j) (byte : UInt64)
      (firstStart : (map.entries[first]'(by omega)).range.start ≤ byte)
      (lastStop : byte < map.entries[j].range.stop) :
      ∃ (i : Nat) (hi : i < map.entries.size), first ≤ i ∧ i ≤ j ∧
        map.entries[i].range.Contains byte := by
    induction j with
    | zero =>
      have same : first = 0 := by omega
      subst first
      exact ⟨0, hj, by omega, by omega, firstStart, lastStop⟩
    | succ j ih =>
      by_cases inLast : map.entries[j + 1].range.start ≤ byte
      · exact ⟨j + 1, hj, firstLe, Nat.le_refl _, inLast, lastStop⟩
      · have before : byte < map.entries[j + 1].range.start :=
          UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_not_ge ((fun le => inLast (UInt64.le_iff_toNat_le.mpr le))))
        have prev : first ≤ j := by
          by_cases h : first ≤ j
          · exact h
          · have same : first = j + 1 := by omega
            subst first
            exact False.elim (inLast firstStart)
        obtain ⟨index, bound, low, high, covered⟩ :=
          ih (by omega) prev firstStart (by rwa [consecutive j hj])
        exact ⟨index, bound, low, by omega, covered⟩
  have atFirst : first < actual.size := by omega
  have outNonzero : actual.size ≠ 0 := by omega
  refine ⟨out, outcome, ?_, ?_, ?_, outSize, layout⟩
  · unfold WellFormed
    change (if h : actual.size = 0 then True else _)
    rw [dite_eq_right outNonzero]
    refine ⟨?_, ?_, ?_⟩
    · change (actual[0]'(by omega)).range.start = 0
      by_cases emptyPrefix : first = 0
      · subst first
        rw [middle]
        exact origin
      · rw [left 0 (by omega)]
        exact origin
    · intro i hi
      change i < actual.size at hi
      change (actual[i]'hi).range.start < (actual[i]'hi).range.stop
      by_cases before : i < first
      · rw [left i before]
        exact positive i (by omega)
      · by_cases same : i = first
        · subst i
          rw [middle]
          exact UInt64.lt_of_lt_of_le (positive first (by omega))
            (stops (stop - 1) (by omega) first (by omega) (by omega))
        · rw [right i (by omega) hi]
          exact positive _ (by dsimp [shift]; omega)
    · intro i hi
      change i + 1 < actual.size at hi
      change (actual[i]'(by omega)).range.stop = (actual[i + 1]'hi).range.start
      by_cases preceding : i + 1 < first
      · rw [left i (by omega), left (i + 1) preceding]
        exact consecutive i (by omega)
      · by_cases before : i < first
        · have next : i + 1 = first := by omega
          rw [left i before]
          have rightEnd : (actual[i + 1]'hi).range.start = (map.entries[i + 1]'(by omega)).range.start := by
            simp only [next, middle]
          rw [rightEnd]
          exact consecutive i (by omega)
        · by_cases same : i = first
          · subst i
            rw [middle, right (first + 1) (by omega) hi]
            have targetIndex : first + 1 + shift = stop := by dsimp [shift]; omega
            simp only [targetIndex]
            have adjacent := consecutive (stop - 1) (by omega)
            simpa only [Nat.sub_add_cancel (show 1 ≤ stop by omega)] using adjacent
          · rw [right i (by omega) (by omega), right (i + 1) (by omega) hi]
            have adjacent := consecutive (i + shift) (by dsimp [shift]; omega)
            simpa only [Nat.add_right_comm] using adjacent
  · have final : (actual[actual.size - 1]'(by omega)).range.stop =
        (map.entries[map.entries.size - 1]'(by omega)).range.stop := by
      by_cases last : actual.size - 1 = first
      · have originalLast : stop - 1 = map.entries.size - 1 := by omega
        simp only [last, middle, originalLast]
      · rw [right (actual.size - 1) (by omega) (by omega)]
        have originalLast : actual.size - 1 + shift = map.entries.size - 1 := by dsimp [shift]; omega
        simp only [originalLast]
    simp only [size, out, Array.back?_eq_getElem?,
      Array.getElem?_eq_getElem (show actual.size - 1 < actual.size by omega),
      Array.getElem?_eq_getElem (show map.entries.size - 1 < map.entries.size by omega), final]
  · intro byte data
    simp only [mapAt_indexed]
    constructor
    · rintro ⟨i, hi, contains, value⟩
      change i < actual.size at hi
      change actual[i].range.Contains byte at contains
      change actual[i].data = data at value
      by_cases before : i < first
      · rw [left i before] at contains value
        exact ⟨i, _, contains, value⟩
      · by_cases same : i = first
        · subst i
          rw [middle] at contains value
          obtain ⟨index, valid, low, high, found⟩ :=
            covers (stop - 1) (by omega) (by omega) byte contains.1 contains.2
          exact ⟨index, valid, found, (equal index valid low (by omega)).trans value⟩
        · rw [right i (by omega) hi] at contains value
          exact ⟨i + shift, _, contains, value⟩
    · rintro ⟨i, hi, contains, value⟩
      by_cases before : i < first
      · exact ⟨i, by change i < actual.size; omega, by change actual[i].range.Contains byte; rwa [left i before],
          by change actual[i].data = data; rwa [left i before]⟩
      · by_cases inRun : i < stop
        · refine ⟨first, atFirst, ?_, ?_⟩
          · change actual[first].range.Contains byte
            rw [middle]
            exact ⟨UInt64.le_trans (starts i hi first (by omega) (by omega)) contains.1,
              UInt64.lt_of_lt_of_le contains.2 (stops (stop - 1) (by omega) i hi (by omega))⟩
          · change actual[first].data = data
            rw [middle]
            exact (equal i hi (by omega) inRun).symm.trans value
        · have targetBound : i - shift < actual.size := by dsimp [shift]; omega
          have targetLater : first < i - shift := by dsimp [shift]; omega
          have targetIndex : i - shift + shift = i := by dsimp [shift]; omega
          refine ⟨i - shift, targetBound, ?_, ?_⟩
          · change actual[i - shift].range.Contains byte
            simpa only [right _ targetLater targetBound, targetIndex] using contains
          · change actual[i - shift].data = data
            simpa only [right _ targetLater targetBound, targetIndex] using value

private theorem splitIndex_shape (map : DedupRangeMap α) (index : Nat) (offset : UInt64)
    (hindex : index < map.entries.size) (hlo : map.entries[index].range.start ≤ offset)
    (hhi : offset ≤ map.entries[index].range.stop) :
    ∃ entries didSplit, splitIndex map.entries index offset id = .ok (entries, didSplit) ∧
      ((didSplit = true) ↔ map.entries[index].range.start < offset ∧ offset < map.entries[index].range.stop) ∧
      entries.size = map.entries.size + (if didSplit then 1 else 0) ∧
      ∀ j, entries[j]? =
        if didSplit then
          if j < index then map.entries[j]? else
          if j = index then some { map.entries[index] with range.stop := offset } else
          if j = index + 1 then some { map.entries[index] with range.start := offset } else
          map.entries[j-1]?
        else map.entries[j]? := by
  simp only [splitIndex, hindex, ↓reduceDIte, beq_iff_eq, Bool.or_eq_true]
  by_cases boundary : offset = map.entries[index].range.start ∨ offset = map.entries[index].range.stop
  · refine ⟨map.entries, false, ?_, ?_, by simp, ?_⟩
    · simp [boundary, pure, Pure.pure, Except.pure]
    · simp only [Bool.false_eq_true, false_iff]
      rcases boundary with h | h <;> simp [h]
    · intro j
      simp
  · let first : RangeMapSegment α := { map.entries[index] with range.stop := offset }
    let second : RangeMapSegment α := { map.entries[index] with range.start := offset }
    have interior : map.entries[index].range.start < offset ∧ offset < map.entries[index].range.stop :=
      ⟨UInt64.lt_of_le_of_ne hlo (fun same => boundary (.inl same.symm)),
        UInt64.lt_of_le_of_ne hhi (fun same => boundary (.inr same))⟩
    have insertBound : index + 1 ≤ (map.entries.set index first hindex).size := by
      rw [Array.size_set]
      omega
    refine ⟨(map.entries.set index first hindex).insertIdx (index + 1) second insertBound, true, ?_,
      by simp [interior], by simp, ?_⟩
    · simp [boundary, UInt64.not_lt.mpr hlo, UInt64.not_le.mpr interior.2, first, second]; rfl
    · intro j
      simp only [↓reduceIte]
      by_cases before : j < index
      · simp [before, Array.getElem?_insertIdx_of_lt insertBound (show j < index+1 by omega),
          Array.getElem?_set_ne hindex (show index ≠ j by omega)]
      · by_cases atIndex : j = index
        · subst j
          simp [Array.getElem?_insertIdx_of_lt insertBound (show index < index+1 by omega), first]
        · by_cases rightIndex : j = index + 1
          · subst j
            simp [second, before, Array.getElem?_insertIdx_self insertBound]
          · have greater : index + 1 < j := by omega
            simp only [before, atIndex, rightIndex, ite_false, Array.getElem?_insertIdx,
              show ¬ j < index + 1 by omega, Array.getElem?_set_ne hindex (show index ≠ j-1 by omega)]

private theorem splitIndex_valid (map : DedupRangeMap α) (wf : map.WellFormed) (index : Nat)
    (hindex : index < map.entries.size) (offset : UInt64)
    (hlo : map.entries[index].range.start ≤ offset)
    (hhi : offset ≤ map.entries[index].range.stop) :
    ∃ entries didSplit, splitIndex map.entries index offset id = .ok (entries, didSplit) ∧
      ((didSplit = true) ↔ map.entries[index].range.start < offset ∧ offset < map.entries[index].range.stop) ∧
      entries.size = map.entries.size + (if didSplit then 1 else 0) ∧
      (∀ j, entries[j]? =
        if didSplit then
          if j < index then map.entries[j]? else
          if j = index then some { map.entries[index] with range.stop := offset } else
          if j = index + 1 then some { map.entries[index] with range.start := offset } else
          map.entries[j-1]?
        else map.entries[j]?) ∧
      (⟨entries⟩ : DedupRangeMap α).WellFormed ∧
      (⟨entries⟩ : DedupRangeMap α).size = map.size ∧
      ∀ byte data, (⟨entries⟩ : DedupRangeMap α).MapAt byte data ↔ map.MapAt byte data := by
  obtain ⟨entries, didSplit, ran, exactly, count, shape⟩ := splitIndex_shape map index offset hindex hlo hhi
  refine ⟨entries, didSplit, ran, exactly, count, shape, ?_, ?_, ?_⟩
  all_goals cases didSplit
  case refine_1.false =>
    have eq : entries = map.entries := Array.ext_getElem? (by simpa using shape)
    simpa [eq] using wf
  case refine_2.false =>
    have eq : entries = map.entries := Array.ext_getElem? (by simpa using shape)
    cases map
    simp [eq]
  case refine_3.false =>
    have eq : entries = map.entries := Array.ext_getElem? (by simpa using shape)
    cases map
    simp [eq]
  all_goals
    simp only [↓reduceIte] at count shape
    have interior := exactly.mp rfl
    have left (j : Nat) (lt : j < index) : entries[j]'(by omega) = map.entries[j]'(by omega) :=
      Option.some.inj (by simpa [lt, getElem?_pos, show j < entries.size by omega,
        show j < map.entries.size by omega] using shape j)
    have leftSplit : entries[index]'(by omega) = { map.entries[index] with range.stop := offset } :=
      Option.some.inj (by simpa [getElem?_pos, show index < entries.size by omega] using shape index)
    have rightSplit : entries[index+1]'(by omega) = { map.entries[index] with range.start := offset } :=
      Option.some.inj (by simpa [getElem?_pos, show index+1 < entries.size by omega, show ¬ index + 1 < index by omega] using shape (index+1))
    have right (j : Nat) (gt : index+1 < j) (bound : j < entries.size) :
        entries[j] = map.entries[j-1]'(by omega) :=
      Option.some.inj (by simpa [getElem?_pos, bound, show j-1 < map.entries.size by omega,
        show ¬ j < index by omega, show j ≠ index by omega, show j ≠ index+1 by omega] using shape j)
  case refine_1.true =>
    unfold WellFormed at *
    have oldNonempty : ¬map.entries.size = 0 := by omega
    have newNonempty : ¬entries.size = 0 := by omega
    simp only [oldNonempty, ↓reduceDIte] at wf
    change (if h : entries.size = 0 then True else _)
    simp only [newNonempty, ↓reduceDIte]
    refine ⟨?_, ?_, ?_⟩
    · by_cases eq : index = 0
      · subst index
        rw [leftSplit]
        exact wf.1
      · rw [left 0 (by omega)]
        exact wf.1
    · intro j bound
      by_cases before : j < index
      · rw [left j before]
        exact wf.2.1 j (by omega)
      · by_cases atLeft : j = index
        · subst j
          rw [leftSplit]
          exact interior.1
        · by_cases atRight : j = index+1
          · subst j
            rw [rightSplit]
            exact interior.2
          · rw [right j (by omega) bound]
            exact wf.2.1 _ (by omega)
    · intro j bound
      by_cases before : j+1 < index
      · rw [left j (by omega), left (j+1) before]
        exact wf.2.2 _ (by omega)
      · by_cases adjacent : j+1 = index
        · rw [left j (by omega)]
          subst index
          rw [leftSplit]
          exact wf.2.2 _ (by omega)
        · by_cases atLeft : j = index
          · subst j
            rw [leftSplit, rightSplit]
          · by_cases atRight : j = index+1
            · subst j
              rw [rightSplit, right (index+1+1) (by omega) bound]
              simpa using wf.2.2 index (by omega)
            · rw [right j (by omega) (by omega), right (j+1) (by omega) bound]
              have eq : j - 1 + 1 = j := by omega
              have adjacent := wf.2.2 (j - 1) (by omega)
              simpa only [eq, Nat.add_sub_cancel] using adjacent
  case refine_2.true =>
    simp only [size, Array.back?_eq_getElem?]
    have lastBound : entries.size - 1 < entries.size := by omega
    have oldBound : map.entries.size - 1 < map.entries.size := by omega
    simp only [getElem?_pos, lastBound, oldBound]
    by_cases last : index+1 = entries.size-1
    · simp only [← last, rightSplit]
      have eq : map.entries.size - 1 = index := by omega
      simp [eq]
    · have gt : index+1 < entries.size-1 := by omega
      rw [right _ gt lastBound]
      have eq : entries.size - 1 - 1 = map.entries.size - 1 := by omega
      simp [eq]
  case refine_3.true =>
    intro byte data
    simp only [mapAt_indexed]
    constructor
    · rintro ⟨j, bound, contains, value⟩
      by_cases before : j < index
      · rw [left j before] at contains value
        exact ⟨j, _, contains, value⟩
      · by_cases atLeft : j = index
        · subst j
          rw [leftSplit] at contains value
          exact ⟨index, hindex, ⟨contains.1, UInt64.lt_of_lt_of_le contains.2 hhi⟩, value⟩
        · by_cases atRight : j = index + 1
          · subst j
            rw [rightSplit] at contains value
            exact ⟨index, hindex, ⟨UInt64.le_trans hlo contains.1, contains.2⟩, value⟩
          · rw [right j (by omega) bound] at contains value
            exact ⟨j - 1, _, contains, value⟩
    · rintro ⟨j, bound, contains, value⟩
      by_cases before : j < index
      · refine ⟨j, by change j < entries.size; omega, ?_, ?_⟩
        · change entries[j].range.Contains byte
          rwa [left j before]
        · change entries[j].data = data
          rwa [left j before]
      · by_cases atIndex : j = index
        · subst j
          by_cases atLeft : byte < offset
          · have newBound : index < entries.size := by omega
            refine ⟨index, newBound, ?_, ?_⟩
            · change entries[index].range.Contains byte
              rw [leftSplit]
              exact ⟨contains.1, atLeft⟩
            · change entries[index].data = data
              rwa [leftSplit]
          · have newBound : index + 1 < entries.size := by omega
            refine ⟨index + 1, newBound, ?_, ?_⟩
            · change entries[index + 1].range.Contains byte
              rw [rightSplit]
              exact ⟨UInt64.not_lt.mp atLeft, contains.2⟩
            · change entries[index + 1].data = data
              rwa [rightSplit]
        · have newBound : j + 1 < entries.size := by omega
          refine ⟨j + 1, newBound, ?_, ?_⟩
          · change entries[j + 1].range.Contains byte
            simpa only [right _ (by omega) newBound, Nat.add_sub_cancel] using contains
          · change entries[j + 1].data = data
            simpa only [right _ (by omega) newBound, Nat.add_sub_cancel] using value

theorem new_wellFormed (size : Size) (initial : α) :
    (new size initial).WellFormed := by
  unfold WellFormed new
  by_cases h : size.bytes = 0
  · simp [h]
  · have hpos : 0 < size.bytes := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have hne : size.bytes.toNat ≠ 0 := by
        intro hzero
        have hzero' : size.bytes.toNat = (0 : UInt64).toNat := by simpa using hzero
        have hbits : size.bytes = 0 := UInt64.toNat_inj.mp hzero'
        exact h hbits
      exact Nat.pos_of_ne_zero hne
    simp [h, hpos]

end DedupRangeMap
end Miri.DataStructures

namespace Miri.DataStructures.DedupRangeMap
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {A : Type} [DecidableEq A]
private theorem findOffset_new_zero (size : Size) (value : A) (positive : size.bytes ≠ 0) :
    findOffset (new size value) 0 = .ok 0 := by
  unfold findOffset new
  simp only [positive,beq_iff_eq,↓reduceIte,Size.ofBytes,Id.run,bind,Bind.bind,pure,Pure.pure,ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [segmentAt?,positive,bind,Bind.bind,pure,Pure.pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [bind,Bind.bind,pure,Pure.pure]

open Lean Elab Meta Tactic in
elab "name_full_range_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun e => e.isAppOf ``Lean.Loop.forIn)
      | throwError "missing full-range source loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← inferType body) body
    let (scan,goal) ← goal.intro1P
    return [← goal.change (target.replace fun e => if e == body then some (mkFVar scan) else none)]

theorem iterMut_new_full (size : Size) (value : A) (positive : size.bytes ≠ 0) :
    (new size value).iterMut Size.ZERO size =
      ⟨new size value,#[0],#[⟨⟨0,size.bytes⟩,value⟩],.ok ()⟩ := by
  have splitZero : splitIndex (new size value).entries 0 0 id =
      .ok ((new size value).entries,false) := by
    simp [new,positive,splitIndex,segmentAt?,Id.run,pure,Pure.pure,Except.pure]
  have finish : checkedEnd 0 size.bytes = .ok size.bytes := by
    simp [checkedEnd,Size.ZERO,Size.ofBytes,Size.add,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  unfold iterMut iterMutWithClone
  simp only [Size.ZERO,Size.ofBytes,positive,beq_iff_eq,↓reduceIte]
  rw [findOffset_new_zero size value positive]
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  rw [splitZero]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [finish]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  simp only [ForIn.forIn]
  name_full_range_scan
  have computed : Lean.Loop.forIn {} ((new size value),0,3,0,false,(none : Option DedupRangeMapError)) scan =
      ((new size value),1,2,1,true,(none : Option DedupRangeMapError)) := by
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [scan,new,positive,segmentAt?,bind,Bind.bind,pure,Pure.pure]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [scan,new,positive,segmentAt?,bind,Bind.bind,pure,Pure.pure]
  rw [computed]
  simp [new,positive,splitIndex,segmentAt?,selectedSlice,Id.run,
    bind,Bind.bind,pure,Pure.pure,Except.bind,Except.pure]
end Miri.DataStructures.DedupRangeMap

namespace Miri.DataStructures.DedupRangeMap

open Miri.ABI

private def searchStep {A : Type} (map : DedupRangeMap A) (offset : UInt64) (_ : Unit)
    (window : Nat × Nat × Option (Except DedupRangeMapError Nat)) :
    Id (ForInStep (Nat × Nat × Option (Except DedupRangeMapError Nat))) :=
  let (low, high, answer) := window
  if low < high && answer.isNone then
    let middle := low + (high - low) / 2
    match segmentAt? map.entries middle with
    | none => pure (ForInStep.yield (low, high, some (.error (.indexOutOfBounds middle map.entries.size))))
    | some segment =>
      if offset < segment.range.start then pure (ForInStep.yield (low, middle, answer))
      else if offset ≥ segment.range.stop then pure (ForInStep.yield (middle + 1, high, answer))
      else pure (ForInStep.yield (low, high, some (.ok middle)))
  else pure (.done (low, high, answer))

private theorem searchWindow {A : Type} (map : DedupRangeMap A) (offset : UInt64)
    (adjacent : ∀ i (hi : i + 1 < map.entries.size),
      map.entries[i].range.stop = map.entries[i + 1].range.start)
    (low high : Nat) (bounded : high ≤ map.entries.size) (nonempty : low < high)
    (above : map.entries[low].range.start ≤ offset)
    (below : offset < map.entries[high - 1].range.stop) :
    ∃ l h i, ∃ hi : i < map.entries.size,
      (Lean.Loop.forIn (m := Id) {} (low, high, (none : Option (Except DedupRangeMapError Nat))) (searchStep map offset) :
        Id (Nat × Nat × Option (Except DedupRangeMapError Nat))) =
      (l, h, some (.ok i)) ∧ map.entries[i].range.Contains offset := by
  let middle := low + (high - low) / 2
  have midLow : low ≤ middle := by omega
  have midHigh : middle < high := by omega
  have midBounds : middle < map.entries.size := by omega
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [searchStep, nonempty, decide_true, Option.isNone_none, Bool.and_true, ↓reduceIte]
  rw [show low + (high - low) / 2 = middle from rfl]
  simp only [segmentAt?, midBounds, ↓reduceDIte]
  by_cases before : offset < map.entries[middle].range.start
  · have smallerLow : low < middle := by
      apply Classical.byContradiction
      intro no
      have same : middle = low := by omega
      exact (UInt64.not_lt.mpr above) (by simpa only [same] using before)
    have midPred : middle - 1 + 1 = middle := by omega
    have predBounds : middle - 1 + 1 < map.entries.size := by omega
    have belowMiddle : offset < map.entries[middle - 1].range.stop := by
      rw [adjacent (middle - 1) predBounds]
      simpa only [midPred] using before
    simp only [before, ↓reduceIte, bind, Bind.bind, pure, Pure.pure]
    exact searchWindow map offset adjacent low middle (by omega) smallerLow above belowMiddle
  · by_cases after : offset ≥ map.entries[middle].range.stop
    · have smallerHigh : middle + 1 < high := by
        apply Classical.byContradiction
        intro no
        have same : middle = high - 1 := by omega
        exact (UInt64.not_le.mpr below) (by simpa only [same] using after)
      have aboveMiddle : map.entries[middle + 1].range.start ≤ offset := by
        rw [← adjacent middle (by omega)]
        exact after
      simp only [before, after, ↓reduceIte, bind, Bind.bind, pure, Pure.pure]
      exact searchWindow map offset adjacent (middle + 1) high bounded smallerHigh aboveMiddle below
    · simp only [before, after, ↓reduceIte, bind, Bind.bind, pure, Pure.pure]
      refine ⟨low, high, middle, midBounds, ?_, UInt64.not_lt.mp before, UInt64.not_le.mp after⟩
      rw [Lean.Loop.forIn_eq_of_monadTail]
      simp [searchStep, bind, Bind.bind, pure, Pure.pure]
termination_by high - low
decreasing_by all_goals omega

/-- Every byte inside a well-formed partition is found by the binary search. -/
theorem findOffset_in_range {A : Type} (map : DedupRangeMap A) (offset : UInt64)
    (formed : map.WellFormed) (inside : offset < map.size.bytes) :
    ∃ i, ∃ hi : i < map.entries.size, findOffset map offset = .ok i ∧
      map.entries[i].range.Contains offset := by
  by_cases empty : map.entries.size = 0
  · have sizeZero : map.size.bytes = 0 := by
      simp [size, Array.back?_eq_getElem?, empty, Size.ZERO]
    rw [sizeZero] at inside
    exact (UInt64.not_lt_zero inside).elim
  have nonempty : 0 < map.entries.size := by omega
  have last : map.entries.size - 1 < map.entries.size := by omega
  have insideLast : offset < map.entries[map.entries.size - 1].range.stop := by
    simpa only [size, Array.back?_eq_getElem?, Array.getElem?_eq_getElem last, Size.ofBytes] using inside
  simp only [WellFormed, empty, ↓reduceDIte] at formed
  have startsBefore : map.entries[0].range.start ≤ offset := by
    rw [formed.1]
    exact UInt64.zero_le
  obtain ⟨low, high, i, hi, found, covered⟩ :=
    searchWindow map offset formed.2.2 0 map.entries.size (Nat.le_refl _) nonempty startsBefore insideLast
  refine ⟨i, hi, ?_, covered⟩
  change (match (Lean.Loop.forIn (m := Id) {} (0, map.entries.size, none) (searchStep map offset)).2.2 with
    | some result => result
    | none => .error (.offsetNotCovered offset map.size.bytes)) = .ok i
  rw [found]

end Miri.DataStructures.DedupRangeMap

namespace Miri.DataStructures.DedupRangeMap

open Miri.ABI
set_option autoImplicit false
variable {A : Type} [DecidableEq A]

omit [DecidableEq A] in
private theorem wf_segment_positive {map : DedupRangeMap A} (wf : map.WellFormed)
    (i : Nat) (hi : i < map.entries.size) :
    map.entries[i].range.start < map.entries[i].range.stop := by
  unfold WellFormed at wf
  rw [dite_eq_right (by omega)] at wf
  exact wf.2.1 i hi

omit [DecidableEq A] in
private theorem wf_segment_adjacent {map : DedupRangeMap A} (wf : map.WellFormed)
    (i : Nat) (hi : i + 1 < map.entries.size) :
    map.entries[i].range.stop = map.entries[i + 1].range.start := by
  unfold WellFormed at wf
  rw [dite_eq_right (by omega)] at wf
  exact wf.2.2 i hi

omit [DecidableEq A] in
private theorem wf_segment_order {map : DedupRangeMap A} (wf : map.WellFormed)
    (i j : Nat) (hij : i < j) (hj : j < map.entries.size) :
    map.entries[i].range.stop ≤ map.entries[j].range.start := by
  induction j with
  | zero => omega
  | succ j ih =>
    have adjacent := wf_segment_adjacent wf j (by omega)
    rw [← adjacent]
    by_cases same : i = j
    · subst j
      exact UInt64.le_refl _
    · exact UInt64.le_trans (ih (by omega) (by omega))
        (UInt64.le_of_lt (wf_segment_positive wf j (by omega)))

omit [DecidableEq A] in
private theorem size_bytes_last {map : DedupRangeMap A} (i : Nat)
    (last : i + 1 = map.entries.size) :
    map.size.bytes = map.entries[i].range.stop := by
  unfold size
  have eq : map.entries.size - 1 = i := by omega
  simp [Array.back?, Size.ofBytes, eq, show i < map.entries.size from by omega]

omit [DecidableEq A] in
private theorem segmentAt?_of_lt {entries : Array (RangeMapSegment A)} (i : Nat)
    (hi : i < entries.size) : segmentAt? entries i = some entries[i] := by
  simp [segmentAt?, hi]

private theorem scan_loop_invariant {β : Type} (scan : Unit → β → Id (ForInStep β))
    (measure : β → Nat) (invariant : β → Prop) (finished : β → Prop)
    (step : ∀ state, invariant state →
      (∃ final, scan () state = .done final ∧ finished final) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ measure next < measure state)
    (initial : β) (valid : invariant initial) :
    finished (Lean.Loop.forIn {} initial scan) := by
  have sound : ∀ bound state, measure state = bound → invariant state →
      finished (Lean.Loop.forIn {} state scan) := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
      intro state measured valid
      rw [Lean.Loop.forIn_eq_of_monadTail]
      rcases step state valid with ⟨final, actual, terminal⟩ | ⟨next, actual, validNext, smaller⟩
      · simpa only [actual, bind, pure] using terminal
      · simp only [actual, bind]
        exact ih (measure next) (by omega) next rfl validNext
  exact sound (measure initial) initial rfl valid

omit [DecidableEq A] in
private theorem prepared_slice (map : DedupRangeMap A) (wf : map.WellFormed)
    (first last : Nat) (ordered : first ≤ last) (lastBound : last < map.entries.size)
    (range : ByteRange)
    (firstStart : map.entries[first].range.start = range.start)
    (lastStop : map.entries[last].range.stop = range.stop)
    (contents : UInt64 → A → Prop)
    (partition : ∀ byte data, map.MapAt byte data ↔ contents byte data) :
    (⟨map, (List.range (last + 1 - first)).toArray.map (· + first),
      map.entries.extract first (last + 1), .ok ()⟩ : IterMutResult A).PreparedFor range contents := by
  constructor
  · rfl
  · exact partition
  · intro cursor bounded
    have cursorBound : cursor < last + 1 - first := by simpa using bounded
    have posBound : cursor + first < map.entries.size := by omega
    have inside : cursor + first ≤ last := by omega
    refine ⟨cursor + first, map.entries[cursor + first], ?_, ?_, ?_, ?_, ?_⟩
    · rw [Array.getElem?_eq_some_iff]
      exact ⟨bounded, by simp⟩
    · rw [Array.getElem?_eq_some_iff]
      have extractBound : cursor < (map.entries.extract first (last + 1)).size := by
        simp only [Array.size_extract]
        omega
      refine ⟨extractBound, ?_⟩
      rw [Array.getElem_extract]
      congr 1
      omega
    · exact Array.getElem?_eq_some_iff.mpr ⟨posBound, rfl⟩
    · exact ⟨_, UInt64.le_refl _, wf_segment_positive wf _ posBound⟩
    · intro byte located
      constructor
      · rw [← firstStart]
        by_cases eq : cursor = 0
        · simpa [eq] using located.1
        · have order := wf_segment_order wf first (cursor + first) (by omega) posBound
          have nonempty := wf_segment_positive wf first (by omega)
          exact UInt64.le_trans (UInt64.le_trans (UInt64.le_of_lt nonempty) order) located.1
      · rw [← lastStop]
        by_cases eq : cursor + first = last
        · simpa only [eq] using located.2
        · have order := wf_segment_order wf (cursor + first) last (by omega) lastBound
          have nonempty := wf_segment_positive wf last lastBound
          exact UInt64.lt_of_lt_of_le located.2 (UInt64.le_trans order (UInt64.le_of_lt nonempty))
  · intro position segment byte present located requested
    rcases Array.getElem?_eq_some_iff.mp present with ⟨bound, value⟩
    subst segment
    have lo : first ≤ position := by
      apply Nat.le_of_not_lt
      intro outside
      have order := wf_segment_order wf position first outside (by omega)
      have h₁ := UInt64.lt_of_lt_of_le located.2 order
      rw [firstStart] at h₁
      exact (UInt64.not_lt.mpr requested.1) h₁
    have hi : position ≤ last := by
      apply Nat.le_of_not_lt
      intro outside
      have order := wf_segment_order wf last position outside bound
      have h₁ := UInt64.le_trans order located.1
      rw [lastStop] at h₁
      exact (UInt64.not_lt.mpr h₁) requested.2
    have cursorBound : position - first < last + 1 - first := by omega
    refine ⟨position - first, by simpa using cursorBound, ?_⟩
    have pos : position - first + first = position := by omega
    rw [Array.getElem?_eq_some_iff]
    exact ⟨by simpa using cursorBound, by simpa using pos⟩

private abbrev IterScanState (A : Type) :=
  DedupRangeMap A × Nat × Nat × Nat × Bool × Option DedupRangeMapError

private structure IterScanMap (original : DedupRangeMap A) (first : Nat) (range : ByteRange)
    (map : DedupRangeMap A) : Prop where
  wf : map.WellFormed
  size : map.size = original.size
  contents : ∀ byte data, map.MapAt byte data ↔ original.MapAt byte data
  firstBound : first < map.entries.size
  firstStart : map.entries[first].range.start = range.start

private structure IterScanActive (original : DedupRangeMap A) (first : Nat) (range : ByteRange)
    (map : DedupRangeMap A) (equalSince budget cursor : Nat) : Prop where
  mapValid : IterScanMap original first range map
  cursorBound : cursor < map.entries.size
  firstLeRun : first ≤ equalSince
  runLeCursor : equalSince ≤ cursor
  cursorStart : map.entries[cursor].range.start < range.stop
  sameRun : ∀ (_ : 0 < budget) (i : Nat) (_lower : equalSince ≤ i) (upper : i ≤ cursor),
    map.entries[i].data = map.entries[equalSince].data

private structure IterScanDone (original : DedupRangeMap A) (first : Nat) (range : ByteRange)
    (map : DedupRangeMap A) (cursor : Nat) : Prop where
  mapValid : IterScanMap original first range map
  afterFirst : first < cursor
  cursorBound : cursor ≤ map.entries.size
  lastStart : map.entries[cursor - 1].range.start < range.stop
  lastStop : range.stop ≤ map.entries[cursor - 1].range.stop

omit [DecidableEq A] in
private theorem scan_at_end {original map : DedupRangeMap A} {first : Nat} {range : ByteRange}
    {equalSince budget cursor : Nat}
    (active : IterScanActive original first range map equalSince budget cursor)
    (requestBound : range.stop ≤ original.size.bytes)
    (incomplete : (map.entries[cursor]'active.cursorBound).range.stop < range.stop) :
    cursor + 1 < map.entries.size := by
  have cursorBound := active.cursorBound
  by_cases next : cursor + 1 < map.entries.size
  · exact next
  · have size := size_bytes_last cursor (map := map) (by omega)
    have endpoint : map.size.bytes = original.size.bytes := congrArg Size.bytes active.mapValid.size
    rw [← endpoint, size] at requestBound
    exact False.elim (UInt64.not_lt.mpr requestBound incomplete)

omit [DecidableEq A] in
private theorem scan_finish_here {original map : DedupRangeMap A} {first : Nat} {range : ByteRange}
    {equalSince budget cursor : Nat}
    (active : IterScanActive original first range map equalSince budget cursor)
    (complete : range.stop ≤ (map.entries[cursor]'active.cursorBound).range.stop) :
    IterScanDone original first range map (cursor + 1) := by
  have cursorBound := active.cursorBound
  have firstLeRun := active.firstLeRun
  have runLeCursor := active.runLeCursor
  refine ⟨active.mapValid, by omega, by omega, ?_, ?_⟩
  · simpa using active.cursorStart
  · simpa using complete

omit [DecidableEq A] in
private theorem scan_next_start {original map : DedupRangeMap A} {first : Nat} {range : ByteRange}
    {equalSince budget cursor : Nat}
    (active : IterScanActive original first range map equalSince budget cursor)
    (next : cursor + 1 < map.entries.size)
    (incomplete : (map.entries[cursor]'active.cursorBound).range.stop < range.stop) :
    map.entries[cursor + 1].range.start < range.stop := by
  rw [← wf_segment_adjacent active.mapValid.wf cursor next]
  exact incomplete

private structure IterRunMerged (map : DedupRangeMap A) (lo hi : Nat)
    (out : DedupRangeMap A) : Prop where
  wf : out.WellFormed
  size : out.size = map.size
  contents : ∀ byte data, out.MapAt byte data ↔ map.MapAt byte data
  count : out.entries.size = map.entries.size - (hi - lo - 1)
  atRun : ∀ (loBound : lo < map.entries.size) (hiBound : hi - 1 < map.entries.size)
    (newBound : lo < out.entries.size),
    out.entries[lo] = { map.entries[lo] with range := {
      map.entries[lo].range with stop := map.entries[hi - 1].range.stop } }
  earlier : ∀ (i : Nat) (_ : i < lo) (oldBound : i < map.entries.size)
    (newBound : i < out.entries.size), out.entries[i] = map.entries[i]
  later : ∀ (i : Nat) (_ : lo < i) (oldBound : i + (hi - lo - 1) < map.entries.size)
    (newBound : i < out.entries.size), out.entries[i] = map.entries[i + (hi - lo - 1)]

omit [DecidableEq A] in
private theorem scan_map_after_merge {original map out : DedupRangeMap A}
    {first lo hi : Nat} {range : ByteRange}
    (geometry : IterScanMap original first range map)
    (merged : IterRunMerged map lo hi out) (firstLeRun : first ≤ lo) (runBeforeEnd : lo < hi)
    (runBound : hi ≤ map.entries.size) :
    IterScanMap original first range out := by
  have loBound : lo < out.entries.size := by rw [merged.count]; omega
  have firstBound : first < out.entries.size := by omega
  refine ⟨merged.wf, merged.size.trans geometry.size,
    fun byte data => (merged.contents byte data).trans (geometry.contents byte data),
    firstBound, ?_⟩
  by_cases atRun : first = lo
  · subst first
    rw [merged.atRun (by omega) (by omega) loBound]
    exact geometry.firstStart
  · rw [merged.earlier first (by omega) geometry.firstBound firstBound]
    exact geometry.firstStart

omit [DecidableEq A] in
private theorem scan_done_after_merge {original map out : DedupRangeMap A}
    {first lo budget cursor : Nat} {range : ByteRange}
    (active : IterScanActive original first range map lo budget cursor)
    (merged : IterRunMerged map lo (cursor + 1) out)
    (complete : range.stop ≤ (map.entries[cursor]'active.cursorBound).range.stop) :
    IterScanDone original first range out (lo + 1) := by
  have cursorBound := active.cursorBound
  have firstLeRun := active.firstLeRun
  have runLeCursor := active.runLeCursor
  have retained : lo < out.entries.size := by rw [merged.count]; omega
  have payload := merged.atRun (by omega) (by omega) retained
  refine ⟨scan_map_after_merge active.mapValid merged firstLeRun (by omega) (by omega),
    by omega, by omega, ?_, ?_⟩
  · simp only [Nat.add_sub_cancel, payload]
    change map.entries[lo].range.start < range.stop
    by_cases same : lo = cursor
    · subst cursor
      exact active.cursorStart
    · have order := wf_segment_order active.mapValid.wf lo cursor (by omega) cursorBound
      exact UInt64.lt_of_le_of_lt
        (UInt64.le_trans (UInt64.le_of_lt (wf_segment_positive active.mapValid.wf lo (by omega))) order)
        active.cursorStart
  · simp only [Nat.add_sub_cancel, payload]
    change range.stop ≤ map.entries[cursor + 1 - 1].range.stop
    simpa using complete

omit [DecidableEq A] in
private theorem scan_next_after_merge {original map out : DedupRangeMap A}
    {first lo budget cursor : Nat} {range : ByteRange}
    (active : IterScanActive original first range map lo budget cursor)
    (merged : IterRunMerged map lo (cursor + 1) out)
    (next : cursor + 1 < map.entries.size)
    (incomplete : (map.entries[cursor]'active.cursorBound).range.stop < range.stop) :
    IterScanActive original first range out (lo + 1) (budget + (cursor + 1 - lo - 1)) (lo + 1) := by
  have cursorBound := active.cursorBound
  have firstLeRun := active.firstLeRun
  have runLeCursor := active.runLeCursor
  have nextBound : lo + 1 < out.entries.size := by rw [merged.count]; omega
  have matched := merged.later (lo + 1) (by omega) (by omega) nextBound
  refine ⟨scan_map_after_merge active.mapValid merged firstLeRun (by omega) (by omega),
    nextBound, by omega, Nat.le_refl _, ?_, ?_⟩
  · simp only [matched, show lo + 1 + (cursor + 1 - lo - 1) = cursor + 1 by omega]
    exact scan_next_start active next incomplete
  · intro _ i lower upper
    have eq : i = lo + 1 := by omega
    subst i
    rfl

private def scanMeasure (state : IterScanState A) : Nat :=
  state.1.entries.size - state.2.2.2.1 + (if state.2.2.2.2.1 then 0 else 1)

private def scanInvariant (original : DedupRangeMap A) (first : Nat) (range : ByteRange)
    (state : IterScanState A) : Prop :=
  state.2.2.2.2.2 = none ∧
    if state.2.2.2.2.1 then IterScanDone original first range state.1 state.2.2.2.1
    else IterScanActive original first range state.1 state.2.1 state.2.2.1 state.2.2.2.1

private def scanTerminal (original : DedupRangeMap A) (first : Nat) (range : ByteRange)
    (state : IterScanState A) : Prop :=
  state.2.2.2.2.2 = none ∧ IterScanDone original first range state.1 state.2.2.2.1

private theorem scan_next_reset {original map : DedupRangeMap A}
    {first lo budget cursor : Nat} {range : ByteRange}
    (active : IterScanActive original first range map lo budget cursor)
    (next : cursor + 1 < map.entries.size)
    (incomplete : (map.entries[cursor]'active.cursorBound).range.stop < range.stop) :
    IterScanActive original first range map (cursor + 1) (budget - 1) (cursor + 1) := by
  have firstLeRun := active.firstLeRun
  have runLeCursor := active.runLeCursor
  refine ⟨active.mapValid, next, by omega, Nat.le_refl _, scan_next_start active next incomplete, ?_⟩
  intro _ i lower upper
  have same : i = cursor + 1 := by omega
  subst i
  rfl

private theorem scan_next_keep {original map : DedupRangeMap A}
    {first lo budget cursor : Nat} {range : ByteRange}
    (active : IterScanActive original first range map lo budget cursor)
    (next : cursor + 1 < map.entries.size)
    (incomplete : (map.entries[cursor]'active.cursorBound).range.stop < range.stop)
    (equal : ∀ (_ : 0 < budget), map.entries[cursor + 1].data =
      (map.entries[lo]'(by have := active.runLeCursor; omega)).data) :
    IterScanActive original first range map lo budget (cursor + 1) := by
  have runLeCursor := active.runLeCursor
  refine ⟨active.mapValid, next, active.firstLeRun, by omega, scan_next_start active next incomplete, ?_⟩
  intro available i lower upper
  by_cases same : i = cursor + 1
  · subst i
    exact equal available
  · exact active.sameRun available i lower (by omega)

/-- On an active cursor the scan either finishes the range or advances one
old segment. A completed run may replace several entries by one entry. -/
private theorem scan_iterate
    (original : DedupRangeMap A) (first : Nat) (range : ByteRange)
    (requestBound : range.stop ≤ original.size.bytes)
    (scan : Unit → IterScanState A → Id (ForInStep (IterScanState A)))
    (doneEq : ∀ map lo budget cursor,
      scan () (map, lo, budget, cursor, true, none) = .done (map, lo, budget, cursor, true, none))
    (activeEq : ∀ map lo budget cursor
      (active : IterScanActive original first range map lo budget cursor),
      let complete := decide (range.stop ≤ (map.entries[cursor]'active.cursorBound).range.stop)
      let merge := if complete then true else
        if h : cursor + 1 < map.entries.size then
          decide (map.entries[cursor + 1].data ≠ (map.entries[lo]'(by have := active.runLeCursor; omega)).data)
        else false
      let removed := cursor + 1 - lo - 1
      scan () (map, lo, budget, cursor, false, none) =
        if budget > 0 && merge then
          if removed > 0 then
            match mergeRun map.entries lo (cursor + 1) with
            | .ok entries => .yield (⟨entries⟩, cursor + 1 - removed, budget + removed,
                cursor + 1 - removed, complete, none)
            | .error error => .yield (map, cursor + 1, budget, cursor + 1, false, some error)
          else .yield (map, cursor + 1, budget - 1, cursor + 1, complete, none)
        else .yield (map, lo, budget, cursor + 1, complete, none))
    (mergeValid : ∀ map lo budget cursor
      (active : IterScanActive original first range map lo budget cursor),
      0 < budget → ∃ entries, mergeRun map.entries lo (cursor + 1) = .ok entries ∧
        IterRunMerged map lo (cursor + 1) ⟨entries⟩)
    (init : IterScanState A) (initial : scanInvariant original first range init) :
    scanTerminal original first range (Lean.Loop.forIn (m := Id) {} init scan) := by
  apply scan_loop_invariant scan scanMeasure (scanInvariant original first range)
    (scanTerminal original first range) _ init initial
  intro state valid
  rcases state with ⟨map, lo, budget, cursor, done, failure⟩
  rcases valid with ⟨failed, valid⟩
  change failure = none at failed
  subst failure
  cases done
  case true =>
    exact Or.inl ⟨_, doneEq map lo budget cursor, rfl, valid⟩
  case false =>
    change IterScanActive original first range map lo budget cursor at valid
    have runBefore := valid.runLeCursor
    have inside := valid.cursorBound
    have earliest := valid.firstLeRun
    have activeStep := activeEq map lo budget cursor valid
    dsimp only at activeStep
    by_cases complete : range.stop ≤ map.entries[cursor].range.stop
    · have terminal := scan_finish_here valid complete
      simp only [complete, decide_true] at activeStep
      by_cases available : 0 < budget
      · by_cases removed : 0 < cursor + 1 - lo - 1
        · rcases mergeValid map lo budget cursor valid available with ⟨entries, ran, merged⟩
          have adjust : cursor + 1 - (cursor + 1 - lo - 1) = lo + 1 := by omega
          simp only [available, removed, decide_true, ↓reduceIte, ran, adjust] at activeStep
          refine Or.inr ⟨_, activeStep, ⟨rfl, scan_done_after_merge valid merged complete⟩, ?_⟩
          dsimp [scanMeasure]
          have count := merged.count
          change entries.size = map.entries.size - (cursor + 1 - lo - 1) at count
          omega
        · simp only [available, removed, decide_true, ↓reduceIte] at activeStep
          exact Or.inr ⟨_, activeStep, ⟨rfl, terminal⟩, by simp [scanMeasure]; omega⟩
      · simp only [available, decide_false, ↓reduceIte] at activeStep
        exact Or.inr ⟨_, activeStep, ⟨rfl, terminal⟩, by simp [scanMeasure]; omega⟩
    · have incomplete : map.entries[cursor].range.stop < range.stop :=
        UInt64.not_le.mp complete
      have next := scan_at_end valid requestBound incomplete
      have loBound : lo < map.entries.size := by omega
      simp only [complete, decide_false, Bool.false_eq_true, ↓reduceIte, dite_eq_left next] at activeStep
      by_cases available : 0 < budget
      · by_cases differs : map.entries[cursor + 1].data ≠ map.entries[lo].data
        · simp only [available, decide_true, Bool.true_and, decide_eq_true_eq, ite_eq_left differs] at activeStep
          by_cases removed : 0 < cursor + 1 - lo - 1
          · rcases mergeValid map lo budget cursor valid available with ⟨entries, ran, merged⟩
            have adjust : cursor + 1 - (cursor + 1 - lo - 1) = lo + 1 := by omega
            simp only [removed, ↓reduceIte, ran, adjust] at activeStep
            refine Or.inr ⟨_, activeStep, ⟨rfl, scan_next_after_merge valid merged next incomplete⟩, ?_⟩
            dsimp [scanMeasure]
            have count := merged.count
            change entries.size = map.entries.size - (cursor + 1 - lo - 1) at count
            omega
          · simp only [removed, ↓reduceIte] at activeStep
            exact Or.inr ⟨_, activeStep, ⟨rfl, scan_next_reset valid next incomplete⟩,
              by simp [scanMeasure]; omega⟩
        · simp only [differs, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at activeStep
          have same := Classical.not_not.mp differs
          exact Or.inr ⟨_, activeStep, ⟨rfl, scan_next_keep valid next incomplete (fun _ => same)⟩,
            by simp [scanMeasure]; omega⟩
      · simp only [available, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at activeStep
        exact Or.inr ⟨_, activeStep, ⟨rfl, scan_next_keep valid next incomplete
          (fun h => False.elim (available h))⟩, by simp [scanMeasure]; omega⟩

omit [DecidableEq A] in
private theorem scan_merge_geometry (original map : DedupRangeMap A) (first : Nat)
    (range : ByteRange) (lo budget cursor : Nat)
    (active : IterScanActive original first range map lo budget cursor) (available : 0 < budget) :
    ∃ entries, mergeRun map.entries lo (cursor + 1) = .ok entries ∧
      IterRunMerged map lo (cursor + 1) ⟨entries⟩ := by
  have runBefore := active.runLeCursor
  have inside := active.cursorBound
  obtain ⟨out, ran, wf, size, contents, count, layout⟩ := mergeRun_valid map lo (cursor + 1)
    active.mapValid.wf (by omega) (by omega)
    (fun i _ lower upper => active.sameRun available i lower (by omega))
  cases out with
  | mk entries =>
    refine ⟨entries, ran, wf, size, contents, count, ?_, ?_, ?_⟩
    · intro loBound hiBound newBound
      simpa using layout lo newBound
    · intro i before oldBound newBound
      simpa [before] using layout i newBound
    · intro i past oldBound newBound
      simpa [show ¬i < lo by omega, show i ≠ lo by omega] using layout i newBound

omit [DecidableEq A] in
private theorem checkedEnd_of_add (offset len finish : Size)
    (added : offset.add len = .ok finish) :
    checkedEnd offset.bytes len.bytes = .ok finish.bytes := by
  simp only [checkedEnd, show Size.ofBytes offset.bytes = offset from by cases offset; rfl,
    show Size.ofBytes len.bytes = len from by cases len; rfl, added]
  rfl

omit [DecidableEq A] in
private theorem finish_after_start (offset len finish : Size)
    (added : offset.add len = .ok finish) (nonempty : len.bytes ≠ 0) :
    offset.bytes < finish.bytes := by
  by_cases overflow : offset.bytes + len.bytes < offset.bytes
  · simp [Size.add, overflow] at added
  · have noOverflow := overflow
    simp only [Size.add, ite_eq_right overflow] at added
    have value := congrArg Size.bytes (Except.ok.inj added)
    change offset.bytes + len.bytes = finish.bytes at value
    rw [← value]
    have offsetBound := UInt64.toNat_lt offset.bytes
    have lenBound := UInt64.toNat_lt len.bytes
    have positive : 0 < len.bytes.toNat := by
      apply Nat.pos_of_ne_zero
      intro zero
      apply nonempty
      exact UInt64.toNat_inj.mp zero
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at noOverflow ⊢
    omega

private theorem prepared_empty (map : DedupRangeMap A) (offset len finish : Size)
    (added : offset.add len = .ok finish) (empty : len.bytes = 0) :
    (map.iterMut offset len).PreparedFor ⟨offset.bytes, finish.bytes⟩ map.MapAt ∧
      (map.iterMut offset len).state = map := by
  simp only [Size.add, empty, UInt64.add_zero, UInt64.lt_irrefl, ↓reduceIte] at added
  have endpoint : offset.bytes = finish.bytes := congrArg Size.bytes (Except.ok.inj added)
  change offset.bytes = finish.bytes at endpoint
  have exactResult : map.iterMut offset len = ⟨map, #[], #[], .ok ()⟩ := by
    simp only [iterMut, iterMutWithClone, empty, beq_self_eq_true, ↓reduceIte, Id.run, pure, Pure.pure]
  rw [exactResult]
  refine ⟨⟨rfl, fun _ _ => Iff.rfl, ?_, ?_⟩, rfl⟩
  · intro cursor valid
    change cursor < 0 at valid
    omega
  · intro position segment byte located contained requested
    rcases requested with ⟨lower, upper⟩
    change offset.bytes ≤ byte at lower
    change byte < finish.bytes at upper
    rw [← endpoint] at upper
    exact False.elim (UInt64.not_lt.mpr lower upper)

omit [DecidableEq A] in
private theorem iter_split_start (map : DedupRangeMap A) (wf : map.WellFormed) (index : Nat)
    (bound : index < map.entries.size) (range : ByteRange)
    (contains : map.entries[index].range.Contains range.start) :
    ∃ entries didSplit, splitIndex map.entries index range.start id = .ok (entries, didSplit) ∧
      IterScanMap map (if didSplit then index + 1 else index) range ⟨entries⟩ := by
  obtain ⟨entries, split, ran, interior, count, shape, formed, size, contents⟩ :=
    splitIndex_valid map wf index bound range.start contains.1 (UInt64.le_of_lt contains.2)
  refine ⟨entries, split, ran, ?_⟩
  cases split
  case false =>
    have retained : index < entries.size := by simpa using (show index < entries.size from by simp [count, bound])
    have exactEntry : entries[index]'retained = map.entries[index] :=
      Option.some.inj (by simpa [getElem?_pos, retained, bound] using shape index)
    refine ⟨formed, size, contents, retained, ?_⟩
    change (entries[index]'retained).range.start = range.start
    rw [exactEntry]
    exact UInt64.le_antisymm contains.1 (UInt64.not_lt.mp (fun earlier =>
      Bool.noConfusion (interior.mpr ⟨earlier, contains.2⟩)))
  case true =>
    have retained : index + 1 < entries.size := by simp [count]; omega
    have exactEntry : entries[index + 1]'retained = { map.entries[index] with range.start := range.start } :=
      Option.some.inj (by simpa [getElem?_pos, retained, show ¬index + 1 < index by omega] using shape (index + 1))
    refine ⟨formed, size, contents, retained, ?_⟩
    change (entries[index + 1]'retained).range.start = range.start
    rw [exactEntry]

omit [DecidableEq A] in
private theorem iter_split_finish {original map : DedupRangeMap A} {first cursor : Nat}
    {range : ByteRange} (finished : IterScanDone original first range map cursor) :
    ∃ entries didSplit, splitIndex map.entries (cursor - 1) range.stop id = .ok (entries, didSplit) ∧
      let newMap : DedupRangeMap A := ⟨entries⟩
      ∃ lastBound : cursor - 1 < entries.size,
        IterScanMap original first range newMap ∧
        entries[cursor - 1].range.stop = range.stop := by
  have previous := finished.afterFirst
  have cursorBound := finished.cursorBound
  let last := cursor - 1
  have bound : last < map.entries.size := by omega
  have start := finished.lastStart
  have stop := finished.lastStop
  obtain ⟨entries, split, ran, interior, count, shape, formed, size, contents⟩ :=
    splitIndex_valid map finished.mapValid.wf last bound range.stop (UInt64.le_of_lt start) stop
  refine ⟨entries, split, ran, ?_⟩
  have retained : last < entries.size := by rw [count]; omega
  have firstBound : first < entries.size := by omega
  refine ⟨retained, ⟨formed, size.trans finished.mapValid.size, fun byte data =>
    (contents byte data).trans (finished.mapValid.contents byte data), firstBound, ?_⟩, ?_⟩
  · change entries[first].range.start = range.start
    cases split
    case false =>
      have entry : entries[first] = map.entries[first]'finished.mapValid.firstBound :=
        Option.some.inj (by simpa [getElem?_pos, firstBound, finished.mapValid.firstBound] using shape first)
      rw [entry]
      exact finished.mapValid.firstStart
    case true =>
      by_cases before : first < last
      · have entry : entries[first] = map.entries[first]'finished.mapValid.firstBound :=
          Option.some.inj (by simpa [getElem?_pos, firstBound, finished.mapValid.firstBound, before] using shape first)
        rw [entry]
        exact finished.mapValid.firstStart
      · have same : first = last := by omega
        subst first
        have entry : entries[last] = { map.entries[last] with range.stop := range.stop } :=
          Option.some.inj (by simpa [getElem?_pos, retained] using shape last)
        rw [entry]
        exact finished.mapValid.firstStart
  · change entries[last].range.stop = range.stop
    cases split
    case false =>
      have entry : entries[last] = map.entries[last] :=
        Option.some.inj (by simpa [getElem?_pos, retained, bound] using shape last)
      rw [entry]
      exact UInt64.le_antisymm (UInt64.not_lt.mp (fun earlier =>
        Bool.noConfusion (interior.mpr ⟨start, earlier⟩))) stop
    case true =>
      have entry : entries[last] = { map.entries[last] with range.stop := range.stop } :=
        Option.some.inj (by simpa [getElem?_pos, retained] using shape last)
      rw [entry]

omit [DecidableEq A] in
private theorem selectedSlice_valid (entries : Array (RangeMapSegment A)) (first last : Nat)
    (ordered : first ≤ last) (lastBound : last < entries.size) :
    selectedSlice entries first (last + 1) = .ok (entries.extract first (last + 1)) := by
  simp [selectedSlice, show ¬first > last + 1 by omega,
    show ¬last + 1 > entries.size by omega, pure, Pure.pure, Except.pure]

/-- For an in-bounds request whose end is representable, mutable iterator
preparation preserves the byte function and produces exactly the requested
entry slice. The prepared partition remains well-formed and the same size. -/
theorem iterMut_preparedFor (map : DedupRangeMap A) (offset len finish : Size)
    (wf : map.WellFormed) (added : offset.add len = .ok finish)
    (bounds : finish.bytes ≤ map.size.bytes) :
    let prepared := map.iterMut offset len
    prepared.PreparedFor ⟨offset.bytes, finish.bytes⟩ map.MapAt ∧
      prepared.state.WellFormed ∧ prepared.state.size = map.size := by
  by_cases empty : len.bytes = 0
  · obtain ⟨geometry, same⟩ := prepared_empty map offset len finish added empty
    exact ⟨geometry, by simpa only [same] using wf, by rw [same]⟩
  have increasing := finish_after_start offset len finish added empty
  have contained := UInt64.lt_of_lt_of_le increasing bounds
  obtain ⟨index, indexBound, found, contains⟩ := findOffset_in_range map offset.bytes wf contained
  let range : ByteRange := ⟨offset.bytes, finish.bytes⟩
  obtain ⟨entries, didSplit, startSplit, mapValid⟩ :=
    iter_split_start map wf index indexBound range contains
  change (map.iterMut offset len).PreparedFor range map.MapAt ∧ _
  unfold iterMut iterMutWithClone
  simp only [empty, beq_iff_eq, ↓reduceIte]
  rw [found]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  rw [startSplit]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  rw [checkedEnd_of_add offset len finish added]
  dsimp only [bind, Bind.bind, pure, Pure.pure]
  simp only [ForIn.forIn]
  name_full_range_scan
  let first := if didSplit then index + 1 else index
  have active : IterScanActive map first range ⟨entries⟩ first 3 first := by
    refine ⟨mapValid, mapValid.firstBound, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
    · rw [mapValid.firstStart]
      exact increasing
    · intro _ i lower upper
      have same : i = first := by omega
      subst i
      rfl
  have completed := scan_iterate map first range bounds scan
    (by intros; simp [scan])
    (by
      intro current lo budget cursor active
      have cursorBound := active.cursorBound
      have runBound : lo < current.entries.size := by have := active.runLeCursor; omega
      simp only [scan, Bool.not_false, Option.isNone_none, Bool.and_true,
        ↓reduceIte, segmentAt?_of_lt cursor cursorBound]
      by_cases complete : finish.bytes ≤ current.entries[cursor].range.stop
      · by_cases available : 0 < budget
        · by_cases removed : 0 < cursor + 1 - lo - 1
          · cases mergeRun current.entries lo (cursor + 1) <;>
              simp [range, complete, available, removed]
          · simp [range, complete, available, removed]
        · simp [range, complete, available]
      · have incomplete : current.entries[cursor].range.stop < range.stop :=
          UInt64.not_le.mp complete
        have next := scan_at_end active bounds incomplete
        have notLast : ¬ cursor + 1 ≥ current.entries.size := Nat.not_le_of_lt next
        simp only [range, complete, decide_false, Bool.not_false, notLast,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte,
          segmentAt?_of_lt (cursor + 1) next, segmentAt?_of_lt lo runBound, dite_eq_left next]
        by_cases available : 0 < budget
        · by_cases differs : current.entries[cursor + 1].data ≠ current.entries[lo].data
          · by_cases removed : 0 < cursor + 1 - lo - 1
            · cases mergeRun current.entries lo (cursor + 1) <;>
                simp [available, differs, removed, bne_iff_ne]
            · simp [available, differs, removed, bne_iff_ne]
          · simp [available, differs, bne_iff_ne]
        · simp [available])
    (fun current lo budget cursor => scan_merge_geometry map current first range lo budget cursor) (⟨entries⟩, first, 3, first, false, none) ⟨rfl, active⟩
  cases didSplit <;> simp only [first, Bool.false_eq_true, ↓reduceIte] at completed ⊢
  all_goals
    rcases completed with ⟨noError, terminal⟩
    obtain ⟨final, split, endSplit, lastBound, finalValid, lastStop⟩ := iter_split_finish terminal
    have ordered := Nat.le_sub_one_of_lt terminal.afterFirst
    have exactSlice := selectedSlice_valid final _ _ ordered lastBound
    simp only [range] at endSplit
    simp only [noError, endSplit, exactSlice]
    exact ⟨prepared_slice ⟨final⟩ finalValid.wf _ _ ordered lastBound range
      finalValid.firstStart lastStop map.MapAt finalValid.contents, finalValid.wf, finalValid.size⟩

end Miri.DataStructures.DedupRangeMap

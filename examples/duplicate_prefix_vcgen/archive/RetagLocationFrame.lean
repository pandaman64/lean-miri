import duplicate_prefix.RetagRangeFrame
import Miri.Verification.RetagPermissionSifa
import Miri.Verification.MutableReferenceRights

namespace DuplicatePrefix.RetagLocationFrame

open Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.Verification
open Miri.TreeBorrows.BorrowTree Miri.TreeBorrows.BorrowTree.ZeroProtection
open Miri.TreeBorrows.BorrowTree.MutationVerification
open Miri.Verification.MutableRetagFootprint Miri.Verification.RangeModifyLaw
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.RetagRangeFrame

/-- The old rows still supply each byte. Installing a child may change its
own permission. Both bookkeeping stages may change SIFA in any row. -/
def ByteFrameAt (grant : UInt64 → Tree.LocationState → Prop) (initial : DedupRangeMap LocationTree) (child : UniIndex)
    (point : UInt64) (location : LocationTree) : Prop :=
  (∃ prior, ValueAt initial point prior ∧
    ∀ index, index ≠ child → storedPermission location index = storedPermission prior index) ∧
  (∀ state, location.perms.get child = some state →
    grant point state)

private theorem set_child_preserves {grant : UInt64 → Tree.LocationState → Prop} (initial : DedupRangeMap LocationTree) (child : UniIndex)
    (point : UInt64) (location : LocationTree) (state : Tree.LocationState)
    (granted : grant point state)
    (ready : ByteFrameAt grant initial child point location) :
    ByteFrameAt grant initial child point {location with perms := location.perms.insert child state} := by
  obtain ⟨⟨prior, atByte, frame⟩, _⟩ := ready
  refine ⟨⟨prior, atByte, ?_⟩, ?_⟩
  · intro index different
    simpa only [storedPermission, Sparse.get_other _ _ _ _ different] using frame index different
  · intro actual found
    have same := Option.some.inj ((Sparse.get_same location.perms child state).symm.trans found)
    simpa only [← same] using granted

private theorem weakening_shape (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess) :
    (weakened tree index node strongest).locations.entries.map (·.range) =
      tree.locations.entries.map (·.range) := by
  simp [weakened, DedupRangeMap.modifyAll, Array.map_map, Function.comp_def]

private theorem weakening_byteFrame {grant : UInt64 → Tree.LocationState → Prop} (stable : ∀ point (old new : Tree.LocationState),
      old.permission = new.permission → old.accessed = new.accessed → grant point old → grant point new)
    (initial : DedupRangeMap LocationTree) (child : UniIndex)
    (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (strongest : IdempotentForeignAccess)
    (ready : EachByte tree.locations (ByteFrameAt grant initial child)) :
    EachByte (weakened tree index node strongest).locations (ByteFrameAt grant initial child) := by
  intro point position valid lo hi
  have inside : position < tree.locations.entries.size := by
    simpa [weakened, DedupRangeMap.modifyAll] using valid
  have constraints := weakened_storedPermission tree index node strongest position inside
  have original := ready point position inside
    (by simpa only [(constraints child).1] using lo) (by simpa only [(constraints child).1] using hi)
  obtain ⟨⟨prior, located, unchanged⟩, fresh⟩ := original
  refine ⟨⟨prior, located, ?_⟩, ?_⟩
  · intro query different
    exact (constraints query).2.trans (unchanged query different)
  · intro current found
    have childPermission := (constraints child).2
    simp only [storedPermission, found, Option.map_some] at childPermission
    cases earlier : tree.locations.entries[position].data.perms.get child with
    | none => simp [earlier] at childPermission
    | some state =>
      have pair := Option.some.inj (by simpa only [earlier, Option.map_some] using childPermission)
      exact stable point state current (congrArg Prod.fst pair).symm
        (congrArg Prod.snd pair).symm (fresh state earlier)

/-- Allocation size and partition geometry accompany the byte frame. -/
def FramedAt (grant : UInt64 → Tree.LocationState → Prop) (initial : DedupRangeMap LocationTree) (child : UniIndex) (current : BorrowTree) : Prop :=
  current.locations.size = initial.size ∧ current.locations.WellFormed ∧
    EachByte current.locations (ByteFrameAt grant initial child)

private theorem weakening_framed {grant : UInt64 → Tree.LocationState → Prop} (stable : ∀ point (old new : Tree.LocationState),
      old.permission = new.permission → old.accessed = new.accessed → grant point old → grant point new)
    (initial : DedupRangeMap LocationTree) (child : UniIndex)
    (current : BorrowTree) (index : UniIndex) (node : TreeNode) (sifa : IdempotentForeignAccess)
    (haveFrame : FramedAt grant initial child current) :
    FramedAt grant initial child (weakened current index node sifa) := by
  let next := weakened current index node sifa
  have shape := weakening_shape current index node sifa
  have sameSize : next.locations.size = current.locations.size := by
    rw [DuplicatePrefix.GeneralRangeMapState.size_from_ranges next.locations, shape,
      ← DuplicatePrefix.GeneralRangeMapState.size_from_ranges]
  exact ⟨sameSize.trans haveFrame.1, (partition_eq shape).mpr haveFrame.2.1,
    weakening_byteFrame stable initial child current index node sifa haveFrame.2.2⟩

private theorem ancestors_framed {grant : UInt64 → Tree.LocationState → Prop} (stable : ∀ point (old new : Tree.LocationState),
      old.permission = new.permission → old.accessed = new.accessed → grant point old → grant point new)
    (initial : DedupRangeMap LocationTree) (child start : UniIndex)
    (strongest : IdempotentForeignAccess) (fuel steps : Nat) (cursor : Option UniIndex)
    (current : BorrowTree) (ready : FramedAt grant initial child current) :
    weakenAncestorPre start strongest (FramedAt grant initial child) (fun _ _ => True)
      fuel steps cursor current := by
  induction fuel generalizing steps cursor current with
  | zero => trivial
  | succ fuel ih =>
    unfold weakenAncestorPre
    split
    · trivial
    · cases cursor with
      | none => exact ready
      | some index =>
        cases found : current.nodes.get index with
        | none => simp [found]
        | some node =>
          simp only [found]
          have next := weakening_framed stable initial child current index node strongest ready
          split
          · exact ih _ _ _ next
          · exact next

private theorem segments_framed {grant : UInt64 → Tree.LocationState → Prop} (stable : ∀ point (old new : Tree.LocationState),
      old.permission = new.permission → old.accessed = new.accessed → grant point old → grant point new)
    (initial : DedupRangeMap LocationTree)
    (offset : Size) (child : UniIndex) (parent : Option UniIndex) (held : Bool)
    (segments : List (RangeMapSegment Tree.LocationState)) (current : BorrowTree)
    (minimum : IdempotentForeignAccess)
    (fit : ∀ segment ∈ segments, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      start.bytes.toNat + (segment.range.stop - segment.range.start).toNat ≤ initial.size.bytes.toNat)
    (insideRights : ∀ segment ∈ segments, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      ∀ point, start.bytes.toNat ≤ point.toNat →
        point.toNat < (start.bytes + (segment.range.stop - segment.range.start)).toNat →
        grant point segment.data)
    (ready : FramedAt grant initial child current) :
    childSegmentsPre offset child parent held (FramedAt grant initial child) (fun _ _ => True)
      segments current minimum := by
  induction segments generalizing current minimum with
  | nil =>
    simp only [childSegmentsPre, finishChildPre]
    cases parent with
    | none => exact ready
    | some index =>
      unfold weakenAncestorsPre
      by_cases write : (minimum == .Write) = true
      · simpa only [write, ↓reduceIte] using ready
      · simp only [ite_eq_right write]
        exact ancestors_framed stable _ _ _ _ _ _ _ _ ready
  | cons segment rest ih =>
    simp only [childSegmentsPre, childSegmentPre]
    by_cases initialPermission : (!segment.data.permission.isInitial) = true
    · simp [initialPermission]
    · rw [ite_eq_right initialPermission]
      cases strongest : segment.data.permission.strongestIdempotentForeignAccess held with
      | ImpossibleProtectedReservedIM => trivial
      | Access expected =>
        by_cases mismatch : (segment.data.idempotentForeignAccess != expected) = true
        · simp [mismatch]
        · simp only [ite_eq_right mismatch]
          cases checked : Size.add (Size.ofBytes segment.range.start) offset with
          | error => trivial
          | ok start =>
            let length := Size.ofBytes (segment.range.stop - segment.range.start)
            let modify : ByteRange → LocationTree → LocationTree :=
              fun _ row => {row with perms := row.perms.insert child segment.data}
            have within := fit segment List.mem_cons_self start checked
            rw [← ready.1] at within
            have updated := modify_of_bounded_inside current.locations start length modify (ByteFrameAt grant initial child)
              ready.2.1 within ready.2.2
              (fun _ point row lo hi _ _ old => set_child_preserves initial child point row segment.data
                (insideRights segment List.mem_cons_self start checked point lo hi) old)
            change (match (current.locations.modifyRange start length modify).outcome with
              | .error _ => True
              | .ok () => childSegmentsPre offset child parent held (FramedAt grant initial child)
                (fun _ _ => True) rest {current with locations := (current.locations.modifyRange start length modify).state} _)
            rw [updated.1]
            exact ih _ _ (fun seg mem => fit seg (.tail _ mem))
              (fun seg mem => insideRights seg (.tail _ mem))
              ⟨updated.2.2.1.trans ready.1, updated.2.1, updated.2.2.2⟩

/-- Actual successful concrete child insertion preserves every old byte's
permission and preserves a local exclusive right for every materialized
new child byte. Missing child states use the separately preserved default. -/
theorem newChild_framed_at {grant : UInt64 → Tree.LocationState → Prop} (stable : ∀ point (old new : Tree.LocationState),
      old.permission = new.permission → old.accessed = new.accessed → grant point old → grant point new)
    (tree : BorrowTree) (offset : Size)
    (parentTag tag : Miri.Memory.BorTag) (parent child : UniIndex)
    (mapping : UniKeyMap Miri.Memory.BorTag) (inside : DedupRangeMap Tree.LocationState)
    (outside : Permission) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (well : tree.locations.WellFormed)
    (freshRows : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get child = none)
    (fit : ∀ segment ∈ inside.iterAll.toList, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      start.bytes.toNat + (segment.range.stop - segment.range.start).toNat ≤ tree.locations.size.bytes.toNat)
    (insideRights : ∀ segment ∈ inside.iterAll.toList, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      ∀ point, start.bytes.toNat ≤ point.toNat →
        point.toNat < (start.bytes + (segment.range.stop - segment.range.start)).toNat →
        grant point segment.data)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ()) :
    FramedAt grant tree.locations child (tree.newChild offset (.concrete parentTag) tag inside outside held).tree := by
  have distinct : parent ≠ child := by
    intro equal
    rw [equal, vacant] at present
    contradiction
  have start : EachByte tree.locations (ByteFrameAt grant tree.locations child) := by
    intro point position valid lower upper
    refine ⟨⟨_, ⟨position, valid, UInt64.le_iff_toNat_le.mp lower, UInt64.lt_iff_toNat_lt.mp upper, rfl⟩,
      fun _ _ => rfl⟩, ?_⟩
    intro state found
    rw [freshRows position valid] at found
    contradiction
  have pre : insertChildPre tree offset (.concrete parentTag) tag inside outside held
      (FramedAt grant tree.locations child) (fun _ _ => True) := by
    have parentLookup : tree.tagMapping.get parentTag = some parent := parentFound
    have parentNodeLookup : tree.nodes.get parent = some parentNode := present
    unfold insertChildPre
    simp only [mapped, parentLookup, Option.map_some]
    by_cases valid : (!outside.isInitial) = true
    · simp [valid]
    · rw [ite_eq_right valid]
      by_cases unique : outside.isUnique = true
      · simp [unique]
      · rw [ite_eq_right unique]
        cases strength : outside.strongestIdempotentForeignAccess held with
        | ImpossibleProtectedReservedIM => trivial
        | Access defaultSifa =>
          simp only [finishInsertedChildPre, Sparse.get_other _ _ _ _ distinct, parentNodeLookup]
          exact segments_framed stable _ _ _ _ _ _ _ _ fit insideRights ⟨rfl, well, start⟩
  have post := (insertChildPre_iff tree offset (.concrete parentTag) tag inside outside held
    (FramedAt grant tree.locations child) (fun _ _ => True)).mp pre
  simpa only [childResultPre, complete] using post

/-- Point-independent byte grants use the pointwise attachment frame. -/
def ByteFrameWith (grant : Tree.LocationState → Prop) :=
  ByteFrameAt (fun _ => grant)

/-- A point-independent attachment frame retains partition geometry. -/
def FramedWith (grant : Tree.LocationState → Prop) :=
  FramedAt (fun _ => grant)

/-- Materialized child states retain the supplied point-independent grant. -/
theorem newChild_framed_with {grant : Tree.LocationState → Prop} (stable : ∀ old new : Tree.LocationState,
      old.permission = new.permission → old.accessed = new.accessed → grant old → grant new)
    (tree : BorrowTree) (offset : Size)
    (parentTag tag : Miri.Memory.BorTag) (parent child : UniIndex)
    (mapping : UniKeyMap Miri.Memory.BorTag) (inside : DedupRangeMap Tree.LocationState)
    (outside : Permission) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (well : tree.locations.WellFormed)
    (freshRows : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get child = none)
    (fit : ∀ segment ∈ inside.iterAll.toList, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      start.bytes.toNat + (segment.range.stop - segment.range.start).toNat ≤ tree.locations.size.bytes.toNat)
    (insideRights : ∀ segment ∈ inside.iterAll.toList, grant segment.data)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ()) :
    FramedWith grant tree.locations child (tree.newChild offset (.concrete parentTag) tag inside outside held).tree :=
  newChild_framed_at (fun _ => stable) tree offset parentTag tag parent child mapping inside outside held
    mapped parentFound parentNode present vacant well freshRows fit
    (fun segment member _ _ _ _ _ => insideRights segment member) complete

/-- Per-byte attachment frame for a child granted mutable access. -/
def ByteFrame := ByteFrameWith (fun state => MutableReferenceRights.Granted state .LocalAccess true)

/-- Allocation partition and per-byte attachment frame for a mutable child. -/
def Framed := FramedWith (fun state => MutableReferenceRights.Granted state .LocalAccess true)

/-- Actual successful concrete child insertion preserves every old byte's
permission and preserves a local exclusive right for every materialized
new child byte. Missing child states use the separately preserved default. -/
theorem newChild_framed (tree : BorrowTree) (offset : Size)
    (parentTag tag : Miri.Memory.BorTag) (parent child : UniIndex)
    (mapping : UniKeyMap Miri.Memory.BorTag) (inside : DedupRangeMap Tree.LocationState)
    (outside : Permission) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (well : tree.locations.WellFormed)
    (freshRows : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get child = none)
    (fit : ∀ segment ∈ inside.iterAll.toList, ∀ start,
      Size.add (Size.ofBytes segment.range.start) offset = .ok start →
      start.bytes.toNat + (segment.range.stop - segment.range.start).toNat ≤ tree.locations.size.bytes.toNat)
    (insideRights : ∀ segment ∈ inside.iterAll.toList, MutableReferenceRights.Granted segment.data .LocalAccess true)
    (complete : (tree.newChild offset (.concrete parentTag) tag inside outside held).outcome = .ok ()) :
    Framed tree.locations child (tree.newChild offset (.concrete parentTag) tag inside outside held).tree := by
  exact newChild_framed_with
    (fun old new permission accessed granted =>
      (MutableReferenceRights.sifa_irrelevant old new permission.symm accessed.symm .LocalAccess true).mpr granted)
    tree offset parentTag tag parent child mapping inside outside held mapped parentFound parentNode
    present vacant well freshRows fit insideRights complete

#print axioms newChild_framed_with
#print axioms newChild_framed
end DuplicatePrefix.RetagLocationFrame

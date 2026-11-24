import duplicate_prefix.FrozenReborrowInputs

namespace DuplicatePrefix.RawHolderScope

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint
open FrozenReborrowInputs AsMutHolderScope

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The tree calculated by the associated read and a frozen attachment. -/
def frozenTree (tree : BorrowTree) (tags : ProtectedTags) (parentTag newTag : BorTag)
    (start length : Size) (inside : DedupRangeMap LocationState) (held : Bool) : BorrowTree :=
  let read := tree.performNormalAccessRange parentTag start length .Read tags .VisitChildrenOfAccessed
  (read.tree.newChild start (.concrete parentTag) newTag inside (.ReservedFrz false) held).tree

/-- The structural facts of the actual helper's installed mutable tag.
The protector's release outcome is determined by these data. -/
structure ReleaseStage (tree : BorrowTree) (tags : ProtectedTags) (source root : UniIndex)
    (start length : Size) : Prop where
  coherent : CoherentForest tree
  roots : tree.roots = #[root]
  hidden : ∃ node, tree.nodeAt source = some node ∧ node.isExposed = false
  materialized : MaterializedWithin tree source start.bytes (start.bytes+length.bytes)
  vacant : VacantRows tree
  ownership : OwnedOn (fun row => LocationRights tree row tags source)
    start.bytes (start.bytes+length.bytes) tree.locations

theorem fresh_mask_restored (tags : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (absent : tags.contains tag = false) :
    (tags.insert tag kind).remove tag = tags := by
  rcases tags with ⟨entries⟩
  unfold ProtectedTags.contains ProtectedTags.get at absent
  have unlisted : entries.find? (fun row => row.1 == tag) = none := by
    cases h : entries.find? (fun row => row.1 == tag) with
    | none => rfl
    | some row => simp [h] at absent
  have kept : entries.filter (fun row => row.1 != tag) = entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    have no := Array.find?_eq_none.mp unlisted row member
    simpa using no
  unfold ProtectedTags.insert ProtectedTags.remove
  simp only [Array.filter_push, kept, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

theorem finishRaw (tree : BorrowTree) (tags mask : ProtectedTags) (holderTag rawTag : BorTag)
    (holder selected root : UniIndex) (start length : Size)
    (restored : mask.remove rawTag = tags)
    (key : tree.indexOfTag rawTag = some selected)
    (holderKey : tree.indexOfTag holderTag = some holder)
    (holderHidden : (tree.nodeAt holder).map TreeNode.isExposed = some false)
    (paths : BetweenTags tree tags holder selected)
    (watch : MaterializedWithin tree holder start.bytes (start.bytes+length.bytes))
    (ready : ReleaseStage tree mask selected root start length) :
    let result := tree.releaseProtector rawTag mask
    result.status = .Released ∧ CoherentForest result.tree ∧
      result.tree.indexOfTag holderTag = some holder ∧
      (result.tree.nodeAt holder).map TreeNode.isExposed = some false ∧
      ∃ index, result.tree.indexOfTag rawTag = some index ∧ BetweenTags result.tree tags holder index ∧
        CopyHolderRights.Footprint result.tree tags index holder start.bytes (start.bytes+length.bytes) := by
  obtain ⟨node, found, hidden⟩ := ready.hidden
  have path : BetweenTags tree (mask.remove rawTag) holder selected := restored.symm ▸ paths
  obtain ⟨after, released, shape, formed, _, ancestry, footprint⟩ :=
    release_to_raw tree mask rawTag selected holder root node found key hidden ready.coherent ready.roots
      start.bytes (start.bytes+length.bytes) ready.materialized watch ready.vacant ready.ownership path
  dsimp only
  rw [released]
  have raw := (congrArg (fun t : BorrowTree => t.indexOfTag rawTag) shape).trans key
  have old := (congrArg (fun t : BorrowTree => t.indexOfTag holderTag) shape).trans holderKey
  have flag := (congrArg (fun t : BorrowTree => (t.nodeAt holder).map TreeNode.isExposed) shape).trans holderHidden
  exact ⟨rfl,formed,old,flag,selected,raw,restored ▸ ancestry,restored ▸ footprint⟩

/-- Carrier invariants for the original caller after its two real mutable
retags and the helper's active protector release. Each intermediate premise
describes the input structure to that stage. -/
theorem from_two_reborrows
    (tree : BorrowTree) (tags : ProtectedTags) (holderTag reservationTag rawTag : BorTag)
    (holder root : UniIndex) (start length : Size)
    (unheld : tags.contains reservationTag = false)
    (rawUnheld : tags.contains rawTag = false)
    (outerInside innerInside : DedupRangeMap LocationState)
    (outer : Stage tree tags holderTag reservationTag holder root start length outerInside false)
    (originalHidden : (tree.nodeAt holder).map TreeNode.isExposed = some false)
    (inner : let middle := frozenTree tree tags holderTag reservationTag start length outerInside false
      ∀ selected, middle.indexOfTag reservationTag = some selected →
        Stage middle (tags.insert rawTag .StrongProtector) reservationTag rawTag selected root
          start length innerInside true)
    (release : let middle := frozenTree tree tags holderTag reservationTag start length outerInside false
      let mutableTree := frozenTree middle (tags.insert rawTag .StrongProtector) reservationTag rawTag
        start length innerInside true
      ∀ index, mutableTree.indexOfTag rawTag = some index →
        ReleaseStage mutableTree (tags.insert rawTag .StrongProtector) index root start length) :
    let middle := frozenTree tree tags holderTag reservationTag start length outerInside false
    let mutableTree := frozenTree middle (tags.insert rawTag .StrongProtector) reservationTag rawTag start length innerInside true
    let raw := (mutableTree.releaseProtector rawTag (tags.insert rawTag .StrongProtector)).tree
    (mutableTree.releaseProtector rawTag (tags.insert rawTag .StrongProtector)).status = .Released ∧
      CoherentForest raw ∧
      raw.indexOfTag holderTag = some holder ∧
      (raw.nodeAt holder).map TreeNode.isExposed = some false ∧
      ∃ index, raw.indexOfTag rawTag = some index ∧
        BetweenTags raw tags holder index ∧
        CopyHolderRights.Footprint raw tags index holder start.bytes (start.bytes+length.bytes) := by
  have restored := fresh_mask_restored tags rawTag .StrongProtector rawUnheld
  let mask := tags.insert rawTag .StrongProtector
  let middle := frozenTree tree tags holderTag reservationTag start length outerInside false
  let mutableTree := frozenTree middle mask reservationTag rawTag start length innerInside true
  obtain ⟨_, _, reservation, reservationKey, still, originalScope, intermediate, firstKeys, firstExposure⟩ :=
    FrozenReborrowInputs.retag outer outer.parentPresent outer.scope (BetweenTags.self tree tags holder) unheld
  have selected : middle.indexOfTag reservationTag = some reservation := reservationKey
  have stage := inner reservation selected
  have firstDifferent : holderTag ≠ reservationTag := by
    intro same
    have stale := outer.fresh
    rw [← same, outer.parentFound] at stale
    contradiction
  have middleHolder : middle.indexOfTag holderTag = some holder :=
    (firstKeys holderTag firstDifferent).trans outer.parentFound
  have secondDifferent : holderTag ≠ rawTag := by
    intro same
    have stale := stage.fresh
    rw [← same, middleHolder] at stale
    contradiction
  obtain ⟨oldNode, originalNode⟩ := outer.parentPresent
  have originalFlag : oldNode.isExposed = false := by
    rw [originalNode, Option.map_some] at originalHidden
    exact Option.some.inj originalHidden
  have middleHidden : (middle.nodeAt holder).map TreeNode.isExposed = some false :=
    (firstExposure holder oldNode originalNode).trans (congrArg some originalFlag)
  obtain ⟨middleNode, foundMiddle⟩ := still
  change middle.nodeAt holder = some middleNode at foundMiddle
  have middleFlag : middleNode.isExposed = false := by
    rw [foundMiddle, Option.map_some] at middleHidden
    exact Option.some.inj middleHidden
  obtain ⟨_, _, rawIndex, rawKey, _, scope, returning, secondKeys, secondExposure⟩ :=
    FrozenReborrowInputs.retag stage ⟨middleNode,foundMiddle⟩ originalScope intermediate rawUnheld
  have key : mutableTree.indexOfTag rawTag = some rawIndex := rawKey
  have heldKey : mutableTree.indexOfTag holderTag = some holder :=
    (secondKeys holderTag secondDifferent).trans middleHolder
  have heldExposure : (mutableTree.nodeAt holder).map TreeNode.isExposed = some false :=
    (secondExposure holder middleNode foundMiddle).trans (congrArg some middleFlag)
  exact finishRaw mutableTree tags mask holderTag rawTag holder rawIndex root start length restored
    key heldKey heldExposure returning scope (release rawIndex key)

end DuplicatePrefix.RawHolderScope

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.RawHolderScope.finishRaw,
      ``DuplicatePrefix.RawHolderScope.from_two_reborrows] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved raw holder scope dependency {dependency}"

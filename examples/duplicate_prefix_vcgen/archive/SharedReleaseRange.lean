import duplicate_prefix.SharedHolderRead
import duplicate_prefix.RetagReleaseFootprint

namespace DuplicatePrefix.SharedRelease

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open SourceDomain ArchiveForestProjection RetagReleaseRights RetagReleaseFootprint ActiveRelease
open GeneralBorrowExposure GeneralBorrowProjection BorrowRangeAccess
open GeneralRangeMapOrigins GeneralRangeMapState Miri.Verification.RangeModifyLaw

set_option maxRecDepth 65536
set_option maxHeartbeats 1900000

theorem materializedRowIntersects (tree : BorrowTree) (child : UniIndex) (lower upper : UInt64)
    (coherent : CoherentForest tree) (materialized : MaterializedWithin tree child lower upper)
    (position : Nat) (inside : position < tree.locations.entries.size)
    (state : LocationState) (saved : tree.locations.entries[position].data.perms.get child = some state) :
    lower.toNat < upper.toNat ∧ tree.locations.entries[position].range.start.toNat < upper.toNat ∧
      lower.toNat < tree.locations.entries[position].range.stop.toNat := by
  let segment := tree.locations.entries[position]
  have nonempty : tree.locations.entries.size ≠ 0 := by omega
  have valid := coherent.ranges
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at valid
  have positive : segment.range.start < segment.range.stop := valid.2.1 position inside
  obtain ⟨lo, hi⟩ := materialized segment.range.start position inside
    (UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)) positive state saved
  exact ⟨Nat.lt_of_le_of_lt lo hi, hi, Nat.lt_of_le_of_lt lo (UInt64.lt_iff_toNat_lt.mp positive)⟩

private theorem replace_each_byte (property : UInt64 → LocationTree → Prop)
    (table : DedupRangeMap LocationTree) (position : Nat) (inside : position < table.entries.size)
    (next : LocationTree) (before : EachByte table property)
    (keeps : ∀ point, table.entries[position].range.start ≤ point → point < table.entries[position].range.stop →
      property point next) : EachByte (replaced table position inside next) property := by
  intro point index bounded lo hi
  have actual : index < table.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range table position inside next index actual] at lo hi
  by_cases equal : position = index
  · subst index
    simpa [replaced] using keeps point lo hi
  · simpa [replaced, Array.getElem_set, equal] using before point index actual lo hi

private def bounded_materialization (source : UniIndex) (lower upper : UInt64) (point : UInt64)
    (row : LocationTree) : Prop :=
  ∀ state, row.perms.get source = some state → lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat

/-- Release every materialized protected shared byte and retain exclusive
write authority for the earlier mutable holder. The shared permissions and
scope, absent-slot hygiene, and other protectors are structural premises. -/
theorem release_retains_holder_with_frame (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (child parent root : UniIndex) (node holder : TreeNode)
    (found : tree.nodeAt child = some node) (unexposed : node.isExposed = false)
    (holderFound : tree.nodeAt parent = some holder) (tagFound : tree.indexOfTag tag = some child)
    (chain : Ancestor tree parent child) (separate : parent ≠ child)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index child → ¬ Ancestor tree index parent → (tags.remove tag).contains data.tag = false)
    (unique : ∀ index data, tree.nodeAt index = some data → data.tag = tag → index = child)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (lower upper : UInt64) (extent : MaterializedWithin tree child lower upper) (vacant : VacantRows tree)
    (frozen : Every (fun row => ∀ state, row.perms.get child = some state → state.permission = .Frozen) tree.locations)
    (readerRights : OwnedOn (fun row => LocationAccessRights tree row tags child .Read) lower upper tree.locations)
    (holderRights : OwnedOn (fun row => LocationRights tree row (tags.remove tag) parent) lower upper tree.locations) :
    ∃ after, after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧
      OwnedOn (fun row => LocationRights after row (tags.remove tag) parent) lower upper after.locations ∧
      VacantRows after ∧
      (∀ watch, MaterializedWithin tree watch lower upper → MaterializedWithin after watch lower upper) ∧
      ∀ post failure, ProtectorReleaseWP.releasePre tag tags post failure tree ↔ post after := by
  obtain ⟨rank, bounded, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bounded, by
    intro index data present parent edge
    obtain ⟨up, held⟩ := coherent.parentPresent index data parent present edge
    exact ⟨up, held, decreases index data parent present edge⟩⟩
  have childData := forest_children tree coherent
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro index data present child member
    obtain ⟨off, childPresent, _⟩ := (childData index data present).2.1 child member
    exact ⟨off, childPresent⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data present rootEdge
    simpa using (coherent.rootEdges index data present).mp rootEdge
  have prepare (position : Nat) (inside : position < tree.locations.entries.size)
      (state : LocationState) (saved : tree.locations.entries[position].data.perms.get child = some state) :
      let loc := tree.locations.entries[position].data
      Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree loc tags).topology) ∧
        GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree loc tags) child.toNat .Read ∧
        LocationRights tree loc (tags.remove tag) parent := by
    obtain ⟨positive, start, stop⟩ := materializedRowIntersects tree child lower upper coherent extent position inside state saved
    exact ⟨⟨forest tree _ tags coherent.indexFits depth childData⟩,
      normal_access_owned tree _ tags child .Read depth node found coherent.indexFits
        (fun query absent => vacant query absent position inside)
        (readerRights position inside positive start stop), holderRights position inside positive start stop⟩
  have authorized : ∀ position < tree.locations.entries.size, ∃ slot,
      tree.locations.index position = .ok slot ∧ ReleaseOwnership tree child root tags slot := by
    intro position inside
    let slot := tree.locations.entries[position]
    refine ⟨slot, index_exact _ _ inside, ?_⟩
    intro state kind saved _ associated
    have isFrozen := frozen position inside state saved
    rw [isFrozen] at associated
    have kindRead : kind = .Read := (Option.some.inj associated).symm
    subst kind
    obtain ⟨⟨graph⟩, owner, _⟩ := prepare position inside state saved
    let view := source_normal_projection tree slot.data tags
    let component : GeneralBorrowExposedScopedNormal.Component view.topology child.toNat :=
      ⟨fun _ => True, trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
    have path := GeneralBorrowTerminal.ancestor_root_present view.topology graph
      (GeneralBorrowGraph.Present tree) (GeneralBorrowGraph.parents_closed tree slot.data tags depth)
      child.toNat root.toNat owner.anchorValid ⟨child, node, rfl, found⟩
      (fun index _ => GeneralBorrowGraph.unique_root tree slot.data tags root roots covered index)
    refine ⟨graph, ⟨component, fun index _ bound => owner.permissions index bound⟩, ?_⟩
    rw [path]
    exact index_self root
  let preserve (table : DedupRangeMap LocationTree) : Prop :=
    table.WellFormed ∧ table.size = tree.locations.size ∧
      OwnedOn (fun loc => LocationRights tree loc (tags.remove tag) parent) lower upper table ∧
      (∀ query, tree.nodeAt query = none → Every (fun row => row.perms.get query = none) table) ∧
      ∀ watch, MaterializedWithin tree watch lower upper →
        EachByte table (bounded_materialization watch lower upper)
  have step : ∀ table position slot, preserve table →
      table.index position = .ok slot → tree.locations.index position = .ok slot →
      position < table.entries.size → ReleaseOwnership tree child root tags slot →
      preserve (applyVisit {tree with locations := table} child tags position) := by
    intro table position slot stable currentIndex initialIndex inside _
    have originalInside : position < tree.locations.entries.size := by
      unfold DedupRangeMap.index at initialIndex
      split at initialIndex
      · rename_i segment known
        exact (Array.getElem?_eq_some_iff.mp known).1
      · contradiction
    have sameSlot : tree.locations.entries[position] = slot :=
      Except.ok.inj ((index_exact tree.locations position originalInside).symm.trans initialIndex)
    unfold applyVisit
    change preserve (match table.index position with
      | .error _ => table
      | .ok segment =>
        match segment.data.perms.get child with
        | none => table
        | some state =>
          match state.permission.associatedAccess with
          | none => table
          | some kind =>
            if state.accessed then
              let access := ({tree with locations := table} : BorrowTree).performTreeAccessAt
                segment.data (some child) kind tags .SkipChildrenOfAccessed segment.range
              (table.setAtPos position access.location).state
            else table)
    simp only [currentIndex]
    cases stored : slot.data.perms.get child with
    | none => simpa only [stored] using stable
    | some state =>
      have saved : tree.locations.entries[position].data.perms.get child = some state := by
        rwa [sameSlot]
      have initialFrozen := frozen position originalInside state saved
      simp only [initialFrozen, Permission.associatedAccess]
      cases accessed : state.accessed with
      | false => simpa only [accessed, Bool.false_eq_true, ↓reduceIte] using stable
      | true =>
        simp only [↓reduceIte, frame_access]
        have authorized := prepare position originalInside state saved
        rw [sameSlot] at authorized
        obtain ⟨⟨graph⟩, reader, writer⟩ := authorized
        let updated := (tree.performTreeAccessAt slot.data (some child) .Read
          tags .SkipChildrenOfAccessed slot.range).location
        have next : LocationRights tree updated (tags.remove tag) parent :=
          parent_after_read tree slot.data tags tag child parent root node found holder holderFound chain
            separate unheld unique depth coherent.indexFits childNodes roots covered graph reader writer .SkipChildrenOfAccessed slot.range
        rw [setAtPos_exact table position inside updated]
        refine ⟨replaced_wellFormed table position inside updated stable.1,
          (replaced_size table position inside updated).trans stable.2.1,
          owned_replaced _ lower upper table position inside updated stable.2.2.1 next, ?_, ?_⟩
        · intro query absent
          apply replaced_every _ table position inside updated (stable.2.2.2.1 query absent)
          have asNormal : updated = (tree.performNormalAccessAt slot.data child .Read tags
              .SkipChildrenOfAccessed).location :=
            GeneralBorrowRangePreserves.single_root_location tree slot.data tags child root .Read
              .SkipChildrenOfAccessed slot.range graph reader depth childNodes node found roots covered
          rw [asNormal]
          apply GeneralBorrowRangePreserves.normal_no_stale tree slot.data tags child query .Read
            .SkipChildrenOfAccessed depth childNodes node found absent
          rw [← sameSlot]
          exact vacant query absent position originalInside
        · intro watch initial
          apply replace_each_byte (bounded_materialization watch lower upper) table position inside updated
            (stable.2.2.2.2 watch initial)
          intro point lo hi _ _
          have currentSlot := Except.ok.inj ((index_exact table position inside).symm.trans currentIndex)
          rw [currentSlot] at lo hi
          exact extent point position originalInside
            (by rw [sameSlot]; exact lo) (by rw [sameSlot]; exact hi) state saved
  obtain ⟨after, shape, stable, exactRelease⟩ := releaseAll_frame tree tag child root tags tagFound
    roots depth childNodes node found unexposed authorized preserve
    ⟨coherent.ranges, rfl, holderRights, vacant, fun _ scope => scope⟩ step
  refine ⟨after, shape, ?_, stable.2.1, ?_, ?_, stable.2.2.2.2, exactRelease⟩
  · rw [shape]
    exact {coherent with ranges := stable.1}
  · intro position inside positive start stop
    let row := after.locations.entries[position].data
    change LocationRights after row (tags.remove tag) parent
    have grants := stable.2.2.1 position inside positive start stop
    rw [shape]
    exact rights_table tree after.locations row (tags.remove tag) parent grants

  · intro index absent position inside
    have unchanged : after.nodeAt index = tree.nodeAt index := by
      rw [shape]
      rfl
    exact stable.2.2.2.1 index (unchanged.symm.trans absent) position inside

/-- The release and exact writable row grants without the auxiliary frame. -/
theorem release_retains_holder (tree : BorrowTree) (tags : ProtectedTags) (tag : BorTag)
    (child parent root : UniIndex) (node holder : TreeNode)
    (found : tree.nodeAt child = some node) (unexposed : node.isExposed = false)
    (holderFound : tree.nodeAt parent = some holder) (tagFound : tree.indexOfTag tag = some child)
    (chain : Ancestor tree parent child) (separate : parent ≠ child)
    (unheld : ∀ index data, tree.nodeAt index = some data →
      Ancestor tree index child → ¬ Ancestor tree index parent → (tags.remove tag).contains data.tag = false)
    (unique : ∀ index data, tree.nodeAt index = some data → data.tag = tag → index = child)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (lower upper : UInt64) (extent : MaterializedWithin tree child lower upper) (vacant : VacantRows tree)
    (frozen : Every (fun row => ∀ state, row.perms.get child = some state → state.permission = .Frozen) tree.locations)
    (readerRights : OwnedOn (fun row => LocationAccessRights tree row tags child .Read) lower upper tree.locations)
    (holderRights : OwnedOn (fun row => LocationRights tree row (tags.remove tag) parent) lower upper tree.locations) :
    ∃ after, after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧
      OwnedOn (fun row => LocationRights after row (tags.remove tag) parent) lower upper after.locations ∧
      ∀ post failure, ProtectorReleaseWP.releasePre tag tags post failure tree ↔ post after := by
  obtain ⟨after, shape, well, capacity, rights, _, _, checked⟩ :=
    release_retains_holder_with_frame tree tags tag child parent root node holder found unexposed
      holderFound tagFound chain separate unheld unique coherent roots lower upper extent vacant frozen
      readerRights holderRights
  exact ⟨after, shape, well, capacity, rights, checked⟩

#print axioms release_retains_holder

end DuplicatePrefix.SharedRelease

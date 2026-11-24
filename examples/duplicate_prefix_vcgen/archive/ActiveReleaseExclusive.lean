import duplicate_prefix.RetagReleaseRights
import duplicate_prefix.ActiveReleaseRange
import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.RetagReleaseRights

open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection
open GeneralBorrowExposure GeneralBorrowProjection BorrowRangeAccess GeneralRangeMapState GeneralRangeMapOrigins
open ActiveRelease
open Miri.Verification

set_option maxRecDepth 65536
set_option maxHeartbeats 1200000

/-- A release visits only materialized, accessed bytes that have an associated
access kind. The exclusive grant must cover the actual visited bytes,
including any accessed bytes beyond the reference's immediate slice. -/
def ActiveByteRights (tree : BorrowTree) (tags : ProtectedTags) (source : UniIndex)
    (row : LocationTree) : Prop :=
  ∀ state kind, row.perms.get source = some state → state.accessed = true →
    state.permission.associatedAccess = some kind →
    LocationRights tree row tags source ∧
      (∀ index, tree.nodeAt index = none → row.perms.get index = none)

private theorem owned_replaced (predicate : α → Prop) (lower upper : UInt64)
    (table : DedupRangeMap α) (position : Nat) (bound : position < table.entries.size) (fresh : α)
    (before : OwnedOn predicate lower upper table) (after : predicate fresh) :
    OwnedOn predicate lower upper (replaced table position bound fresh) := by
  intro index bounded positive start stop
  have oldBound : index < table.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range table position bound fresh index oldBound] at start stop
  by_cases same : position = index
  · subst index
    simpa [replaced] using after
  · simpa [replaced, Array.getElem_set, same] using before index oldBound positive start stop

private theorem forest_children (tree : BorrowTree) (coherent : CoherentForest tree) :
    ∀ index node, tree.nodeAt index = some node →
      node.children.toList.Nodup ∧
        (∀ child ∈ node.children.toList, ∃ childNode,
          tree.nodeAt child = some childNode ∧ childNode.parent = some index) ∧
        (∀ child childNode, tree.nodeAt child = some childNode →
          childNode.parent = some index → child ∈ node.children.toList) := by
  intro index node present
  simpa using coherent.childEdges index node present

private theorem authorize (tree : BorrowTree) (tags : ProtectedTags)
    (source root : UniIndex) (node : TreeNode) (found : tree.nodeAt source = some node)
    (depth : ParentDepth tree.nodes) (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree) (slot : RangeMapSegment LocationTree)
    (grants : ActiveByteRights tree tags source slot.data) :
    ReleaseOwnership tree source root tags slot := by
  intro state kind lookup accessed assoc
  obtain ⟨right, clean⟩ := grants state kind lookup accessed assoc
  let projection := source_normal_projection tree slot.data tags
  have graph := forest tree slot.data tags coherent.indexFits depth (forest_children tree coherent)
  have writable := normal_write_owned tree slot.data tags source depth node found coherent.indexFits clean right
  have own := GeneralBorrowRangePreserves.owned_for_access projection source.toNat kind .Write
    (by simp) writable
  let component : GeneralBorrowExposedScopedNormal.Component projection.topology source.toNat :=
    ⟨fun _ => True, trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial⟩
  have path := GeneralBorrowTerminal.ancestor_root_present projection.topology graph
    (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree slot.data tags depth) source.toNat root.toNat
    own.anchorValid ⟨source, node, rfl, found⟩
    (fun index _ => GeneralBorrowGraph.unique_root tree slot.data tags root roots covered index)
  refine ⟨graph, ⟨component, fun index _ bound => own.permissions index bound⟩, ?_⟩
  rw [path]
  exact index_self root

private theorem frame_access (tree : BorrowTree) (table : DedupRangeMap LocationTree)
    (tags : ProtectedTags) (source : UniIndex) (kind : AccessKind)
    (slot : RangeMapSegment LocationTree) :
    ({tree with locations := table} : BorrowTree).performTreeAccessAt slot.data (some source)
      kind tags .SkipChildrenOfAccessed slot.range =
    tree.performTreeAccessAt slot.data (some source) kind tags .SkipChildrenOfAccessed slot.range := by
  cases tree
  rfl

private theorem ancestry_table (tree : BorrowTree) (table : DedupRangeMap LocationTree)
    (index source : UniIndex) :
    Ancestor ({tree with locations := table} : BorrowTree) index source ↔ Ancestor tree index source := by
  constructor
  · intro path
    induction path with
    | self => exact .self _
    | parent _ data found edge ih => exact .parent ih data found edge
  · intro path
    induction path with
    | self => exact .self _
    | parent _ data found edge ih => exact .parent ih data found edge

private theorem rights_table (tree : BorrowTree) (table : DedupRangeMap LocationTree) (row : LocationTree)
    (tags : ProtectedTags) (source : UniIndex) (before : LocationRights tree row tags source) :
    LocationRights {tree with locations := table} row tags source := by
  intro index data found
  obtain ⟨stored, indexed, own, allow⟩ := before index data found
  exact ⟨stored, indexed, fun path => own ((ancestry_table tree table index source).mp path),
    fun away => allow (fun path => away ((ancestry_table tree table index source).mpr path))⟩

/-- Operational protector release retains the raw reference's byte grant.
Both the release visit and cache write are performed with the protector live.
The global ledger can then drop that tag via `remove_preserves`. -/
theorem release_retains_owned (tree : BorrowTree) (tag : BorTag) (source root : UniIndex)
    (tags : ProtectedTags) (tagKnown : tree.indexOfTag tag = some source)
    (coherent : CoherentForest tree) (roots : tree.roots = #[root])
    (node : TreeNode) (found : tree.nodeAt source = some node) (unexposed : node.isExposed = false)
    (active : Every (ActiveByteRights tree tags source) tree.locations)
    (lower upper : UInt64) (owned : OwnedOn (fun row => LocationRights tree row tags source)
      lower upper tree.locations) :
    ∃ after, after = {tree with locations := after.locations} ∧
      CoherentForest after ∧ after.locations.size = tree.locations.size ∧
      OwnedOn (fun row => LocationRights after row (tags.remove tag) source) lower upper after.locations ∧
      ∀ post failure, ProtectorReleaseWP.releasePre tag tags post failure tree ↔ post after := by
  obtain ⟨rank, bound, decreases⟩ := coherent.parentDepth
  let depth : ParentDepth tree.nodes := ⟨rank, bound, by
    intro index data present parent edge
    obtain ⟨parentNode, parentKnown⟩ := coherent.parentPresent index data parent present edge
    exact ⟨parentNode, parentKnown, decreases index data parent present edge⟩⟩
  have childNodes : GeneralBorrowGraph.ChildNodes tree := by
    intro index data present child member
    obtain ⟨childNode, childKnown, _⟩ := (forest_children tree coherent index data present).2.1 child member
    exact ⟨childNode, childKnown⟩
  have covered : GeneralBorrowGraph.RootsCover tree := by
    intro index data present rootEdge
    simpa using (coherent.rootEdges index data present).mp rootEdge
  have authorized : ∀ position < tree.locations.entries.size, ∃ slot,
      tree.locations.index position = .ok slot ∧ ReleaseOwnership tree source root tags slot := by
    intro position inside
    exact ⟨tree.locations.entries[position], index_exact _ _ inside,
      authorize tree tags source root node found depth coherent roots covered _ (active position inside)⟩
  let good (table : DedupRangeMap LocationTree) : Prop :=
    table.WellFormed ∧ table.size = tree.locations.size ∧
      OwnedOn (fun row => LocationRights tree row tags source) lower upper table
  have keep : ∀ table position slot, good table →
      table.index position = .ok slot → tree.locations.index position = .ok slot →
      position < table.entries.size →
      ReleaseOwnership tree source root tags slot →
      good (applyVisit {tree with locations := table} source tags position) := by
    intro table position slot invariant indexed initialIndex inside _
    have originalInside : position < tree.locations.entries.size := by
      unfold DedupRangeMap.index at initialIndex
      split at initialIndex
      · rename_i segment known
        exact (Array.getElem?_eq_some_iff.mp known).1
      · contradiction
    have exactSlot : tree.locations.entries[position] = slot :=
      Except.ok.inj ((index_exact tree.locations position originalInside).symm.trans initialIndex)
    have grants : ActiveByteRights tree tags source slot.data := by
      rw [← exactSlot]
      exact active position originalInside
    unfold applyVisit
    change good (match table.index position with
      | .error _ => table
      | .ok segment =>
        match segment.data.perms.get source with
        | none => table
        | some permission =>
          match permission.permission.associatedAccess with
          | none => table
          | some kind =>
            if permission.accessed then
              let visited := ({tree with locations := table} : BorrowTree).performTreeAccessAt
                segment.data (some source) kind tags .SkipChildrenOfAccessed segment.range
              (table.setAtPos position visited.location).state
            else table)
    simp only [indexed]
    cases state : slot.data.perms.get source with
    | none => simpa only [state] using invariant
    | some permission =>
      cases association : permission.permission.associatedAccess with
      | none => simpa only [state, association] using invariant
      | some kind =>
        cases accessed : permission.accessed with
        | false => simpa only [state, association, accessed, Bool.false_eq_true, ↓reduceIte] using invariant
        | true =>
          simp only [association, accessed, ↓reduceIte, frame_access]
          obtain ⟨right, clean⟩ := grants permission kind state accessed association
          have graph := forest tree slot.data tags coherent.indexFits depth (forest_children tree coherent)
          have owner := normal_write_owned tree slot.data tags source depth node found coherent.indexFits clean right
          have next := GeneralBorrowRangePreserves.location_owned tree slot.data tags source root kind
            .Write .SkipChildrenOfAccessed slot.range (by simp) coherent.indexFits ⟨⟨graph⟩, owner⟩
            depth childNodes node found roots covered
          let out := (tree.performTreeAccessAt slot.data (some source) kind tags .SkipChildrenOfAccessed slot.range).location
          have retained : LocationRights tree out tags source :=
            normal_write_owned_to_location tree out tags source depth node found next.2
          rw [setAtPos_exact table position inside out]
          exact ⟨replaced_wellFormed table position inside out invariant.1,
            (replaced_size table position inside out).trans invariant.2.1,
            owned_replaced _ lower upper table position inside out invariant.2.2 retained⟩
  obtain ⟨after, shape, valid, exactRelease⟩ := releaseAll_frame tree tag source root tags tagKnown
    roots depth childNodes node found unexposed authorized good ⟨coherent.ranges, rfl, owned⟩ keep
  refine ⟨after, shape, ?_, valid.2.1, ?_, exactRelease⟩
  · rw [shape]
    exact {coherent with ranges := valid.1}
  · intro position inside positive start stop
    let row := after.locations.entries[position].data
    change LocationRights after row (tags.remove tag) source
    have grants := remove_preserves tree row source tags tag (valid.2.2 position inside positive start stop)
    rw [shape]
    exact rights_table tree after.locations row (tags.remove tag) source grants

end DuplicatePrefix.RetagReleaseRights

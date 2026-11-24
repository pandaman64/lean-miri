import duplicate_prefix.RetagLocationFrame
import Miri.TreeBorrows.RetagPolicy

namespace DuplicatePrefix.RetagFrozenChild

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.BorrowTree Miri.TreeBorrows.BorrowTree.ZeroProtection
open Miri.TreeBorrows.BorrowTree.MutationVerification
open DuplicatePrefix.RetagRangeFrame DuplicatePrefix.RetagLocationFrame

private theorem selected_size (offset : Size) (range : ByteRange) (capacity : Size)
    (ordered : range.start ≤ range.stop)
    (fits : offset.bytes.toNat + range.stop.toNat ≤ capacity.bytes.toNat) :
    ∃ start, Size.add (Size.ofBytes range.start) offset = .ok start ∧
      start.bytes.toNat + (range.stop - range.start).toNat ≤ capacity.bytes.toNat := by
  have orderedNat := UInt64.le_iff_toNat_le.mp ordered
  have nooverflow : range.start.toNat + offset.bytes.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (by omega) capacity.bytes.toNat_lt
  have sum : (range.start + offset.bytes).toNat = range.start.toNat + offset.bytes.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt nooverflow]
  have ordinary : ¬ range.start + offset.bytes < range.start := by
    intro impossible
    have less := UInt64.lt_iff_toNat_lt.mp impossible
    omega
  refine ⟨Size.ofBytes (range.start + offset.bytes), ?_, ?_⟩
  · simp [Size.add, Size.ofBytes, ordinary]
  · simp only [Size.ofBytes, sum, UInt64.toNat_sub_of_le _ _ ordered]
    omega

/-- The typed FnEntry policy for a frozen byte initializes an accessed
reservation or an accessed unique permission, with an empty SIFA. -/
def FrozenEntryState (state : Tree.LocationState) : Prop :=
  state = ⟨.ReservedFrz false, true, .None⟩ ∨ state = ⟨.Unique, true, .None⟩

theorem frozenEntry_of_policy (config : RetagPolicy.PolicyConfig)
    (policy : RetagPolicy.NewPermission) (state : Tree.LocationState)
    (selected : RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry config = some policy)
    (initialized : RetagPolicy.initialLocationState policy true = .ok state) :
    FrozenEntryState state := by
  obtain ⟨writes, suppressed⟩ := config
  cases writes <;> cases suppressed
  all_goals
    change some _ = some policy at selected
    obtain rfl := Option.some.inj selected
    change Except.ok _ = Except.ok state at initialized
    obtain rfl := Except.ok.inj initialized
    first | exact Or.inl rfl | exact Or.inr rfl

/-- Frozen FnEntry leaves a reserved default outside the argument and
installs the source's strong call protector. -/
theorem frozen_policy (config : RetagPolicy.PolicyConfig) (policy : RetagPolicy.NewPermission)
    (selected : RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry config = some policy) :
    policy.outsidePermission = .ReservedFrz false ∧ policy.protector = some .StrongProtector := by
  obtain ⟨writes, suppressed⟩ := config
  cases writes <;> cases suppressed
  all_goals
    change some _ = some policy at selected
    obtain rfl := Option.some.inj selected
    exact ⟨rfl, rfl⟩

/-- The uniform frozen partition produced by the typed retag hook meets the
segment conditions from the argument's allocation-relative bounds. -/
theorem uniform_segments (offset size capacity : Size) (state : Tree.LocationState)
    (bounded : offset.bytes.toNat + size.bytes.toNat ≤ capacity.bytes.toNat)
    (valid : FrozenEntryState state) :
    ∀ segment ∈ (DedupRangeMap.new size state).iterAll.toList,
      (segment.range.start ≤ segment.range.stop ∧
        offset.bytes.toNat + segment.range.stop.toNat ≤ capacity.bytes.toNat) ∧
      FrozenEntryState segment.data := by
  intro segment member
  by_cases empty : size.bytes = 0
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, empty] at member
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, beq_iff_eq, empty] at member
    subst segment
    exact ⟨⟨by simp, bounded⟩, valid⟩

/-- The initial frozen permission agrees with the source protection policy
and recorded SIFA. A reserved child can be protected or unprotected. -/
def FrozenChildState (held : Bool) (state : Tree.LocationState) : Prop :=
  state = ⟨.ReservedFrz false, true, if held then .None else .Read⟩ ∨
    state = ⟨.Unique, true, .None⟩

private theorem reserved_sifa (held : Bool) :
    Permission.strongestIdempotentForeignAccess (.ReservedFrz false) held =
      .Access (if held then .None else .Read) := by
  cases held <;> rfl

private theorem segments_safe (offset : Size) (child parent : UniIndex) (held : Bool)
    (segments : List (RangeMapSegment Tree.LocationState)) (current : BorrowTree)
    (minimum : IdempotentForeignAccess)
    (span : ∀ segment ∈ segments, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ current.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ segments, FrozenChildState held segment.data)
    (well : current.locations.WellFormed)
    (graph : ParentDepth current.nodes)
    (parentLive : ∃ node, current.nodes.get parent = some node)
    (rank : graph.depth parent < current.nodes.size) :
    childSegmentsPre offset child (some parent) held (fun _ => True) (fun _ _ => False)
      segments current minimum := by
  induction segments generalizing current minimum with
  | nil =>
    simp only [childSegmentsPre, finishChildPre]
    obtain ⟨node, found⟩ := parentLive
    have completed := ZeroProtection.succeeds current graph parent node found rank minimum
    rw [weakenAncestorsPre_iff]
    dsimp only
    rw [completed]
    trivial
  | cons segment rest ih =>
    have unique : Permission.strongestIdempotentForeignAccess .Unique held = .Access .None := rfl
    obtain ⟨ordered, fits⟩ := span segment List.mem_cons_self
    obtain ⟨start, checked, bounds⟩ := selected_size offset segment.range current.locations.size ordered fits
    let length := Size.ofBytes (segment.range.stop - segment.range.start)
    let modify : ByteRange → LocationTree → LocationTree :=
      fun _ row => {row with perms := row.perms.insert child segment.data}
    have updated := modify_of_bounded current.locations start length modify (fun _ _ => True)
      well bounds (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
    have recursive : ∀ sifa, childSegmentsPre offset child (some parent) held
        (fun _ => True) (fun _ _ => False) rest
        {current with locations := (current.locations.modifyRange start length modify).state} sifa := by
      intro sifa
      apply ih ({current with locations := (current.locations.modifyRange start length modify).state}) sifa ?_ (fun part mem => frozen part (.tail _ mem)) updated.2.1 graph parentLive rank
      intro part mem
      have here := span part (.tail _ mem)
      simpa only [updated.2.2.1] using here
    have material := frozen segment List.mem_cons_self
    rcases material with permission | permission
    all_goals
      simp only [childSegmentsPre, childSegmentPre, permission, Permission.isInitial,
        reserved_sifa, unique, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, bne_self_eq_false, checked]
      simp only [modify, length, permission] at updated recursive
      rw [updated.1]
      exact recursive _

private theorem segments_in_attachedTree (offset : Size) (child parent : UniIndex) (held : Bool)
    (inside : DedupRangeMap Tree.LocationState) (tree : BorrowTree)
    (mapping : UniKeyMap BorTag) (nodes : UniValMap TreeNode)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data)
    (well : tree.locations.WellFormed)
    (graph : ParentDepth nodes) (parentLive : ∃ node, nodes.get parent = some node)
    (rank : graph.depth parent < nodes.size) :
    childSegmentsPre offset child (some parent) held (fun _ => True) (fun _ _ => False) inside.iterAll.toList
      {tree with tagMapping := mapping, nodes := nodes} (if held then .None else .Read) := by
  exact segments_safe offset child parent held inside.iterAll.toList
    {tree with tagMapping := mapping, nodes := nodes} (if held then .None else .Read) span frozen well graph parentLive rank

/-- Allocate an available tag from the actual mapping, without assuming the
result of its insertion. Existing holes can be reused or the table extended. -/
theorem select_slot (tree : BorrowTree) (tag : BorTag)
    (fresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (appendAligned : tree.tagMapping.deassigned.back? = none →
      tree.tagMapping.mapping.size = tree.nodes.size)
    (reuseValid : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none) :
    ∃ mapping child, tree.tagMapping.insert tag = .Inserted mapping child ∧
      child.toNat ≤ tree.nodes.size ∧ tree.nodeAt child = none := by
  have unique : tree.tagMapping.get tag = none := fresh
  cases available : tree.tagMapping.deassigned.back? with
  | none =>
    have roomAtEnd := room available
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let mapping : UniKeyMap BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag, index)
      deassigned := tree.tagMapping.deassigned }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, UniIndex.ofNat?, roomAtEnd, unique, mapping, index]
    have atEnd : index.toNat = tree.nodes.data.size := by
      simp only [index, UniIndex.toNat, UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2 ^ 32)]
      exact appendAligned available
    refine ⟨mapping, index, inserted, Nat.le_of_eq atEnd, ?_⟩
    unfold BorrowTree.nodeAt UniValMap.get
    simp [atEnd]
  | some index =>
    let mapping : UniKeyMap BorTag := {
      mapping := (tree.tagMapping.mapping.filter fun row => row.1 != tag).push (tag, index)
      deassigned := tree.tagMapping.deassigned.pop }
    have inserted : tree.tagMapping.insert tag = .Inserted mapping index := by
      simp [UniKeyMap.insert, available, unique, mapping]
    obtain ⟨bounded, vacant⟩ := reuseValid index available
    exact ⟨mapping, index, inserted, Nat.le_of_lt bounded, vacant⟩

private theorem constructor_pre (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent child : UniIndex) (mapping : UniKeyMap BorTag)
    (inside : DedupRangeMap Tree.LocationState) (parentNode : TreeNode) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none)
    (next : BorrowTree → Prop) (failure : BorrowTree.ChildInsertError → BorrowTree → Prop)
    (tail : let node : TreeNode := {
        tag, parent := some parent, children := #[], defaultInitialPermission := .ReservedFrz false,
        defaultInitialSifa := if held then .None else .Read, isExposed := false }
      childSegmentsPre offset child (some parent) held next failure inside.iterAll.toList
        {tree with tagMapping := mapping, nodes := Append.attachedNodes tree.nodes child parent parentNode node}
        (if held then .None else .Read)) :
    insertChildPre tree offset (.concrete parentTag) tag inside (.ReservedFrz false) held next failure := by
  have distinct := Reuse.parent_not_vacant tree.nodes child parent parentNode vacant present
  have parentLookup : tree.tagMapping.get parentTag = some parent := parentFound
  have found : tree.nodes.get parent = some parentNode := present
  have defaultSifa : Permission.strongestIdempotentForeignAccess (.ReservedFrz false) held =
      .Access (if held then .None else .Read) := reserved_sifa held
  unfold insertChildPre
  simp only [mapped, parentLookup, Option.map_some, Permission.isInitial, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, Permission.isUnique, defaultSifa, finishInsertedChildPre,
    Sparse.get_other _ _ _ _ distinct, found]
  exact tail

private theorem completed_from_pre (result : BorrowTree.ChildInsertResult)
    (post : childResultPre (fun _ => True) (fun _ _ => False) result) :
    result.outcome = .ok () := by
  obtain ⟨tree, outcome⟩ := result
  cases outcome with
  | error error => contradiction
  | ok value =>
    cases value
    rfl

set_option maxHeartbeats 1200000 in
/-- Actual concrete frozen child construction succeeds for bounded frozen
segments and an acyclic allocator-selected vacant node. This includes both
the append and reusable-slot branches and all actual segmented writes. -/
theorem newChild_frozen_completes_with_mode (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent child : UniIndex)
    (mapping : UniKeyMap BorTag) (inside : DedupRangeMap Tree.LocationState) (held : Bool)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none) (validSlot : child.toNat ≤ tree.nodes.size)
    (well : tree.locations.WellFormed)
    (graph : ParentDepth tree.nodes) (rank : graph.depth parent < tree.nodes.size)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data) :
    (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held).outcome = .ok () := by
  let added : TreeNode := {
    tag, parent := some parent, children := #[], defaultInitialPermission := .ReservedFrz false,
    defaultInitialSifa := if held then .None else .Read, isExposed := false }
  have distinct : parent ≠ child := Reuse.parent_not_vacant tree.nodes child parent parentNode vacant present
  have lookup : (tree.nodes.insert child added).get parent = some parentNode :=
    (Sparse.get_other tree.nodes child parent added distinct).trans present
  let attached := Append.attachedNodes tree.nodes child parent parentNode added
  have attachParent : ∃ node, attached.get parent = some node := by
    let updated := {parentNode with children := parentNode.children.push child}
    exact ⟨updated, insert_existing_get_same _ parent parentNode updated lookup⟩
  have height : ∃ certificate : ParentDepth attached, certificate.depth parent < attached.size := by
    by_cases reuse : child.toNat < tree.nodes.size
    · exact ⟨Reuse.attached_depth _ graph child parent parentNode added reuse vacant present rfl rank,
        Reuse.attached_parent_strict _ graph child parent parentNode added reuse vacant present rfl rank⟩
    · have endSlot : child.toNat = tree.nodes.data.size := by
        change child.toNat = tree.nodes.size
        omega
      exact ⟨Append.attached_depth _ graph child parent parentNode added endSlot present rfl,
        Append.attached_parent_strict _ graph child parent parentNode added endSlot present rfl⟩
  obtain ⟨certificate, parentRank⟩ := height
  have tail := segments_in_attachedTree offset child parent held inside tree mapping attached
    span frozen well certificate attachParent parentRank
  have provePre := constructor_pre tree offset parentTag tag parent child mapping inside
    parentNode held mapped parentFound present vacant (fun _ => True) (fun _ _ => False) tail
  have post := (insertChildPre_iff tree offset (.concrete parentTag) tag inside
    (.ReservedFrz false) held (fun _ => True) (fun _ _ => False)).mp provePre
  exact completed_from_pre _ post

theorem newChild_frozen_completes (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent child : UniIndex)
    (mapping : UniKeyMap BorTag) (inside : DedupRangeMap Tree.LocationState)
    (mapped : tree.tagMapping.insert tag = .Inserted mapping child)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (parentNode : TreeNode) (present : tree.nodeAt parent = some parentNode)
    (vacant : tree.nodeAt child = none) (validSlot : child.toNat ≤ tree.nodes.size)
    (well : tree.locations.WellFormed)
    (graph : ParentDepth tree.nodes) (rank : graph.depth parent < tree.nodes.size)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenEntryState segment.data) :
    (tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) true).outcome = .ok () :=
  newChild_frozen_completes_with_mode tree offset parentTag tag parent child mapping inside true
    mapped parentFound parentNode present vacant validSlot well graph rank span frozen

/-- Bounded frozen permissions and the concrete tag allocator's consistency
give both actual insertion success and the byte-level frame. No completed
retag or range operation is an input premise. -/
theorem newChild_frozen_frame_with_mode (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (inside : DedupRangeMap Tree.LocationState) (held : Bool)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode)
    (tagFresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (appendAligned : tree.tagMapping.deassigned.back? = none →
      tree.tagMapping.mapping.size = tree.nodes.size)
    (reuseValid : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (well : tree.locations.WellFormed)
    (graph : ParentDepth tree.nodes) (rank : graph.depth parent < tree.nodes.size)
    (freshRows : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenChildState held segment.data) :
    ∃ mapping child, tree.tagMapping.insert tag = .Inserted mapping child ∧ tree.nodeAt child = none ∧
      let result := tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) held
      result.outcome = .ok () ∧ Framed tree.locations child result.tree := by
  obtain ⟨mapping, child, mapped, slot, vacant⟩ :=
    select_slot tree tag tagFresh room appendAligned reuseValid
  have completes := newChild_frozen_completes_with_mode tree offset parentTag tag parent child mapping inside held
    mapped parentFound parentNode present vacant slot well graph rank span frozen
  refine ⟨mapping, child, mapped, vacant, completes, ?_⟩
  apply newChild_framed tree offset parentTag tag parent child mapping inside (.ReservedFrz false) held
    mapped parentFound parentNode present vacant well (freshRows child vacant) ?_ ?_ completes
  · intro segment member start checked
    obtain ⟨ordered, bounded⟩ := span segment member
    obtain ⟨expected, calculated, fits⟩ := selected_size offset segment.range tree.locations.size ordered bounded
    have same := Except.ok.inj (calculated.symm.trans checked)
    simpa only [same] using fits
  · intro segment member
    rcases frozen segment member with exactState | exactState <;> rw [exactState] <;> rfl

theorem newChild_frozen_frame (tree : BorrowTree) (offset : Size)
    (parentTag tag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (inside : DedupRangeMap Tree.LocationState)
    (parentFound : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some parentNode)
    (tagFresh : tree.indexOfTag tag = none)
    (room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (appendAligned : tree.tagMapping.deassigned.back? = none →
      tree.tagMapping.mapping.size = tree.nodes.size)
    (reuseValid : ∀ index, tree.tagMapping.deassigned.back? = some index →
      index.toNat < tree.nodes.size ∧ tree.nodeAt index = none)
    (well : tree.locations.WellFormed)
    (graph : ParentDepth tree.nodes) (rank : graph.depth parent < tree.nodes.size)
    (freshRows : ∀ index, tree.nodeAt index = none →
      ∀ position (valid : position < tree.locations.entries.size),
        tree.locations.entries[position].data.perms.get index = none)
    (span : ∀ segment ∈ inside.iterAll.toList, segment.range.start ≤ segment.range.stop ∧
      offset.bytes.toNat + segment.range.stop.toNat ≤ tree.locations.size.bytes.toNat)
    (frozen : ∀ segment ∈ inside.iterAll.toList, FrozenEntryState segment.data) :
    ∃ mapping child, tree.tagMapping.insert tag = .Inserted mapping child ∧ tree.nodeAt child = none ∧
      let result := tree.newChild offset (.concrete parentTag) tag inside (.ReservedFrz false) true
      result.outcome = .ok () ∧ Framed tree.locations child result.tree :=
  newChild_frozen_frame_with_mode tree offset parentTag tag parent parentNode inside true
    parentFound present tagFresh room appendAligned reuseValid well graph rank freshRows span frozen

end DuplicatePrefix.RetagFrozenChild

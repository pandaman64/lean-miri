import Miri.TreeBorrows.TreeState

/-! Project sparse normal-access writeback into the next normal access. -/

namespace Miri.Verification.TreeNormalCommitWP

open Miri.TreeBorrows Miri.TreeBorrows.Tree

private structure Preserves (before after : NormalTreeState) : Prop where
  topology : after.topology = before.topology
  defaults : after.defaultStates = before.defaultStates
  protection : after.protectedNodes = before.protectedNodes
  size : after.locationStates.size = before.locationStates.size
  present : ∀ (i : Nat) (state : LocationState), before.locationStates[i]? = some (some state) →
    ∃ next, after.locationStates[i]? = some (some next)

private theorem Preserves.refl (tree : NormalTreeState) : Preserves tree tree :=
  ⟨rfl, rfl, rfl, rfl, fun _ state seen => ⟨state, seen⟩⟩

private theorem Preserves.trans {before middle after : NormalTreeState}
    (first : Preserves before middle) (second : Preserves middle after) :
    Preserves before after :=
  ⟨second.topology.trans first.topology, second.defaults.trans first.defaults,
    second.protection.trans first.protection, second.size.trans first.size,
    fun i state seen => by
      obtain ⟨updated, stored⟩ := first.present i state seen
      exact second.present i updated stored⟩

private theorem setState_preserves {before after : NormalTreeState} (node : Nat)
    (state : LocationState) (set : before.setState node state = some after) :
    Preserves before after := by
  unfold NormalTreeState.setState at set
  split at set
  · rename_i bounded
    cases set
    refine ⟨rfl, rfl, rfl, Array.size_set bounded, ?_⟩
    intro index old seen
    by_cases same : node = index
    · exact ⟨state, by simp [same]⟩
    · exact ⟨old, by simp [same, seen]⟩
  · contradiction

private theorem processEvents_preserves (before : NormalTreeState) (root : Nat)
    (kind : AccessKind) (events : List TraversalEvent) :
    Preserves before (before.processEvents root kind events).tree := by
  induction events generalizing before with
  | nil => exact Preserves.refl before
  | cons event rest ih =>
    unfold NormalTreeState.processEvents
    split
    · exact Preserves.refl before
    · rename_i old found
      split
      · exact Preserves.refl before
      · rename_i recorded record
        dsimp only
        split
        · exact Preserves.refl before
        · rename_i next set
          have step := setState_preserves _ _ set
          split
          · exact step.trans (ih next)
          all_goals exact step

private theorem index_value {position : Nat} {index : UniIndex}
    (found : UniIndex.ofNat? position = some index) : index.toNat = position := by
  unfold UniIndex.ofNat? at found
  split at found
  · rename_i bounded
    cases found
    simp only [UniIndex.toNat, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : position < 2 ^ 32)]
  · contradiction

private def writeNode (states : Array (Option LocationState)) (position : Nat)
    (before : LocationTree) : Id (ForInStep LocationTree) :=
  match states[position]? with
  | some (some state) =>
    match UniIndex.ofNat? position with
    | some index => pure (.yield { before with perms := before.perms.insert index state })
    | none => pure (.yield before)
  | _ => pure (.yield before)

private theorem writeNodes_get (states : Array (Option LocationState))
    (positions : List Nat) (before : LocationTree) (position : Nat) (index : UniIndex)
    (indexEq : UniIndex.ofNat? position = some index) :
    (Id.run (forIn positions before (writeNode states))).perms.get index =
      if position ∈ positions then (states[position]?.join).or (before.perms.get index)
      else before.perms.get index := by
  induction positions generalizing before with
  | nil => rfl
  | cons first rest ih =>
    rw [List.forIn_cons]
    by_cases same : first = position
    · subst first
      cases state : states[position]? with
      | none => simp [writeNode, state, ih]
      | some entry =>
        cases entry with
        | none => simp [writeNode, state, ih]
        | some value =>
          simp [writeNode, state, indexEq, ih, BorrowTree.ZeroProtection.Sparse.get_same]
    · have outside : position ≠ first := Ne.symm same
      cases state : states[first]? with
      | none => simp [writeNode, state, ih, outside]
      | some entry =>
        cases entry with
        | none => simp [writeNode, state, ih, outside]
        | some value =>
          cases candidate : UniIndex.ofNat? first with
          | none => simp [writeNode, state, candidate, ih, outside]
          | some target =>
            have distinct : index ≠ target := by
              intro equal
              exact outside ((index_value indexEq).symm.trans (equal ▸ index_value candidate))
            simp [writeNode, state, candidate, ih, outside,
              BorrowTree.ZeroProtection.Sparse.get_other _ _ _ _ distinct]

/-- The normal view has one permission slot for each node-table slot. -/
theorem normalView_size (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags) :
    (tree.normalView location tags).locationStates.size = tree.nodes.data.size :=
  Array.size_mapIdx

private theorem viewEntry (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (position : Nat) (index : UniIndex) (bounded : position < tree.nodes.data.size)
    (indexEq : UniIndex.ofNat? position = some index) :
    (tree.normalView location tags).locationStates[position]? = some (location.perms.get index) := by
  change (tree.nodes.data.mapIdx (fun position _ =>
    match UniIndex.ofNat? position with
    | none => none
    | some index => location.perms.get index))[position]? = _
  rw [Array.getElem?_mapIdx, Array.getElem?_eq_getElem bounded]
  simp only [indexEq, Option.map_some]

/-- For representable node positions and present, unexposed visited nodes, a
normal access commits successfully and reproduces its normal-tree state. -/
theorem normalView_after_access (tree : BorrowTree) (location : LocationTree)
    (start : UniIndex) (kind : AccessKind) (tags : ProtectedTags) (mode : ChildrenVisitMode)
    (bounded : tree.nodes.data.size ≤ 2 ^ 32)
    (unexposed : ∀ event ∈ (tree.performNormalAccessAt location start kind tags mode).access.visited,
      ∃ index node, UniIndex.ofNat? event.node = some index ∧
        tree.nodeAt index = some node ∧ node.isExposed = false) :
    let result := tree.performNormalAccessAt location start kind tags mode
    result.outcome = .ok () ∧ tree.normalView result.location tags = result.access.tree := by
  dsimp only
  obtain ⟨ok, committed⟩ := BorrowTree.RangeVerification.performNormalAccessAt_unexposed tree location start kind tags mode unexposed
  refine ⟨ok, ?_⟩
  let result := tree.performNormalAccessAt location start kind tags mode
  change tree.normalView result.location tags = result.access.tree
  change result.location = _ at committed
  have accessEq : result.access = (tree.normalView location tags).performAccess start.toNat kind mode := rfl
  have preserve : Preserves (tree.normalView location tags) result.access.tree := by
    rw [accessEq, NormalTreeState.performAccess]
    exact processEvents_preserves _ _ _ _
  have arraySize : result.access.tree.locationStates.size = tree.nodes.data.size :=
    preserve.size.trans (normalView_size tree location tags)
  have statesEq : (tree.normalView result.location tags).locationStates = result.access.tree.locationStates := by
    apply Array.ext_getElem?
    intro position
    by_cases within : position < tree.nodes.data.size
    · have indexEq : UniIndex.ofNat? position = some ⟨UInt32.ofNat position⟩ := by
        unfold UniIndex.ofNat?
        simp only [show position ≤ 4294967295 by omega, ↓reduceIte]
      rw [viewEntry _ _ _ _ _ within indexEq]
      have written := writeNodes_get result.access.tree.locationStates
        (List.range' 0 result.access.tree.locationStates.size) location position ⟨UInt32.ofNat position⟩ indexEq
      have member : position ∈ List.range' 0 result.access.tree.locationStates.size :=
        List.mem_range'.mpr ⟨position, by omega, by simp⟩
      have permission : result.location.perms.get ⟨UInt32.ofNat position⟩ =
          (result.access.tree.locationStates[position]?.join).or
            (location.perms.get ⟨UInt32.ofNat position⟩) := by
        rw [committed]
        simp only [member, ↓reduceIte] at written
        rw [← written]
        simp only [BorrowTree.RangeVerification.normalPermissionWriteback, Std.Legacy.Range.forIn_eq_forIn_range',
          Std.Legacy.Range.size, Nat.sub_zero, Nat.div_one, Nat.add_sub_cancel, Id.run, bind, Bind.bind,
          pure, Pure.pure]
        apply congrArg (fun next : LocationTree => next.perms.get ⟨UInt32.ofNat position⟩)
        congr 1
      rw [permission]
      have present := preserve.present position
      rw [viewEntry _ _ _ _ _ within indexEq] at present
      cases pool : result.access.tree.locationStates[position]? with
      | none => exact False.elim (by have := Array.getElem?_eq_none_iff.mp pool; omega)
      | some entry =>
        cases entry with
        | some state => rfl
        | none =>
          cases old : location.perms.get ⟨UInt32.ofNat position⟩ with
          | none => rfl
          | some state =>
            obtain ⟨next, kept⟩ := present state (by simp only [old])
            simp only [pool, Option.some.injEq, reduceCtorEq] at kept
    · rw [Array.getElem?_eq_none (by rw [normalView_size]; omega),
        Array.getElem?_eq_none (by omega)]
  have topology : (tree.normalView result.location tags).topology = result.access.tree.topology :=
    preserve.topology.symm
  have defaults : (tree.normalView result.location tags).defaultStates = result.access.tree.defaultStates :=
    preserve.defaults.symm
  have protection : (tree.normalView result.location tags).protectedNodes = result.access.tree.protectedNodes :=
    preserve.protection.symm
  generalize (tree.normalView result.location tags) = projected at statesEq topology defaults protection ⊢
  generalize result.access.tree = computed at statesEq topology defaults protection ⊢
  cases projected
  cases computed
  exact NormalTreeState.mk.injEq .. ▸ ⟨topology, defaults, protection, statesEq⟩

end Miri.Verification.TreeNormalCommitWP

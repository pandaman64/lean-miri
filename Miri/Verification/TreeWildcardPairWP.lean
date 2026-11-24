import Miri.Verification.TreeRangePointwiseWP

/-! Successful wildcard reads and writes in terms of the original roots and
the locations prepared from the initial range map. -/

namespace Miri.Verification.TreeWildcardPairWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree TreeRangeAccess

/-- Each stack position is an index and a flag recording whether its
children have already been checked. -/
abbrev PermissionStack := Array (UniIndex × Bool)

/-- Check the permissions and exposure updates for one traversal position.
Postorder reads the counters again after the children have run. -/
def permissionPositionPre (tree : BorrowTree) (root : UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool)
    (location : LocationTree) (exposed : Bool) (stack : PermissionStack)
    (finish : LocationTree → Bool → PermissionStack → Prop) : Prop :=
  match stack.back? with
  | none => False
  | some (index, afterChildren) =>
    match tree.nodes.get index with
    | none => False
    | some node =>
      let related := wildcardRelatedness location.exposedCache root index kind secondary false
      let oldState := (location.perms.get index).getD node.defaultLocationState
      if !afterChildren then
        let skip := match related.bind exactRelatedness? with
          | some rel =>
            match oldState.skipIfKnownNoop kind rel with
            | .SkipSelfAndChildren => true
            | .Recurse => false
          | none => false
        if skip then finish location exposed stack.pop
        else
          let next := node.children.foldl (fun frames child => frames.push (child, false))
            (stack.pop.push (index, true))
          finish location exposed next
      else
        match related with
        | none => False
        | some related =>
          let held := tags.contains node.tag
          let witnessed := node.isExposed && (oldState.permission.strongestAllowedLocalAccess held).allows kind
          let (perms, current) := location.perms.orInsert index node.defaultLocationState
          match exactRelatedness? related with
          | none => finish { location with perms } (exposed || witnessed) stack.pop
          | some rel =>
            match current.recordNewAccess kind rel with
            | .DebugAssertion => False
            | .Recorded recorded =>
              recorded.resultPre kind rel held fun
              | .Success updated transition =>
                let next := { location with perms := (perms.insert index recorded).insert index updated }
                if node.isExposed && !transition.isNoop then
                  location.exposedCache.updateExposurePre tree.nodes index
                    (oldState.permission.strongestAllowedLocalAccess held)
                    (updated.permission.strongestAllowedLocalAccess held)
                    (fun cache => finish { next with exposedCache := cache } (exposed || witnessed) stack.pop)
                    (fun _ _ => False)
                else finish next (exposed || witnessed) stack.pop
              | _ => False

private theorem permissionPositionPre_iff (tree : BorrowTree) (root : UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool)
    (location : LocationTree) (exposed : Bool) (stack : PermissionStack)
    (finish : LocationTree → Bool → PermissionStack → Prop) :
    RangeVerification.wildcardNodePre tree root none kind tags secondary
        ⟨location, exposed, .Completed, stack⟩
        (fun next => next.status = .Completed ∧ finish next.location next.hasValidExposed next.stack) ↔
      permissionPositionPre tree root kind tags secondary location exposed stack finish := by
  unfold RangeVerification.wildcardNodePre prepareWildcardNode permissionPositionPre
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  cases frame : stack.back? with
  | none => simp
  | some pair =>
    obtain ⟨index, afterChildren⟩ := pair
    cases afterChildren <;> cases present : tree.nodes.get index <;> simp only [present,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_and]
    · rename_i node
      have foldChildren :
          (forIn node.children (stack.pop.push (index, true))
            (fun child frames => ForInStep.yield (frames.push (child, false))) : Id PermissionStack) =
          node.children.foldl (fun frames child => frames.push (child, false))
            (stack.pop.push (index, true)) := by
        change (forIn node.children (stack.pop.push (index, true))
            (fun child frames => pure (.yield (frames.push (child, false)))) : Id PermissionStack) = _
        rw [Array.forIn_pure_yield_eq_foldl]
        rfl
      have folded := Iff.of_eq (congrArg (finish location exposed) foldChildren)
      cases related : wildcardRelatedness location.exposedCache root index kind secondary false
      · simpa only [Option.bind_none, Bool.false_eq_true, ↓reduceIte, true_and] using folded
      · rename_i relation
        cases exact : exactRelatedness? relation
        · simpa only [Option.bind_some, exact, Bool.false_eq_true, ↓reduceIte, true_and] using folded
        · rename_i rel
          cases skip : ((location.perms.get index).getD node.defaultLocationState).skipIfKnownNoop kind rel
          · simpa only [Option.bind_some, exact, skip, Bool.false_eq_true, ↓reduceIte, true_and] using folded
          · simp [exact, skip]
    · rename_i node
      cases related : wildcardRelatedness location.exposedCache root index kind secondary false
      · simp
      · rename_i relation
        simp only [Option.isNone_none, Bool.true_or, Bool.and_true]
        by_cases witnessed : (node.isExposed &&
          (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
            (tags.contains node.tag)).allows kind) = true
        all_goals
          simp only [witnessed, ↓reduceIte]
          cases exact : exactRelatedness? relation
          · simp
          · rename_i rel
            generalize location.perms.orInsert index node.defaultLocationState = inserted
            rcases inserted with ⟨perms, current⟩
            cases recorded : current.recordNewAccess kind rel with
            | DebugAssertion => simp [recorded]
            | Recorded recordedState =>
              simp only [recorded, Bool.false_eq_true, ↓reduceIte]
              rw [← Tree.LocationState.resultPre_iff, ← Tree.LocationState.resultPre_iff]
              cases recordedState.performAccess kind rel (tags.contains node.tag) <;>
                simp [RangeVerification.wildcardPermissionCommitPre,
                  Tree.LocationState.AccessResult.resultingState]

/-- Prove root success by consuming stack positions and composing only
successful permission transitions. The final primary-root condition is the
exposure witness accumulated in postorder. -/
private def permissionWalkPre (tree : BorrowTree) (root : UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool)
    (finish : LocationTree → Prop) :
    Nat → Nat → LocationTree → Bool → PermissionStack → Prop
  | 0, _, location, exposed, _ => (secondary = true ∨ exposed = true) ∧ finish location
  | fuel + 1, steps, location, exposed, stack =>
    if stack.isEmpty then (secondary = true ∨ exposed = true) ∧ finish location
    else if tree.nodes.size * 2 + 1 < steps + 1 then False
    else permissionPositionPre tree root kind tags secondary location exposed stack
      (permissionWalkPre tree root kind tags secondary finish fuel (steps + 1))

private theorem permissionWalkPre_iff (tree : BorrowTree) (root : UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool) (finish : LocationTree → Prop)
    (fuel steps : Nat) (visit : WildcardVisit) :
    RangeVerification.wildcardWalkPre
        (RangeVerification.wildcardScanPre tree root none kind tags secondary)
        (fun final => (finishWildcardVisit root secondary final.1).status = .Completed ∧
          finish (finishWildcardVisit root secondary final.1).location)
        fuel (visit, steps) ↔
      visit.status = .Completed ∧
        permissionWalkPre tree root kind tags secondary finish fuel steps visit.location
          visit.hasValidExposed visit.stack := by
  have finishIff (visit : WildcardVisit) :
      (finishWildcardVisit root secondary visit).status = .Completed ∧
        finish (finishWildcardVisit root secondary visit).location ↔
      visit.status = .Completed ∧ (secondary = true ∨ visit.hasValidExposed = true) ∧ finish visit.location := by
    rcases visit with ⟨location, exposed, status, stack⟩
    cases status <;> cases secondary <;> cases exposed <;> simp [finishWildcardVisit]
  induction fuel generalizing visit steps with
  | zero => exact finishIff visit
  | succ fuel ih =>
    rcases visit with ⟨location, exposed, status, stack⟩
    by_cases complete : status = .Completed
    · subst status
      by_cases empty : stack.isEmpty = true
      · simp only [RangeVerification.wildcardWalkPre, RangeVerification.wildcardScanPre, WildcardVisit.active,
          empty, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, permissionWalkPre, true_and]
        simpa only [true_and] using finishIff ⟨location, exposed, .Completed, stack⟩
      · simp only [RangeVerification.wildcardWalkPre, RangeVerification.wildcardScanPre, WildcardVisit.active,
          Bool.eq_false_iff.mpr empty, Bool.not_false, beq_self_eq_true, Bool.and_self, ↓reduceIte,
          permissionWalkPre, Bool.false_eq_true, true_and]
        by_cases limit : tree.nodes.size * 2 + 1 < steps + 1
        · simp only [gt_iff_lt, limit, ↓reduceIte]
          simpa using ih (steps + 1) ⟨location, exposed, .ParentCycle root, stack⟩
        · simp only [gt_iff_lt, limit, ↓reduceIte]
          have same : (fun next : WildcardVisit =>
                RangeVerification.wildcardWalkPre
                  (RangeVerification.wildcardScanPre tree root none kind tags secondary)
                  (fun final => (finishWildcardVisit root secondary final.1).status = .Completed ∧
                    finish (finishWildcardVisit root secondary final.1).location)
                  fuel (next, steps + 1)) =
              (fun next => next.status = .Completed ∧
                permissionWalkPre tree root kind tags secondary finish fuel (steps + 1)
                  next.location next.hasValidExposed next.stack) :=
            funext fun next => propext (ih _ _)
          rw [same]
          exact permissionPositionPre_iff tree root kind tags secondary location exposed stack _
    · simp only [RangeVerification.wildcardWalkPre, RangeVerification.wildcardScanPre, WildcardVisit.active,
        beq_iff_eq, Bool.and_eq_true, complete, and_false, ↓reduceIte, false_and]
      simp [finishIff, complete]

/-- Permission, exposure, and protector conditions for one root, including
the same bounded stack schedule as the wildcard semantics. -/
def permissionRootPre (tree : BorrowTree) (root : UniIndex) (location : LocationTree)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool) (finish : LocationTree → Prop) : Prop :=
  permissionWalkPre tree root kind tags secondary finish (tree.nodes.size * 2 + 2)
    0 location false #[(root, false)]

theorem permissionRootPre_iff (tree : BorrowTree) (root : UniIndex) (location : LocationTree)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool) (finish : LocationTree → Prop) :
    RangeVerification.wildcardPre tree location root none kind tags secondary
        (fun result => result.status = .Completed ∧ finish result.location) ↔
      permissionRootPre tree root location kind tags secondary finish := by
  unfold RangeVerification.wildcardPre permissionRootPre
  rw [permissionWalkPre_iff]
  simp

/-- Pull a successful location postcondition through the listed root positions.
The main root needs a valid exposed reference. The other roots receive the
location, including the permissions and exposure counters, left by earlier roots. -/
def rootsPre (tree : BorrowTree) (kind : AccessKind) (tags : ProtectedTags)
    (finish : LocationTree → Prop) : List Nat → LocationTree → Prop
  | [], location => finish location
  | position :: rest, location =>
    match tree.roots[position]? with
    | none => rootsPre tree kind tags finish rest location
    | some root =>
      permissionRootPre tree root location kind tags (position != 0)
        (rootsPre tree kind tags finish rest)

private theorem rootsPre_iff (tree : BorrowTree) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (range : ByteRange) (finish : LocationTree → Prop)
    (failure : BorrowTreeAccessStatus → LocationTree → Prop)
    (rejected : ∀ status after, ¬ failure (.WildcardFailure range status) after)
    (positions : List Nat) (inside : ∀ position ∈ positions, position < tree.roots.size)
    (location : LocationTree) :
    RangeVerification.otherRootsContract tree none kind tags mode range none none finish
        failure positions location ↔ rootsPre tree kind tags finish positions location := by
  induction positions generalizing location with
  | nil => rfl
  | cons position rest ih =>
    have valid := inside position (.head _)
    have present : tree.roots[position]? = some tree.roots[position] :=
      Array.getElem?_eq_getElem valid
    rw [RangeVerification.otherRootsContract_wildcard_cons _ _ _ _ _ _ _ _ _ _ _ present]
    simp only [rootsPre, present, ← permissionRootPre_iff, ← RangeVerification.wildcardPre_iff]
    split
    · simpa [*] using ih (fun index member => inside index (.tail _ member)) _
    · simp [*]

/-- A wildcard location succeeds with the given postcondition exactly when
the root obligations hold in order. Its success has no normal-access trace. -/
theorem location_success_iff (tree : BorrowTree) (location : LocationTree)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (finish : LocationTree → Prop) :
    RangeVerification.locationContract tree location none kind tags mode range
        (fun result => result.status = none ∧ finish result.location) ↔
      rootsPre tree kind tags finish (List.range' 0 tree.roots.size) location := by
  rw [RangeVerification.locationContract_wildcard_eq]
  simp only [true_and, reduceCtorEq, false_and]
  exact rootsPre_iff tree kind tags mode range finish _ (by simp) _ (by simp [List.mem_range']) location

/-- A two-root obligation keeps the read or write permission check for each
root separately, including the absence of the exposed-reference requirement at the second root. -/
theorem rootsPre_two (tree : BorrowTree) (first second : UniIndex) (roots : tree.roots = #[first, second])
    (kind : AccessKind) (tags : ProtectedTags) (finish : LocationTree → Prop) (location : LocationTree) :
    rootsPre tree kind tags finish (List.range' 0 tree.roots.size) location ↔
      permissionRootPre tree first location kind tags false (fun after =>
        permissionRootPre tree second after kind tags true finish) := by
  simp [roots, List.range', rootsPre]

/-- A childless root's authorization and resulting location from its
initial permission, exposure counters, and protector. The primary root
requires a valid exposed reference. A permission change at an exposed root
updates the cache before the continuation runs. -/
def leafPre (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool)
    (finish : LocationTree → Prop) : Prop :=
  let oldState := (location.perms.get root).getD node.defaultLocationState
  let held := tags.contains node.tag
  match wildcardRelatedness location.exposedCache root root kind secondary false with
  | none => False
  | some related =>
    let (perms, state) := location.perms.orInsert root node.defaultLocationState
    let witness := secondary = true ∨
      (node.isExposed && (oldState.permission.strongestAllowedLocalAccess held).allows kind) = true
    match exactRelatedness? related with
    | none => witness ∧ finish { location with perms }
    | some exact =>
      if oldState.skipIfKnownNoop kind exact = .SkipSelfAndChildren then secondary = true ∧ finish location
      else
        match state.recordNewAccess kind exact with
        | .DebugAssertion => False
        | .Recorded recorded =>
          recorded.resultPre kind exact held fun
          | .Success updated transition =>
            let next := { location with perms := (perms.insert root recorded).insert root updated }
            if node.isExposed && !transition.isNoop then
              location.exposedCache.updateExposurePre tree.nodes root
                (oldState.permission.strongestAllowedLocalAccess held)
                (updated.permission.strongestAllowedLocalAccess held)
                (fun cache => witness ∧ finish { next with exposedCache := cache }) (fun _ _ => False)
            else witness ∧ finish next
          | _ => False

private theorem wildcardWalkPre_empty (tree : BorrowTree) (root : UniIndex)
    (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool) (finish : WildcardVisit × Nat → Prop)
    (fuel : Nat) (visit : WildcardVisit) (steps : Nat) (empty : visit.stack = #[]) :
    RangeVerification.wildcardWalkPre
        (RangeVerification.wildcardScanPre tree root none kind tags secondary)
        finish fuel (visit, steps) ↔ finish (visit, steps) := by
  cases fuel <;>
    simp [RangeVerification.wildcardWalkPre, RangeVerification.wildcardScanPre, WildcardVisit.active, empty]

private theorem leafFinish (tree : BorrowTree) (root : UniIndex) (kind : AccessKind) (tags : ProtectedTags)
    (secondary : Bool) (finish : LocationTree → Prop) (fuel : Nat)
    (location : LocationTree) (exposed : Bool) (status : WildcardAccessStatus) (steps : Nat) :
    RangeVerification.wildcardWalkPre
        (RangeVerification.wildcardScanPre tree root none kind tags secondary)
        (fun final => (finishWildcardVisit root secondary final.1).status = .Completed ∧
          finish (finishWildcardVisit root secondary final.1).location)
        fuel (⟨location, exposed, status, #[]⟩, steps) ↔
      status = .Completed ∧ (secondary = true ∨ exposed = true) ∧ finish location := by
  rw [wildcardWalkPre_empty _ _ _ _ _ _ _ _ _ rfl]
  cases status <;> cases secondary <;> cases exposed <;> simp [finishWildcardVisit]

/-- A childless root can be discharged with permission and cache conditions
without expanding a traversal. This includes exposed primary roots and
secondary roots whose permissions may see a foreign or ambiguous access. -/
theorem leafPre_iff (tree : BorrowTree) (location : LocationTree) (root : UniIndex)
    (node : TreeNode) (kind : AccessKind) (tags : ProtectedTags) (secondary : Bool)
    (finish : LocationTree → Prop) (present : tree.nodes.get root = some node)
    (leaf : node.children = #[]) :
    RangeVerification.wildcardPre tree location root none kind tags secondary
        (fun result => result.status = .Completed ∧ finish result.location) ↔
      leafPre tree location root node kind tags secondary finish := by
  unfold RangeVerification.wildcardPre leafPre
  have firstBound : ¬ tree.nodes.size * 2 + 1 < 1 := by omega
  have secondBound : ¬ tree.nodes.size * 2 + 1 < 2 := by
    intro limit
    have zero : tree.nodes.data.size = 0 := by
      change tree.nodes.data.size * 2 + 1 < 2 at limit
      omega
    simp [UniValMap.get, Array.getElem?_eq_none (by omega : tree.nodes.data.size ≤ root.toNat)] at present
  have emptyForIn (visit : UniIndex → Array (UniIndex × Bool) → Id (ForInStep (Array (UniIndex × Bool)))) :
      forIn (#[] : Array UniIndex) #[(root, true)] visit = #[(root, true)] := rfl
  have pushed : (#[].push (root, true)) = #[(root, true)] := rfl
  have stackFacts : ∀ phase : Bool,
      (#[(root, phase)] : Array (UniIndex × Bool)).back? = some (root, phase) ∧
      (#[ (root, phase)] : Array (UniIndex × Bool)).isEmpty = false ∧
      (#[ (root, phase)] : Array (UniIndex × Bool)).pop = #[] := fun _ => ⟨rfl, rfl, rfl⟩
  rw [show tree.nodes.size * 2 + 2 = (tree.nodes.size * 2) + 1 + 1 by omega]
  cases related : wildcardRelatedness location.exposedCache root root kind secondary false <;>
    simp only [RangeVerification.wildcardWalkPre, RangeVerification.wildcardScanPre,
      WildcardVisit.active, (stackFacts false).1, (stackFacts false).2.1, (stackFacts false).2.2,
      (stackFacts true).1, (stackFacts true).2.1, (stackFacts true).2.2,
      Bool.not_false, beq_self_eq_true, Bool.and_self, ↓reduceIte, Nat.zero_add, firstBound, secondBound,
      RangeVerification.wildcardNodePre, prepareWildcardNode, Id.run, present, related,
      Option.bind_some, Option.bind_none, leaf, bind, Bind.bind, pure, Pure.pure, pushed, emptyForIn,
      Bool.not_true, Bool.false_eq_true, Option.isNone_none, Bool.true_or, Bool.and_true, leafFinish, reduceCtorEq, false_and]
  case some relation =>
    let exposed := node.isExposed = true ∧
      (((location.perms.get root).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
        (tags.contains node.tag)).allows kind = true
    have sameWitness : ((node.isExposed &&
        (((location.perms.get root).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
          (tags.contains node.tag)).allows kind) = true) = exposed := by simp [exposed]
    cases exact : exactRelatedness? relation with
    | none =>
      by_cases witness : exposed <;> simp [exact, present, related, sameWitness, witness, leafFinish]
    | some rel =>
      cases skip : ((location.perms.get root).getD node.defaultLocationState).skipIfKnownNoop kind rel with
      | SkipSelfAndChildren => cases secondary <;> simp [skip, finishWildcardVisit]
      | Recurse =>
        simp only [exact, skip, reduceCtorEq, Bool.false_eq_true, ↓reduceIte, (stackFacts true).1,
          (stackFacts true).2.1, (stackFacts true).2.2, Bool.not_false, Bool.not_true,
          beq_self_eq_true, Bool.and_self, present, related]
        generalize location.perms.orInsert root node.defaultLocationState = inserted
        rcases inserted with ⟨perms, current⟩
        cases recorded : current.recordNewAccess kind rel with
        | DebugAssertion =>
          by_cases witness : exposed <;> simp [sameWitness, witness, leafFinish]
        | Recorded recordedState =>
          by_cases witness : exposed
          all_goals
            simp only [sameWitness, witness, ↓reduceIte]
            rw [← Tree.LocationState.resultPre_iff, ← Tree.LocationState.resultPre_iff]
            cases recordedState.performAccess kind rel (tags.contains node.tag) <;>
              simp [RangeVerification.wildcardPermissionCommitPre, leafFinish,
                Tree.LocationState.AccessResult.resultingState]

/-- Every index recorded in the roots array resolves to a childless node. -/
def LeafForest (tree : BorrowTree) : Prop :=
  ∀ root ∈ tree.roots, ∃ node, tree.nodes.get root = some node ∧ node.children = #[]

/-- A forest of leaves needs only the permission and exposure conditions
for its roots, in the order they appear in the original array. -/
def leafRootsPre (tree : BorrowTree) (kind : AccessKind) (tags : ProtectedTags)
    (finish : LocationTree → Prop) : List Nat → LocationTree → Prop
  | [], location => finish location
  | position :: rest, location =>
    match tree.roots[position]? with
    | none => leafRootsPre tree kind tags finish rest location
    | some root =>
      match tree.nodes.get root with
      | none => False
      | some node =>
        leafPre tree location root node kind tags (position != 0)
          (leafRootsPre tree kind tags finish rest)

theorem rootsPre_iff_leafForest (tree : BorrowTree) (forest : LeafForest tree)
    (kind : AccessKind) (tags : ProtectedTags) (finish : LocationTree → Prop)
    (positions : List Nat) (location : LocationTree) :
    rootsPre tree kind tags finish positions location ↔
      leafRootsPre tree kind tags finish positions location := by
  induction positions generalizing location with
  | nil => rfl
  | cons position rest ih =>
    cases found : tree.roots[position]? with
    | none => simpa only [rootsPre, leafRootsPre, found] using ih location
    | some root =>
      have member := Array.mem_of_getElem? (xs := tree.roots) found
      obtain ⟨node, present, leaf⟩ := forest root member
      simp only [rootsPre, leafRootsPre, found, present]
      rw [← permissionRootPre_iff, leafPre_iff _ _ _ _ _ _ _ _ present leaf]
      have continuations :
          rootsPre tree kind tags finish rest = leafRootsPre tree kind tags finish rest :=
        funext fun after => propext (ih after)
      rw [continuations]

/-- Each cursor is checked against its own prepared location. Any read result
used by the writer is the location produced by the ordered root obligations. -/
def slotPre (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (kind : AccessKind) (tags : ProtectedTags) (cursor : Nat) (finish : LocationTree → Prop) : Prop :=
  ∃ position segment, prepared.positions[cursor]? = some position ∧
    prepared.segments[cursor]? = some segment ∧ position < prepared.state.entries.size ∧
    rootsPre tree kind tags finish (List.range' 0 tree.roots.size) segment.data

/-- Retain the successful wildcard result with its location and empty diagnostics. -/
theorem completedLocation_iff (tree : BorrowTree) (location : LocationTree)
    (kind : AccessKind) (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (finish : TreeLocationAccessAtResult → Prop) :
    RangeVerification.locationContract tree location none kind tags mode range
        (fun result => finish result ∧ result.status.getD .Completed = .Completed) ↔
      rootsPre tree kind tags (fun after => finish ⟨after, none, none⟩)
        (List.range' 0 tree.roots.size) location := by
  rw [RangeVerification.locationContract_wildcard_eq]
  simp only [Option.getD_none, and_true]
  exact rootsPre_iff tree kind tags mode range _ _ (by simp) _
    (by simp [List.mem_range']) location

private theorem readSlot_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (cursor : Nat)
    (retained : TreeLocationAccessAtResult) :
    SnapshotAuthorized tree prepared none .Read tags mode cursor retained ↔
      slotPre tree prepared .Read tags cursor (fun after => ⟨after, none, none⟩ = retained) := by
  simp only [SnapshotAuthorized, slotPre, completedLocation_iff]

private theorem writeSlot_iff (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (tags : ProtectedTags) (mode : Tree.ChildrenVisitMode) (cursor : Nat) :
    SlotAuthorized tree prepared none .Write tags mode cursor ↔
      slotPre tree prepared .Write tags cursor (fun _ => True) := by
  unfold SlotAuthorized slotPre
  apply exists_congr
  intro position
  apply exists_congr
  intro segment
  have same := completedLocation_iff tree segment.data .Write tags mode segment.range (fun _ => True)
  simp only [true_and] at same
  simp only [same]

/-- Check the read snapshots using the initial range map and root permissions.
Prepare the write snapshots from the retained read locations, then check the
same ordered roots with the write's protector set. The modes have no effect
when both sources are wildcard. -/
def readWritePre (tree : BorrowTree) (readOffset readLength writeOffset writeLength : Size)
    (readTags writeTags : ProtectedTags) : Prop :=
  let prepared := tree.locations.iterMut readOffset readLength
  prepared.outcome = .ok () ∧
    ∃ retained : Nat → TreeLocationAccessAtResult,
      (∀ cursor, cursor < prepared.positions.size →
        slotPre tree prepared .Read readTags cursor (fun after => ⟨after, none, none⟩ = retained cursor)) ∧
      let write := (TreeRangePointwiseWP.readLocations prepared retained).iterMut writeOffset writeLength
      write.outcome = .ok () ∧
        ∀ cursor, cursor < write.positions.size → slotPre tree write .Write writeTags cursor (fun _ => True)

theorem readWritePre_iff (tree : BorrowTree) (readOffset readLength writeOffset writeLength : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode) :
    TreeRangePointwiseWP.readWritePre tree .wildcard .wildcard readOffset readLength writeOffset
        writeLength readTags writeTags readMode writeMode ↔
      readWritePre tree readOffset readLength writeOffset writeLength readTags writeTags := by
  simp only [TreeRangePointwiseWP.readWritePre, TreeRangePointwiseWP.writeAuthorized, readWritePre,
    true_and, readSlot_iff, writeSlot_iff]

/-- Exact safety rule for a wildcard read followed by a wildcard write. -/
theorem wp_read_write_iff (tree : BorrowTree) (readOffset readLength writeOffset writeLength : Size)
    (readTags writeTags : ProtectedTags) (readMode writeMode : Tree.ChildrenVisitMode) :
    wp ((do
      let reads ← TreeBorrowsWP.access .wildcard readOffset readLength .Read readTags readMode
      let writes ← TreeBorrowsWP.access .wildcard writeOffset writeLength .Write writeTags writeMode
      pure (reads, writes)) : EStateM TreeRangeOutcomeWP.RangeAccessError BorrowTree
        (TreeRangeOutcomeWP.Trace × TreeRangeOutcomeWP.Trace)) (fun _ _ => True) (fun _ _ => False) tree ↔
      readWritePre tree readOffset readLength writeOffset writeLength readTags writeTags := by
  rw [TreeRangePointwiseWP.wp_read_write_pointwise_iff, readWritePre_iff]

/-- Use the same wildcard formula for the nested continuation from VC generation. -/
theorem accessPre_read_write_iff (tree : BorrowTree)
    (readOffset readLength writeOffset writeLength : Size) (readTags writeTags : ProtectedTags)
    (readMode writeMode : Tree.ChildrenVisitMode) :
    TreeBorrowsWP.accessPre tree .wildcard readOffset readLength .Read readTags readMode (fun after _ =>
      TreeBorrowsWP.accessPre after .wildcard writeOffset writeLength .Write writeTags writeMode
        (fun _ _ => True) (fun _ _ _ => False)) (fun _ _ _ => False) ↔
      readWritePre tree readOffset readLength writeOffset writeLength readTags writeTags := by
  rw [← wp_read_write_iff tree readOffset readLength writeOffset writeLength readTags writeTags
    readMode writeMode, wp_read_write_successPre_iff]
  simp only [accessPre_successPre_iff]

end Miri.Verification.TreeWildcardPairWP

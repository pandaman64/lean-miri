import Miri.TreeBorrows.LocationState
import Miri.TreeBorrows.RetagPolicy

/-! Permission rights for an exclusive reference to a region of frozen bytes.
The right is relative to a source tag: its ancestor chain must permit local
access, while foreign nodes must tolerate access under their live protectors. -/
namespace Miri.Verification.MutableReferenceRights

open Miri.TreeBorrows Miri.TreeBorrows.Tree RetagPolicy

/-- A node on the source-to-root path grants a write, including activation
of an unconflicted reservation. -/
def LocalWrite (permission : Permission) (held : Bool) : Bool :=
  match permission with
  | .Cell | .ReservedFrz false | .Unique => true
  | .ReservedIM | .ReservedFrz true => !held
  | .Frozen | .Disabled => false

/-- A foreign node has no conflicting accessed protector. -/
def ForeignWrite (state : LocationState) (held : Bool) : Bool :=
  !held || decide (state.permission = .Cell) ||
    (!state.accessed && decide (state.permission ≠ .ReservedIM))

/-- A byte's exclusive right at a single node, independent of any operation
the callee will perform. SIFA is deliberately absent from the right. -/
def Granted (state : LocationState) (related : AccessRelatedness) (held : Bool) : Prop :=
  (state.possible && match related with
    | .LocalAccess => LocalWrite state.permission held
    | .ForeignAccess => ForeignWrite state held) = true

/-- Retag may weaken SIFA for existing nodes without modifying their
permission or the accessed bit. Such bookkeeping preserves rights. -/
theorem sifa_irrelevant (state updated : LocationState)
    (permission : updated.permission = state.permission) (accessed : updated.accessed = state.accessed)
    (related : AccessRelatedness) (held : Bool) :
    Granted updated related held ↔ Granted state related held := by
  cases related <;> simp [Granted, ForeignWrite, LocationState.possible, permission, accessed]

/-- Recording SIFA does not modify exclusive rights. -/
theorem record_preserves (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) (updated : LocationState)
    (grant : Granted state related held)
    (recorded : state.recordNewAccess kind related = .Recorded updated) :
    Granted updated related held := by
  unfold LocationState.recordNewAccess at recorded
  split at recorded
  · cases recorded
    exact grant
  · contradiction

private instance (state : LocationState) (related : AccessRelatedness) (held : Bool) :
    Decidable (Granted state related held) :=
  inferInstanceAs (Decidable (_ = true))

private def keepsRight (result : LocationState.AccessResult)
    (related : AccessRelatedness) (held : Bool) : Prop :=
  match result with
  | .Success updated _ => Granted updated related held
  | _ => False

private instance (result : LocationState.AccessResult) (related : AccessRelatedness) (held : Bool) :
    Decidable (keepsRight result related held) := by
  cases result <;> unfold keepsRight <;> infer_instance

private def visit (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) : Prop :=
  match state.recordNewAccess kind related with
  | .DebugAssertion => False
  | .Recorded recorded => keepsRight (recorded.performAccess kind related held) related held

private instance (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) :
    Decidable (visit state kind related held) :=
  match result : state.recordNewAccess kind related with
  | .DebugAssertion => isFalse (by simp [visit, result])
  | .Recorded recorded =>
    decidable_of_iff _ (by simp [visit, result] :
      keepsRight (recorded.performAccess kind related held) related held ↔
        visit state kind related held)

set_option maxHeartbeats 2000000 in
/-- A visited node records the access, performs the transition, and retains
both rights whenever the caller's original right allowed the visit. -/
theorem visit_preserves (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) (grant : Granted state related held)
    (recurse : state.skipIfKnownNoop kind related = .Recurse) :
    ∃ recorded updated transition, state.recordNewAccess kind related = .Recorded recorded ∧
      recorded.performAccess kind related held = .Success updated transition ∧
      Granted updated related held := by
  have preserved : ¬ Granted state related held ∨
      state.skipIfKnownNoop kind related ≠ .Recurse ∨ visit state kind related held := by
    clear grant recurse
    rcases state with ⟨permission, accessed, sifa⟩
    cases kind <;> cases related <;> cases held <;> cases accessed <;> cases sifa <;>
      cases permission
    all_goals try (rename_i conflicted; cases conflicted)
    all_goals decide
  have visited := (preserved.resolve_left (fun missing => missing grant)).resolve_left
    (fun skipped => skipped recurse)
  unfold visit at visited
  cases recording : state.recordNewAccess kind related with
  | DebugAssertion => simp [recording] at visited
  | Recorded recorded =>
    simp only [recording] at visited
    cases access : recorded.performAccess kind related held <;> simp only [access, keepsRight] at visited
    case Success updated transition => exact ⟨recorded, updated, transition, rfl, access, visited⟩
    all_goals contradiction

/-- FnEntry grants the fresh frozen byte a local exclusive right under
either compiler policy, including when the implicit operation is only a read. -/
theorem entry_grants (config : PolicyConfig) :
    ∃ policy state, create ⟨true, true, true⟩ .Mutable .FnEntry config = some policy ∧
      policy.protector = some .StrongProtector ∧ initialLocationState policy true = .ok state ∧
      Granted state .LocalAccess true := by
  rcases config with ⟨writes, suppressed⟩
  cases writes <;> cases suppressed <;>
    exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- A frozen shared argument with an active protector blocks a foreign
exclusive right. This condition can hold before a type-directed retag read. -/
theorem no_foreign_right_for_shared_protector (sifa : IdempotentForeignAccess) :
    ¬ Granted ⟨.Frozen, true, sifa⟩ .ForeignAccess true := by
  simp [Granted, ForeignWrite]

/-- Installing the FnEntry protector leaves each distinct existing tag's
protected lookup unchanged. -/
theorem contains_insert_other (map : ProtectedTags) (fresh old : Miri.Memory.BorTag)
    (kind : ProtectorKind) (different : old ≠ fresh) :
    (map.insert fresh kind).contains old = map.contains old := by
  unfold ProtectedTags.contains ProtectedTags.get ProtectedTags.insert
  simp [Array.find?_push, Array.find?_filter, beq_iff_eq, Ne.symm different]
  congr 3
  funext entry
  by_cases same : entry.1 = old <;> simp [same, different]

/-- Old nodes retain their access relationship when a new child is inserted.
This law lifts an already preserved collection of old-node rights to the
extended domain when the caller supplies the actual old/new node mapping. -/
theorem extend {Old New : Type}
    (oldState : Old → LocationState) (oldRelated : Old → AccessRelatedness) (oldHeld : Old → Bool)
    (newState : New → LocationState) (newRelated : New → AccessRelatedness) (newHeld : New → Bool)
    (child : New) (childRight : Granted (newState child) (newRelated child) (newHeld child))
    (oldRights : ∀ node, Granted (oldState node) (oldRelated node) (oldHeld node))
    (mapped : ∀ node, node ≠ child → ∃ old,
      oldState old = newState node ∧ oldRelated old = newRelated node ∧ oldHeld old = newHeld node) :
    ∀ node, Granted (newState node) (newRelated node) (newHeld node) := by
  intro node
  by_cases fresh : node = child
  · simpa [fresh] using childRight
  · obtain ⟨old, state, related, held⟩ := mapped node fresh
    simpa only [state, related, held] using oldRights old

/-- Every represented byte location grants rights to the same source
lineage, with each node checked against its actual protector. -/
def NormalRights (tree : NormalTreeState) (scope : Nat → Prop)
    (related : Nat → AccessRelatedness) : Prop :=
  ∀ node, scope node → node < tree.locationStates.size →
    ∃ state, tree.stateAt node = some state ∧
      Granted state (related node) (tree.protectedNodes.contains node)

/-- The initial pruning decisions and lineage expected for a single ordered
visit. Such a visit cannot process a node twice. -/
def AuthorizedSchedule (tree : NormalTreeState) (scope : Nat → Prop)
    (related : Nat → AccessRelatedness)
    (kind : AccessKind) (events : List TraversalEvent) : Prop :=
  (events.map (·.node)).Nodup ∧
    ∀ event ∈ events, scope event.node ∧
      event.node < tree.locationStates.size ∧ event.relatedness = related event.node ∧
      ∀ state, tree.stateAt event.node = some state →
        state.skipIfKnownNoop kind event.relatedness = .Recurse

private theorem stateAt_set (tree : NormalTreeState) (other node : Nat) (state : LocationState)
    (inside : node < tree.locationStates.size) :
    let next : NormalTreeState := {tree with locationStates := tree.locationStates.set node (some state)}
    next.stateAt other = if other = node then some state else tree.stateAt other := by
  by_cases same : other = node
  · subst other
    simp [NormalTreeState.stateAt, inside]
  · simp [NormalTreeState.stateAt, same, Ne.symm same]

/-- The interpreter's ordered event executor completes and preserves the
exclusive right on every represented node. The schedule premise contains
only structural visitation facts and the initial pruning decisions. -/
theorem processEvents_preserves (tree : NormalTreeState) (scope : Nat → Prop)
    (related : Nat → AccessRelatedness) (kind : AccessKind) (events : List TraversalEvent) (root : Nat)
    (rights : NormalRights tree scope related)
    (schedule : AuthorizedSchedule tree scope related kind events) :
    let result := tree.processEvents root kind events
    result.status = .Completed ∧ NormalRights result.tree scope related := by
  induction events generalizing tree with
  | nil => exact ⟨rfl, rights⟩
  | cons event rest ih =>
    obtain ⟨unique, valid⟩ := schedule
    obtain ⟨fresh, tailUnique⟩ := List.nodup_cons.mp unique
    obtain ⟨active, inside, relation, skips⟩ := valid event List.mem_cons_self
    obtain ⟨old, found, granted⟩ := rights event.node active inside
    have grant : Granted old event.relatedness (tree.protectedNodes.contains event.node) :=
      relation.symm ▸ granted
    obtain ⟨recorded, state, transition, record, access, grantAfter⟩ :=
      visit_preserves old kind event.relatedness _ grant (skips old found)
    let next : NormalTreeState := {tree with locationStates := tree.locationStates.set event.node (some state)}
    have nextSize : next.locationStates.size = tree.locationStates.size := by simp [next]
    have nextAt node := stateAt_set tree node event.node state inside
    have nextRights : NormalRights next scope related := by
      intro node inScope within
      by_cases same : node = event.node
      · subst node
        refine ⟨state, ?_, ?_⟩
        · simpa [next] using nextAt event.node
        · simpa only [next, relation] using grantAfter
      · obtain ⟨oldState, atOld, oldRight⟩ := rights node inScope (nextSize ▸ within)
        refine ⟨oldState, ?_, oldRight⟩
        simpa only [next, same, ite_false, atOld] using nextAt node
    have tailValid : AuthorizedSchedule next scope related kind rest := by
      refine ⟨tailUnique, ?_⟩
      intro item member
      obtain ⟨inScope, bound, lineage, skipped⟩ := valid item (.tail event member)
      refine ⟨inScope, nextSize.symm ▸ bound, lineage, ?_⟩
      intro oldState materialized
      have distinct : item.node ≠ event.node := by
        intro same
        have mapped : item.node ∈ rest.map (·.node) := List.mem_map.mpr ⟨item, member, rfl⟩
        exact fresh (by simpa only [same] using mapped)
      have unchanged : next.stateAt item.node = tree.stateAt item.node := by
        simpa only [next, distinct, ite_false] using nextAt item.node
      exact skipped oldState (unchanged ▸ materialized)
    have done := ih next nextRights tailValid
    simpa only [NormalTreeState.processEvents, found, record, access,
      LocationState.AccessResult.resultingState, NormalTreeState.setState, inside, ↓reduceDIte, next] using done

/-- Preservation through the concrete traversal's actual pruning and event
executor. The only schedule premises are graph facts: distinct valid
indices with the expected lineage. -/
theorem normalAccess_preserves (tree : NormalTreeState) (scope : Nat → Prop)
    (related : Nat → AccessRelatedness)
    (source : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (rights : NormalRights tree scope related)
    (distinct : ((tree.topology.traverseWithSkip source mode
      (tree.shouldSkipForeignNode kind)).2.map (·.node)).Nodup)
    (lineage : ∀ event ∈ (tree.topology.traverseWithSkip source mode
      (tree.shouldSkipForeignNode kind)).2,
      scope event.node ∧ event.node < tree.locationStates.size ∧ event.node < tree.topology.nodes.size ∧
        event.relatedness = related event.node) :
    let result := tree.performAccess source kind mode
    result.status = .Completed ∧ NormalRights result.tree scope related := by
  apply processEvents_preserves _ _ _ _ _ _ rights
  refine ⟨distinct, ?_⟩
  intro event member
  obtain ⟨active, inside, inTopology, relation⟩ := lineage event member
  refine ⟨active, inside, relation, ?_⟩
  intro state found
  cases access : event.relatedness
  · rfl
  · have visited := tree.topology.traverseWithSkip_foreign_notSkipped source mode
      (tree.shouldSkipForeignNode kind) event member access
    simp only [NormalTreeState.shouldSkipForeignNode, inTopology, ↓reduceIte, found] at visited
    cases skipped : state.skipIfKnownNoop kind .ForeignAccess <;> simp_all

/-- For the actual BorrowTree location, the normal component's permission
result retains the exclusive right. Exposed-cache commit and additional
wildcard roots belong to the surrounding ranged access. -/
theorem borrowLocation_preserves (tree : BorrowTree) (location : LocationTree)
    (source : UniIndex) (tags : ProtectedTags)
    (scope : Nat → Prop) (related : Nat → AccessRelatedness) (kind : AccessKind) (mode : ChildrenVisitMode)
    (rights : NormalRights (tree.normalView location tags) scope related)
    (distinct : let view := tree.normalView location tags
      ((view.topology.traverseWithSkip source.toNat mode
        (view.shouldSkipForeignNode kind)).2.map (·.node)).Nodup)
    (lineage : let view := tree.normalView location tags
      ∀ event ∈ (view.topology.traverseWithSkip source.toNat mode
        (view.shouldSkipForeignNode kind)).2,
        scope event.node ∧ event.node < view.locationStates.size ∧ event.node < view.topology.nodes.size ∧
          event.relatedness = related event.node) :
    let result := tree.performNormalAccessAt location source kind tags mode
    result.access.status = .Completed ∧ NormalRights result.access.tree scope related := by
  exact normalAccess_preserves (tree.normalView location tags) scope related source.toNat kind mode
    rights distinct lineage

end Miri.Verification.MutableReferenceRights

import Miri.Verification.ExactWP
import Init.Internal.Order.While

namespace MiriTests.Verification.TreeBorrowsWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.Verification.TreeBorrowsWP Miri.Verification.TreeRangeAccess Std.WP

set_option experimental.vcgen true
set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def aliasTag : BorTag := ⟨2, by decide⟩
private def bytes := Size.ofBytes 1
private def entry := BorrowTree.new BorTag.one bytes
private def permissions := DedupRangeMap.new bytes (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
private def protectors := ({} : ProtectedTags).insert aliasTag .StrongProtector
private def inserted := entry.newChild Size.ZERO (.concrete BorTag.one) aliasTag permissions .Frozen true
private def writeWith (tags : ProtectedTags) :=
  access (.concrete BorTag.one) Size.ZERO bytes .Write tags .VisitChildrenOfAccessed
private def protectedWrite := inserted.tree.performBorrowAccessRange (.concrete BorTag.one)
  Size.ZERO bytes .Write protectors .VisitChildrenOfAccessed

private def protectedError : BorrowTree.BorrowTreeAccessStatus :=
  .AccessFailure ⟨0, 1⟩ (.TransitionError 1 (.ProtectedDisabled .Frozen))

private def visitedPermission (locations : Array BorrowTree.BorrowTreeLocationResult) : Option Permission :=
  (((locations[0]?.bind (·.normalAccess)).bind (·.tree.stateAt 1)).map (·.permission))

/-- The ranged access rule passes the failing trace and exact successor to an
arbitrary client postcondition. -/
theorem protectedAliasWrite (post : BorrowTree → Prop) (after : post protectedWrite.tree) :
    Triple (writeWith protectors) (· = inserted.tree) (fun _ _ => False)
      (fun (status, locations) tree =>
        status = protectedError ∧ visitedPermission locations = some .Disabled ∧ post tree) := by
  vcgen [writeWith]
  subst_vars
  rw [accessPre_iff]
  change (match protectedWrite.status with
    | .Completed => False
    | status => status = protectedError ∧
        visitedPermission protectedWrite.locations = some .Disabled ∧ post protectedWrite.tree)
  rw [show protectedWrite.status = protectedError from by cbv]
  exact ⟨rfl, by cbv, after⟩

/-- A protected shared child rejects a foreign write at the permission step. -/
example (post : Tree.LocationState.AccessResult → Prop)
    (retained : post (.Error ⟨.Disabled, true, .Read⟩ (.ProtectedDisabled .Frozen))) :
    (match (⟨.Frozen, true, .Read⟩ : Tree.LocationState).performAccess .Write .ForeignAccess true with
      | .Success .. => False
      | result => post result) :=
  (location_iff ⟨.Frozen, true, .Read⟩ .Write .ForeignAccess true (fun _ _ => False) post).mpr
    retained

/-- A visited foreign read prevents a later local write at an initially
unique location, independently of the protector, accessed bit and SIFA. -/
example (state : Tree.LocationState) (held : Bool) (unique : state.permission = .Unique) :
    ¬ locationPre state .Read .ForeignAccess held (fun afterRead _ =>
      locationPre afterRead .Write .LocalAccess held (fun _ _ => True) (fun _ => False))
      (fun _ => False) := by
  simp [locationReadWritePre, locationWriteAllowedAfterRead, unique]

/-- At an unconflicted reservation, a visited foreign read followed by a
local write succeeds exactly when the reservation is unprotected. -/
example (state : Tree.LocationState) (held : Bool)
    (reserved : state.permission = .ReservedFrz false) :
    visitedLocationPre state .Read (some .ForeignAccess) held (fun afterRead =>
      visitedLocationPre afterRead .Write (some .LocalAccess) held (fun _ => True)) ↔
    held = false := by
  simp [locationReadWritePre, locationReadAllowed, locationWriteAllowedAfterRead, reserved]

/-- `vcgen` selects the ordered protector release rule for arbitrary trees. -/
example (tag : BorTag) (tags : ProtectedTags) (post : Unit → BorrowTree → Prop)
    (failure : BorrowTree.ProtectorReleaseStatus → BorrowTree → Prop) :
    Triple (release tag tags)
      (Miri.Verification.ProtectorReleaseWP.releasePre tag tags (post ()) failure) post failure := by
  vcgen <;> assumption

/-- Retag insertion generates its precondition with both continuations. -/
example (offset : Size) (parent : ProvenanceExtra) (tag : BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (post : Unit → BorrowTree → Prop) (failure : BorrowTree.ChildInsertError → BorrowTree → Prop) :
    Triple (insertChild offset parent tag inside outside held)
      (fun tree => BorrowTree.MutationVerification.insertChildPre tree offset parent tag inside outside held
        (post ()) failure) post failure := by
  vcgen <;> assumption

/-- Duplicate retag insertion reports the mapping left by the failed insert. -/
example (offset : Size) (parent : ProvenanceExtra) (tag : BorTag)
    (inside : DedupRangeMap Tree.LocationState) (outside : Permission) (held : Bool)
    (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex)
    (failed : tree.tagMapping.insert tag = .DuplicateKeyAfterReplacement mapping index) :
    Triple (insertChild offset parent tag inside outside held) (· = tree) (fun _ _ => False)
      (fun error after => error = .DuplicateTag tag ∧ after = { tree with tagMapping := mapping }) := by
  vcgen
  subst_vars
  simp [BorrowTree.MutationVerification.insertChildPre, failed]

/-- The alias is inserted successfully. The same write completes when its
protector is absent. -/
example : inserted.outcome = .ok () := by cbv

example : (inserted.tree.performBorrowAccessRange (.concrete BorTag.one) Size.ZERO bytes .Write
    {} .VisitChildrenOfAccessed).status = .Completed := by cbv

private def exposed := entry.exposeTag {} BorTag.one
private def wildcardRead := access .wildcard Size.ZERO bytes .Read {} .VisitChildrenOfAccessed
private def wildcardReadResult :=
  exposed.tree.performBorrowAccessRange .wildcard Size.ZERO bytes .Read {} .VisitChildrenOfAccessed

/-- Exposure lets the wildcard read satisfy any postcondition of its exact
successor and trace. -/
example (post : Array BorrowTree.BorrowTreeLocationResult → BorrowTree → Prop)
    (after : post wildcardReadResult.locations wildcardReadResult.tree) :
    Triple wildcardRead (· = exposed.tree) post (fun _ _ => False) := by
  vcgen [wildcardRead]
  subst_vars
  rw [accessPre_iff]
  change (match wildcardReadResult.status with
    | .Completed => post wildcardReadResult.locations wildcardReadResult.tree
    | _ => False)
  rw [show wildcardReadResult.status = .Completed from by cbv]
  exact after

/-- An actual typed reborrow generates its staged continuation with arbitrary
compiler hooks, permissions and machine postconditions. -/
example {K U : Type} [DecidableEq K] (hooks : Miri.Interpreter.TypedRetag.Hooks K U)
    (budget : Nat) (place : Miri.Interpreter.MPlaceTy Provenance) (size : Size)
    (policy : RetagPolicy.NewPermission) (tag : BorTag)
    (post : Option Provenance → Miri.Interpreter.MachineHooks.State K U → Prop)
    (failure : Miri.Interpreter.StepError → Miri.Interpreter.MachineHooks.State K U → Prop) :
    Triple (Miri.Interpreter.TypedRetag.reborrow hooks budget place size policy tag)
      (Miri.Verification.TypedRetagWP.reborrowPre hooks budget place size policy tag post failure)
      post failure := by
  vcgen

/-- The prune callback applies to foreign subtrees. It leaves the local
visit intact and omits both a skipped root and its descendants. -/
example :
    let tree : Tree.TraversalTree :=
      ⟨#[⟨none, [1, 2]⟩, ⟨some 0, [3]⟩, ⟨some 0, []⟩, ⟨some 1, []⟩]⟩
    tree.traverseWithSkipPre 0 .VisitChildrenOfAccessed (fun node => node == 0 || node == 1)
      (fun root visits => root = 0 ∧ visits = [⟨0, .LocalAccess⟩, ⟨2, .ForeignAccess⟩]) := by
  cbv

private def twoBytes := Size.ofBytes 2
private def wildcardRoot := (BorrowTree.new BorTag.one twoBytes).newChild Size.ZERO
  .wildcard aliasTag permissions .Frozen false
private def twoRoots := ((wildcardRoot.tree.exposeTag {} BorTag.one).tree.exposeTag {} aliasTag).tree
private def twoSlots := twoRoots.locations.iterMut Size.ZERO twoBytes

private theorem wildcardReadAuthorized :
    AccessAuthorized twoRoots .wildcard Size.ZERO twoBytes .Read {} .VisitChildrenOfAccessed := by
  have slots : twoSlots.positions.size = 2 := by cbv
  refine ⟨True.intro, by cbv, ?_⟩
  intro cursor within
  change cursor < twoSlots.positions.size at within
  rw [slots] at within
  have cursorIndex : cursor = 0 ∨ cursor = 1 := by omega
  have roots : twoRoots.roots = #[⟨0⟩, ⟨1⟩] := by cbv
  rcases cursorIndex with rfl | rfl
  · refine ⟨0, _, by cbv, by cbv, by cbv, ?_⟩
    rw [wildcardTwoRootsComplete_iff _ _ _ _ _ _ _ _ roots]
    cbv
  · refine ⟨1, _, by cbv, by cbv, by cbv, ?_⟩
    rw [wildcardTwoRootsComplete_iff _ _ _ _ _ _ _ _ roots]
    cbv

/-- A wildcard access through both roots and across the split range can be
proved from the two original snapshots. -/
example :
    Triple (access .wildcard Size.ZERO twoBytes .Read {} .VisitChildrenOfAccessed)
      (· = twoRoots) (fun _ _ => True) (fun _ _ => False) := by
  vcgen
  subst_vars
  miri_tree_range_wp
  exact wildcardReadAuthorized

private def afterReadTwoRoots := (accessSuccessor twoRoots .wildcard Size.ZERO twoBytes .Read {}
  .VisitChildrenOfAccessed).1
private def writeSlots := afterReadTwoRoots.locations.iterMut bytes bytes

/-- The second prepared snapshot supplies the write range's input location. -/
example :
    afterReadTwoRoots.locations.entries[1]?.map (·.data) =
      preparedSlotLocationAt twoRoots twoSlots none .Read {} .VisitChildrenOfAccessed 1 1 := by
  rw [afterReadTwoRoots, accessSuccessor_locationAt]
  cbv

/-- The write uses one of the two read locations, and the postcondition
observes the diagnostics of each access separately. -/
example :
    wp ((do
        let reads ← access .wildcard Size.ZERO twoBytes .Read {} .VisitChildrenOfAccessed
        let writes ← access (.concrete BorTag.one) bytes bytes .Write {} .VisitChildrenOfAccessed
        pure (reads, writes)) :
        EStateM (BorrowTree.BorrowTreeAccessStatus × Array BorrowTree.BorrowTreeLocationResult)
          BorrowTree (Array BorrowTree.BorrowTreeLocationResult × Array BorrowTree.BorrowTreeLocationResult))
      (fun (reads, writes) _ => reads.size = 2 ∧ (writes[0]?.map (·.range)) = some ⟨1, 2⟩)
      (fun _ _ => False) twoRoots := by
  miri_tree_range_wp
  refine ⟨wildcardReadAuthorized, ?_⟩
  constructor
  · change AccessAuthorized afterReadTwoRoots (.concrete BorTag.one) bytes bytes .Write {}
      .VisitChildrenOfAccessed
    have single : writeSlots.positions.size = 1 := by cbv
    refine ⟨by cbv, by cbv, ?_⟩
    intro cursor within
    change cursor < writeSlots.positions.size at within
    rw [single] at within
    have cursorZero : cursor = 0 := by omega
    subst cursor
    refine ⟨1, _, by cbv, by cbv, by cbv, ?_⟩
    rw [← BorrowTree.RangeVerification.locationContract_iff]
    cbv
  · cbv

/-- An unresolved tag fails the success-only WP even for a zero-byte access. -/
example :
    ¬ wp (access (.concrete aliasTag) Size.ZERO Size.ZERO .Read {} .VisitChildrenOfAccessed)
      (fun _ _ => True) (fun _ _ => False) entry := by
  rw [wp_access_succeeds_iff]
  intro authorized
  have resolved : (entry.indexOfTag aliasTag).isSome = true := authorized.1
  cbv at resolved

/-- A resolved tag cannot authorize bytes outside the prepared map. -/
example :
    ¬ wp (access (.concrete BorTag.one) Size.ZERO twoBytes .Read {} .VisitChildrenOfAccessed)
      (fun _ _ => True) (fun _ _ => False) entry := by
  rw [wp_access_succeeds_iff]
  intro authorized
  have prepared : (entry.locations.iterMut Size.ZERO twoBytes).outcome = .ok () := authorized.2.1
  cbv at prepared
  cases prepared

end MiriTests.Verification.TreeBorrowsWP

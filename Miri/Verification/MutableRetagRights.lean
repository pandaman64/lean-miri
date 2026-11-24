import Miri.Verification.TypedRetagWP
import Miri.Verification.TreeRangeAccess

namespace Miri.Verification.MutableRetagRights

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory
open Miri.TreeBorrows Miri.TreeBorrows.RetagPolicy Miri.Verification Std.WP
open Miri.Interpreter.TypedRetag

variable {K U : Type}

/-- Independent permissions at the iterator slots discharge the real
retag parent access, with the changed permission tree installed in memory. -/
theorem parentAccess_of_slots [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (offset length : Size) (kind : AccessKind) (before : MachineHooks.State K U)
    (entry : LocalAllocation Provenance BorrowTree K) (borrow : MachineHooks.BorrowState)
    (live : before.machine.memory.live[location.allocId]? = some entry)
    (tracked : before.machine.borrowTracker = some borrow)
    (prepared : IterMutResult LocationTree) (source : Option UniIndex)
    (selected : match location.parentProvenance with
      | .concrete tag => ∃ index, source = some index ∧ entry.allocation.extra.indexOfTag tag = some index
      | .wildcard => source = none)
    (prepare : entry.allocation.extra.locations.iterMut offset length = prepared)
    (okay : prepared.outcome = .ok ())
    (owned : TreeRangeAccess.SlotsAuthorized entry.allocation.extra prepared source
      kind borrow.global.protectedTags .VisitChildrenOfAccessed) :
    let result := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
      offset length kind borrow.global.protectedTags .VisitChildrenOfAccessed
    let memory := {before.machine.memory with live :=
      (before.machine.memory.live.insert location.allocId
        {entry with allocation := entry.allocation.setExtra result.tree})}
    TypedRetagWP.parentAccessPre location offset length kind
      (fun after => after = {before with machine := {before.machine with memory}})
      (fun _ _ => False) before := by
  have completed := TreeRangeAccess.rangeComplete entry.allocation.extra location.parentProvenance
    offset length kind borrow.global.protectedTags .VisitChildrenOfAccessed prepared source selected prepare okay owned
  simp only [TypedRetagWP.parentAccessPre, TypedRetagWP.effectPre, getTree_apply, tracker_apply,
    live, tracked, TreeBorrowsWP.accessPre_iff, completed, updateTree_apply,
    MemoryState.setLiveAllocation_of_find _ _ _ _ live]

/-- Commit a checked child constructor in the actual allocation entry of the
typed reborrow, preserving the other machine and frame state. -/
theorem insertChild_of_complete [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) (inside : DedupRangeMap Tree.LocationState)
    (before : MachineHooks.State K U) (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.machine.memory.live[location.allocId]? = some entry)
    (complete : (entry.allocation.extra.newChild location.baseOffset location.parentProvenance
      tag inside policy.outsidePermission policy.protector.isSome).outcome = .ok ()) :
    let result := entry.allocation.extra.newChild location.baseOffset location.parentProvenance
      tag inside policy.outsidePermission policy.protector.isSome
    let memory := {before.machine.memory with live :=
      (before.machine.memory.live.insert location.allocId
        {entry with allocation := entry.allocation.setExtra result.tree})}
    TypedRetagWP.insertChildPre location policy tag inside
      (fun after => after = {before with machine := {before.machine with memory}})
      (fun _ _ => False) before := by
  simp only [TypedRetagWP.insertChildPre, TypedRetagWP.effectPre, getTree_apply, live,
    BorrowTree.MutationVerification.insertChildPre_iff, BorrowTree.MutationVerification.childResultPre,
    complete, updateTree_apply, MemoryState.setLiveAllocation_of_find _ _ _ _ live]

/-- In the imprecise profile, a Freeze type produces a uniform permission
partition over the actual object size. -/
theorem frozen_insidePermissions (hooks : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission)
    (state : Tree.LocationState)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (initialized : initialLocationState policy true = .ok state) :
    insidePermissions hooks budget place size policy = pure (DedupRangeMap.new size state) := by
  funext before
  simp [insidePermissions, imprecise, freeze, checked, initialized, bind, Bind.bind, pure,
    Pure.pure, EStateM.bind, EStateM.pure]

/-- Zero bytes with a resolved absence of an allocation take the actual
short branch and return the incoming provenance. Pointer validation and
the creation log are the only hook effects on that branch. -/
theorem zero_unallocated [DecidableEq K] (hooks : Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : NewPermission) (tag : BorTag) (before checked resolved logged : MachineHooks.State K U)
    (check : hooks.checkPtrAccess place.mplace.ptr Size.ZERO before = .ok () checked)
    (resolve : hooks.resolveAllocation place.mplace.ptr checked = .ok none resolved)
    (log : hooks.logCreation place Size.ZERO policy tag none resolved = .ok () logged) :
    wp (reborrow hooks budget place Size.ZERO policy tag)
      (fun provenance after => provenance = place.mplace.ptr.provenance ∧ after = logged)
      (fun _ _ => False) before := by
  rw [← TypedRetagWP.reborrowPre_iff]
  have zero : Size.ZERO.bytes = 0 := rfl
  simp [TypedRetagWP.reborrowPre, TypedRetagWP.effectPre, check, resolve, log, zero]

end Miri.Verification.MutableRetagRights

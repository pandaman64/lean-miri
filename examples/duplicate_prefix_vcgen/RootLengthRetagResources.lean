import RootLengthRegion
import duplicate_prefix.RetagSuccessorCapacity

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint RetagFrozenChild

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem RootLengthState.reservationStage
    {config : RootConfig} {older : Array CompilerFrameContext.ActualFrame}
    {outside initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : ActiveCaller older outside initialFrame initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthState config older outside initialFrame frame initial final root allocation offset len count tracker)
    (initialKeys : RetagInsertionCapacity.Ready allocation.allocation.extra)
    (room : allocation.allocation.extra.nodes.size+2 < 2^32)
    (bounds : offset.toNat + len.toNat ≤ allocation.allocation.extra.locations.size.bytes.toNat) :
    let tree := post.branch.ready.entry.allocation.extra
    let global := post.branch.ready.tracker.global
    FrozenReborrowInputs.Stage tree global.protectedTags post.branch.ready.tag global.nextPointerTag
      post.branch.ready.source post.branch.ready.root (Size.ofBytes offset) (Size.ofBytes len)
      (DedupRangeMap.new (Size.ofBytes len) ExclusiveTwoPhaseRetag.initial) false := by
  dsimp only
  let cap := post.insertionCapacity initialKeys room
  have extent : offset.toNat + len.toNat ≤ post.branch.ready.entry.allocation.extra.locations.size.bytes.toNat := by
    simpa only [post.branch.rangeCapacity] using bounds
  refine ⟨post.branch.coherence,post.branch.ready.indexed,⟨post.branch.ready.node,post.branch.ready.found⟩,
    cap.roots,cap.freshKey,cap.room,cap.aligned,cap.reuse,extent,?_,?_,
    post.branch.writable,post.branch.materialized,post.branch.vacant⟩
  · intro segment member
    by_cases empty : len = 0
    · simp [DedupRangeMap.new,DedupRangeMap.iterAll,Size.ofBytes,empty] at member
    · simp [DedupRangeMap.new,DedupRangeMap.iterAll,Size.ofBytes,beq_iff_eq,empty] at member
      subst segment
      exact ⟨by simp,extent⟩
  · intro segment member
    by_cases empty : len = 0
    · simp [DedupRangeMap.new,DedupRangeMap.iterAll,Size.ofBytes,empty] at member
    · simp [DedupRangeMap.new,DedupRangeMap.iterAll,Size.ofBytes,beq_iff_eq,empty] at member
      subst segment
      exact .inl rfl

theorem RootLengthState.futureCapacity
    {config : RootConfig} {older : Array CompilerFrameContext.ActualFrame}
    {outside initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : ActiveCaller older outside initialFrame initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthState config older outside initialFrame frame initial final root allocation offset len count tracker)
    (initialKeys : RetagInsertionCapacity.Ready allocation.allocation.extra)
    (room : allocation.allocation.extra.nodes.size+3 < 2^32)
    (budget : tracker.global.nextPointerTag.value.toNat+4 < 2^64)
    (bounds : offset.toNat + len.toNat ≤ allocation.allocation.extra.locations.size.bytes.toNat) :
    let tree := post.branch.ready.entry.allocation.extra
    let global := post.branch.ready.tracker.global
    let newTag := global.nextPointerTag
    ∀ (advanced : TreeBorrows.GlobalState) (child : UniIndex),
      global.newPointerTag = .ok (advanced,newTag) →
      (ExclusiveTwoPhaseRetag.reservationTree tree post.branch.ready.tag newTag (Size.ofBytes offset)
        (Size.ofBytes len) global.protectedTags).indexOfTag newTag = some child →
      advanced.nextPointerTag.value ≠ 18446744073709551615 ∧
      CurrentTwoPhaseStructural.InsertionCapacity
        (ExclusiveTwoPhaseRetag.reservationTree tree post.branch.ready.tag newTag (Size.ofBytes offset)
          (Size.ofBytes len) global.protectedTags) child post.branch.ready.root advanced.nextPointerTag := by
  exact RetagSuccessorCapacity.afterReservation _ _ _ _ _ _ _
    (post.reservationStage initialKeys (by omega) bounds) (post.keys)
    (by have growth := post.nodes; omega) post.tagAge (by rw [post.nextTag]; omega)

#print axioms RootLengthState.futureCapacity
end DuplicatePrefix.RootZeroShallowReturn

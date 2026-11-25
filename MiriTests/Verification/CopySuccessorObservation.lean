import Miri.Verification.MemoryObservationWP
import Miri.Verification.TreeObservationWP
import Init.Internal.Order.While

/-! Check the copy and its following scalar load from initial bytes and permissions. -/
namespace MiriTests.Verification.CopySuccessorObservation

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification Std.WP
open TreeObservationWP

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

private def sourceRange := allocRange Size.ZERO (Size.ofBytes 1)
private def destinationRange := allocRange (Size.ofBytes 1) (Size.ofBytes 1)
private def target : TargetDataLayout := ⟨.little, .w64⟩
private def image : Option (Allocation Provenance Unit) :=
  (Allocation.fromBytes #[73, 13] Align.ONE .Mut).toOption

private theorem imageExists : image.isSome = true := by cbv
private def initialImage := image.get imageExists

private def child : BorTag := ⟨2, by decide⟩
private def tree : BorrowTree :=
  let root := BorrowTree.new BorTag.one (Size.ofBytes 2)
  (root.newChild (Size.ofBytes 1) (.concrete BorTag.one) child
    (DedupRangeMap.new (Size.ofBytes 1) ⟨.Unique, true, .None⟩) (.ReservedFrz false) false).tree

private def access (tag : BorTag) (range : AllocRange) : Access :=
  ⟨.concrete tag, range.start, range.size, {}, .VisitChildrenOfAccessed⟩

local macro "check_fixture_fact" : tactic =>
  `(tactic| first | rfl | decide +kernel | cbv)

/-- The byte mutation uses the source image kept by the read, retains the
destination tree left by the write, and yields 73 at the observing offset. -/
theorem copied_byte (afterRead afterWrite : BorrowTree) :
    let source := initialImage.mapExtra (fun _ => afterRead)
    let dest := initialImage.mapExtra (fun _ => afterWrite)
    MemoryObservationWP.afterMutationPre
      (source.copyRepeatedly sourceRange destinationRange.start 1 (Size.ofBytes 8) true true dest)
      target destinationRange false
      (fun scalar stored => scalar.toUInt8 = .ok 73 ∧ stored.extra = afterWrite)
      (fun _ _ => False) (fun _ _ => False) := by
  let source := initialImage.mapExtra (fun _ => afterRead)
  let dest := initialImage.mapExtra (fun _ => afterWrite)
  change MemoryObservationWP.afterMutationPre
    (source.copyRepeatedly sourceRange destinationRange.start 1 (Size.ofBytes 8) true true dest)
    target destinationRange false _ _ _
  have sourceBytes : source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) =
      .ok #[73, 13] := by check_fixture_fact
  have destBytes : dest.getBytesUnchecked (allocRange Size.ZERO dest.byteSize) =
      .ok #[73, 13] := by check_fixture_fact
  obtain ⟨copied, mutation, _, _, _, _, extra, _, _, _, init, _, _, provenance, bytes, _⟩ :=
    Allocation.copy_initialized_spec source dest sourceRange
      (Size.ofBytes 1) destinationRange.start (Size.ofBytes 8) true true #[73]
      ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      (by check_fixture_fact) (by check_fixture_fact) (by check_fixture_fact) (by check_fixture_fact)
      (by check_fixture_fact) (by check_fixture_fact) (by check_fixture_fact) (by check_fixture_fact)
      (by intro data observed; rw [sourceBytes] at observed; cases observed; check_fixture_fact)
      (by intro _ _; exact .inl (by check_fixture_fact))
      (by check_fixture_fact) (by check_fixture_fact) (by check_fixture_fact)
      (by check_fixture_fact) (by check_fixture_fact)
      (by intro data observed; rw [destBytes] at observed; cases observed; check_fixture_fact)
      (by check_fixture_fact)
  unfold Allocation.copy at mutation
  rw [mutation]
  simp only [MemoryObservationWP.afterMutationPre]
  rw [show allocRange destinationRange.start sourceRange.size = destinationRange from rfl] at init bytes
  rw [init, bytes, provenance]
  have sameTree : copied.extra = afterWrite := extra
  simp only [sameTree, and_true]
  check_fixture_fact

/-- At the successful write continuation, the byte mutation keeps that
write's permission tree and copies the initialized source byte. The next
permission check uses precisely that tree. The same ordered obligations
apply to the parent and stale-child observations. -/
theorem copy_and_observe_pre (tag : BorTag)
    (post : Traces → BorrowTree → Prop)
    (onError : TreeRangeOutcomeWP.RangeAccessError → BorrowTree → Prop) :
    wp (readWriteObserve (access BorTag.one sourceRange) (access BorTag.one destinationRange)
      (access tag destinationRange) .Read) post onError tree ↔
    TreeBorrowsWP.accessPre tree (.concrete BorTag.one) sourceRange.start sourceRange.size
      .Read {} .VisitChildrenOfAccessed (fun afterRead readTrace =>
        TreeBorrowsWP.accessPre afterRead (.concrete BorTag.one) destinationRange.start
          destinationRange.size .Write {} .VisitChildrenOfAccessed (fun afterWrite writeTrace =>
            (let source := initialImage.mapExtra (fun _ => afterRead)
             let dest := initialImage.mapExtra (fun _ => afterWrite)
             MemoryObservationWP.afterMutationPre
               (source.copyRepeatedly sourceRange destinationRange.start 1 (Size.ofBytes 8) true true dest)
               target destinationRange false
               (fun scalar stored => scalar.toUInt8 = .ok 73 ∧ stored.extra = afterWrite)
               (fun _ _ => False) (fun _ _ => False)) ∧
            TreeBorrowsWP.accessPre afterWrite (.concrete tag) destinationRange.start destinationRange.size
              .Read {} .VisitChildrenOfAccessed
              (fun observed trace => post ((readTrace, writeTrace), trace) observed)
              (fun status retained trace => onError (status, trace) retained))
          (fun status retained trace => onError (status, trace) retained))
      (fun status retained trace => onError (status, trace) retained) := by
  rw [wp_readWriteObserve_iff]
  simp only [readWriteObservePre, TreeRangeOutcomeWP.readWritePre, access]
  simp only [copied_byte, true_and]

/-- The adjacent write keeps the original tag readable at the destination. -/
theorem original_tag_reads_copy :
    wp (readWriteObserve (access BorTag.one sourceRange) (access BorTag.one destinationRange)
      (access BorTag.one destinationRange) .Read) (fun _ _ => True) (fun _ _ => False) tree := by
  rw [copy_and_observe_pre]
  simp only [copied_byte, true_and]
  cbv

/-- The child would be readable without the intervening copy write. -/
theorem child_tag_reads_before_copy :
    wp (TreeBorrowsWP.access (.concrete child) destinationRange.start destinationRange.size
      .Read {} .VisitChildrenOfAccessed) (fun _ _ => True) (fun _ _ => False) tree := by
  rw [TreeRangeOutcomeWP.wp_access_outcomePre_iff]
  cbv

/-- The same write disables the child tag at the destination. The error
continuation is reached by the observation, after both copy accesses. -/
theorem child_tag_rejects_copy_observation :
    wp (readWriteObserve (access BorTag.one sourceRange) (access BorTag.one destinationRange)
      (access child destinationRange) .Read) (fun _ _ => False)
      (fun error _ => match error.1 with
        | .AccessFailure ⟨1, 2⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)) => True
        | _ => False) tree := by
  rw [copy_and_observe_pre]
  simp only [copied_byte, true_and]
  cbv

#print axioms original_tag_reads_copy
#print axioms child_tag_reads_before_copy
#print axioms child_tag_rejects_copy_observation
#print axioms copied_byte
#print axioms copy_and_observe_pre

end MiriTests.Verification.CopySuccessorObservation

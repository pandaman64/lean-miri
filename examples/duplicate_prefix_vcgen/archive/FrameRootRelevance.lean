import duplicate_prefix.ActiveStackRelease
import duplicate_prefix.PushThread
import Lean

namespace DuplicatePrefix.FrameRootRelevance
open Miri.Interpreter

theorem topmostLocal
    (older : Array (Frame P LocalLayout MachineHooks.FrameExtra))
    (root helper : Frame P LocalLayout MachineHooks.FrameExtra)
    (localRank : root.extra.userRelevance = 255) :
    FrameRelevance.computeTop ⟨(older.push root).push helper⟩ 1 = some older.size := by
  unfold FrameRelevance.computeTop
  simp only [Array.size_push, List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.drop_succ_cons, List.drop_zero, List.forIn_cons]
  have rootAt : ((older.push root).push helper)[older.size]? = some root := by
    simp [Array.getElem?_push, Array.size_push]
  rw [rootAt]
  simp [localRank, bind, Bind.bind, pure, Pure.pure, Id.run]

theorem restoredAfterHelper
    (older : Array (Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra))
    (root helper : Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (localRank : root.extra.userRelevance = 255)
    (oldCache : thread.topUserRelevantFrame = some older.size ∨
      thread.topUserRelevantFrame = some (older.push root).size) :
    let index := thread.topUserRelevantFrame.getD (older.push root).size
    let after := ActiveRelease.afterRelevance (older.push root) helper machine index
    ∃ thread, after.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some older.size := by
  intro index after
  rcases oldCache with rootCache | helperCache
  · have miss : index ≠ (older.push root).size := by
      simp [index,rootCache]
    have unchanged : after = machine := by
      unfold after ActiveRelease.afterRelevance
      rw [ite_eq_right miss]
    exact ⟨thread,unchanged.symm ▸ active,rootCache⟩
  · have hit : index = (older.push root).size := by simp [index,helperCache]
    have tree := topmostLocal older root helper localRank
    have changed : after = CallEntryFacts.cacheTop machine older.size := by
      simp [after,ActiveRelease.afterRelevance,hit,tree,CallEntryFacts.cacheTop]
    refine ⟨{thread with topUserRelevantFrame := some older.size},?_,rfl⟩
    rw [changed]
    exact PushThread.cache_top_active machine thread older.size active

end DuplicatePrefix.FrameRootRelevance

#print axioms DuplicatePrefix.FrameRootRelevance.topmostLocal

#print axioms DuplicatePrefix.FrameRootRelevance.restoredAfterHelper

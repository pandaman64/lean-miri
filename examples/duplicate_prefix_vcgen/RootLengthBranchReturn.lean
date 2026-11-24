import RootLengthPrefix

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows

/-- The actual rejecting arm closes the root scope starting at the shared
length checkpoint. -/
theorem RootLengthState.rejectionTrace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel+1)
    {older : Array CompilerFrameContext.ActualFrame} {outside original frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : ActiveCaller older outside original initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthState (PreparedContracts.actualConfig options () (remaining+1) span)
      older outside original frame initial final root allocation offset len count tracker)
    (reject : count > len / 2) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent (older.push outside) frame final
    ∃ done, SuccessfulTrace.Trace cfg limits before done ∧ done.stack.frames.size < before.stack.frames.size := by
  obtain ⟨returned, trace⟩ := executesRejectionReturn options limits remaining span source debug fuel fuelEq
    older outside frame final len count reject post.branch.guard post.branch.ready post.branch.defaultMode
    post.branch.gc post.branch.unchecked
  exact ⟨_, trace, by simp [Storage.withCurrent]⟩

#print axioms RootLengthState.rejectionTrace
end DuplicatePrefix.RootZeroShallowReturn

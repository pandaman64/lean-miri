import RootSliceRegion
import PhysicalReturnFromSlice
import duplicate_prefix.RootPhysicalCarrierTransport

namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts SourceDomain PreparedArguments CanonicalCallDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- The actual rejection arm writes false and releases both frame-owned
protectors with the same output provenance as the original call. -/
theorem RootLengthOfSlice.rejectedPhysicalTrace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (debugOff : options.place.debugAssertions = false) (source : PreparedContracts.SourceComparator)
    {initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : RetainedSlice initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthOfSlice (PreparedContracts.actualConfig options () (remaining+1) span)
      #[] initialFrame frame initial final root allocation offset len count tracker)
    (rejected : count > len/2) (positive : 0 < len)
    (pointer : Pointer (Option Provenance))
    (concrete : pointer.provenance = some (.concrete root.id root.tag))
    (selected : MachineHooks.BorrowState) (tracked : initial.borrowTracker = some selected)
    (sameTracker : selected = tracker)
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] initialFrame initial) initialFrame pointer len)
    (headroom : Nat)
    (profile : AllocationProfile (Storage.withCurrent #[] initialFrame initial) initialFrame headroom)
    (raceOff : initial.dataRace = none) (backendOff : initial.user.payload.payload.user.backend = .none)
    (continues : initialFrame.returnContinuation = .stop true) (noVarargs : initialFrame.vaList = #[]) :
    ∃ done, SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent #[] frame final) done ∧ done.stack.frames = #[] ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () done = (done,.ok false) := by
  let first := RootZeroCompleteState.tick options remaining span final
  let second := RootZeroCompleteState.tick options remaining span first
  let third := RootZeroCompleteState.tick options remaining span second
  obtain ⟨result, trace, body, location, slot, extra, place, continuation, varargs, immediate, ghost, shallow,
    unchecked, gc, stable, memory, borrowing, threads⟩ :=
    rejectsBeforePhysicalReturn options limits remaining span source debugOff fuel budget frame final len count rejected
      post.branch.guard post.branch.ready post.branch.defaultMode post.branch.gc post.branch.unchecked
  let ready : RetainedSlice third := {
    post.branch.ready with
    present := by rw [memory]; exact post.branch.ready.present
    tracked := borrowing.trans post.branch.ready.tracked
    active := by rw [threads]; exact post.branch.ready.active }
  subst selected
  have sameMask : ready.tracker.global.protectedTags = tracker.global.protectedTags := post.protectors
  have slotSame : pointer.provenance = some (.concrete ready.id ready.tag) := by
    change pointer.provenance = some (.concrete post.branch.ready.id post.branch.ready.tag)
    rw [post.branch.id,post.branch.tag]
    exact concrete
  have distinct : ∀ key, key ≠ ready.id → third.memory.live[key]? = initial.memory.live[key]? := by
    intro key different
    rw [memory]
    exact post.branch.unrelated key (by simpa only [ready,post.branch.id] using different)
  have preservation := post.branch.stable.trans stable
  have stored := RootPhysicalCarrierTransport.transport
    (Storage.withCurrent #[] initialFrame initial) (Storage.withCurrent #[] result third)
    initialFrame result pointer len ready.id ready.tag
    (by intro zero; rw [zero] at positive; exact (UInt64.lt_irrefl _ positive))
    slotSame tracker ready.tracker tracked ready.tracked sameMask (place.trans post.place)
    (congrArg (·.borrowTracker) (extra.trans post.frameExtra)) preservation.addresses distinct destination
  have outputBacking := RootPhysicalCarrierTransport.backing
    (Storage.withCurrent #[] initialFrame initial) (Storage.withCurrent #[] result third)
    initialFrame headroom profile ready.id distinct preservation.extras
  obtain ⟨done, returned, empty, stop⟩ :=
    returnPhysicalWithRetainedSlice options limits remaining span fuel budget debugOff result third pointer len
      positive ready slotSame stored outputBacking post.branch.coherence offset (offset+len) post.footprint
      body location false slot (by rw [extra]; exact post.branch.guard.noClocks)
      (continuation.trans (post.continuation.trans continues)) immediate (varargs.trans (post.varargs.trans noVarargs))
      ghost shallow unchecked gc (by rw [threads]; exact post.branch.guard.fixed)
      (preservation.race.trans raceOff) (preservation.backend.trans backendOff)
  exact ⟨done,SuccessfulTrace.append trace returned,empty,stop⟩

#print axioms RootLengthOfSlice.rejectedPhysicalTrace
end DuplicatePrefix.RootZeroShallowReturn

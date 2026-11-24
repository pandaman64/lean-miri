import RootLengthOfActiveSlice
import PhysicalReturnWithSharedSlice
import PhysicalDestinationAfterLength
namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts SourceDomain PreparedArguments CanonicalCallDomain ScopedPhysicalRelease

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- The actual rejection arm writes false and releases both frame-owned
protectors with the same output provenance as the original call. -/
theorem RootLengthOfActiveSlice.rejectedPhysicalTrace
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (debugOff : options.place.debugAssertions = false) (source : PreparedContracts.SourceComparator)
    {initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : RetainedSlice initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState} (base : UInt64)
    (post : RootLengthOfActiveSlice (PreparedContracts.actualConfig options () (remaining+1) span)
      #[] initialFrame frame initial final root allocation offset len count tracker)
    (rejected : count > len/2) (positive : 0 < len)
    (pointer : Pointer (Option Provenance))
    (concrete : pointer.provenance = some (.concrete root.id root.tag))
    (original : root.entry = allocation) (tracked : initial.borrowTracker = some tracker)
    (sourceBase : initial.user.addresses.baseAddr.find? (·.allocId == root.id) = some ⟨root.id,base⟩)
    (sourceAddress : pointer.offset.bytes.toNat = base.toNat + offset.toNat)
    (sourceUpper : (offset+len).toNat = offset.toNat + len.toNat)
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] initialFrame initial) initialFrame pointer len true)
    (headroom : Nat)
    (profile : AllocationProfile (Storage.withCurrent #[] initialFrame initial) initialFrame headroom)
    (raceOff : initial.dataRace = none) (backendOff : initial.user.payload.payload.user.backend = .none)
    (continues : initialFrame.returnContinuation = .stop true) (noVarargs : initialFrame.vaList = #[]) :
    ∃ done, SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent #[] frame final) done ∧ done.stack.frames = #[] ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () done = (done,.ok false) := by
  let first : LenExitFacts.MachineState := RootZeroCompleteState.tick options remaining span final
  let second : LenExitFacts.MachineState := RootZeroCompleteState.tick options remaining span first
  let third : LenExitFacts.MachineState := RootZeroCompleteState.tick options remaining span second
  obtain ⟨result, trace, body, location, slot, extra, place, continuation, varargs, immediate, ghost, shallow,
    unchecked, gc, stable, memory, borrowing, threads⟩ :=
    rejectsBeforePhysicalReturn options limits remaining span source debugOff fuel budget frame final len count rejected
      post.branch.guard post.branch.ready post.branch.defaultMode post.branch.gc post.branch.unchecked
  let ready : RetainedSlice third := {
    post.branch.ready with
    present := by rw [memory]; exact post.branch.ready.present
    tracked := borrowing.trans post.branch.ready.tracked
    active := by rw [threads]; exact post.branch.ready.active }
  have nonempty : len ≠ 0 := by
    intro equal
    rw [equal] at positive
    exact UInt64.lt_irrefl _ positive
  have originalLive : initial.memory.live[root.id]? = some allocation := by rw [← original]; exact root.present
  have readyLive : third.memory.live[root.id]? = some {allocation with
      allocation := allocation.allocation.setExtra ready.entry.allocation.extra} := by
    rw [← post.branch.id, ← post.branch.allocationData]
    exact ready.present
  have key : allocation.allocation.extra.indexOfTag root.tag = some root.source := by
    rw [← original]
    exact root.indexed
  have oldNode : ∃ node, allocation.allocation.extra.nodeAt root.source = some node := by
    rw [← original]
    exact ⟨root.node,root.found⟩
  have preservation := post.branch.stable.trans stable
  have unrelated : ∀ id, id ≠ root.id → third.memory.live[id]? = initial.memory.live[id]? := by
    intro id different
    rw [memory]
    exact post.branch.unrelated id different
  have stored := PhysicalDestinationAfterLength.transport
    (before := Storage.withCurrent #[] initialFrame initial) (after := Storage.withCurrent #[] result third) concrete nonempty originalLive readyLive
    unrelated (place.trans post.place) (congrArg (·.borrowTracker) (extra.trans post.frameExtra))
    preservation.addresses sourceBase sourceAddress sourceUpper key oldNode tracked ready.tracked
    post.protectors post.branch.rangeCapacity ready.roots post.branch.coherence post.branch.vacant post.watched destination
  have backing (key : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (live : third.memory.live[key]? = some entry) :
      third.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) =
        some (key,{weakMemory := none, backtrace := (AllocationBacktrace.get
          third.user.payload.payload.user.runtime.extras.allocations key)}) := by
    have present : initial.memory.live.contains key = true := by
      by_cases same : key = root.id
      · subst key
        simp [Std.ExtTreeMap.contains_eq_isSome_getElem?,originalLive]
      · have old := (unrelated key same).symm.trans live
        simp [Std.ExtTreeMap.contains_eq_isSome_getElem?,old]
    obtain ⟨effects,lookup,noWeak,noSync⟩ := profile.extras key present
    change initial.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) = some (key,effects) at lookup
    rw [preservation.extras,AllocationBacktrace.of_lookup lookup,lookup]
    congr 2
    cases effects
    simp_all
  have concrete' : pointer.provenance = some (.concrete ready.id ready.tag) := by
    change pointer.provenance = some (.concrete post.branch.ready.id post.branch.ready.tag)
    simpa only [post.branch.id,post.branch.tag] using concrete
  have sourceBase' : third.user.addresses.baseAddr.find? (·.allocId == ready.id) = some ⟨ready.id,base⟩ := by
    change third.user.addresses.baseAddr.find? (·.allocId == post.branch.ready.id) = _
    rw [preservation.addresses,post.branch.id]
    exact sourceBase
  let accessed : AccessedOnlyWithin ready.entry.allocation.extra ready.source offset.toNat (offset+len).toNat :=
    post.branch.activeScope
  obtain ⟨done, returned, empty, stop, _⟩ :=
    returnPhysicalWithSharedSlice options limits remaining span fuel budget debugOff result third pointer len
      positive ready concrete' false stored backing post.branch.coherence offset (offset+len) base sourceAddress
      sourceUpper sourceBase' accessed.visitsWithin post.branch.vacant post.branch.writable
      body location false slot (by rw [extra]; exact post.branch.guard.noClocks)
      (continuation.trans (post.continuation.trans continues)) immediate (varargs.trans (post.varargs.trans noVarargs))
      ghost shallow unchecked gc (by rw [threads]; exact post.branch.guard.fixed)
      (preservation.race.trans raceOff) (preservation.backend.trans backendOff)
  exact ⟨done,SuccessfulTrace.append trace returned,empty,stop⟩

#print axioms RootLengthOfActiveSlice.rejectedPhysicalTrace
end DuplicatePrefix.RootZeroShallowReturn

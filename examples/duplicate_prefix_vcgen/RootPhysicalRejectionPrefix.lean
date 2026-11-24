import duplicate_prefix.LenExitFacts
import RetainedSlicePhysicalPlan
import RootRejectedAfterLen

namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The exact execution of the rejecting arm before the physical return.
At this point only local state and the accounted terminator state changed. -/
theorem rejectsBeforePhysicalReturn
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : LenExitFacts.MachineState)
    (length count : UInt64) (rejected : count > length / 2)
    (entry : RejectionEntry frame machine length count) (ready : RetainedSlice machine)
    (defaultMode : ready.tracker.retagMode = .Default)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent #[] frame machine
    let first := RootZeroCompleteState.tick options remaining span machine
    let second := RootZeroCompleteState.tick options remaining span first
    let third := RootZeroCompleteState.tick options remaining span second
    ∃ result,
      SuccessfulTrace.Trace cfg limits before (Storage.withCurrent #[] result third) ∧
      result.body = RootBody.reflected.body.body ∧ result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧
      result.returnContinuation = frame.returnContinuation ∧ result.vaList = frame.vaList ∧
      ZeroImmediateFacts.AllImmediate result ∧
      third.user.payload.ghost = false ∧ third.user.payload.validation = .Shallow ∧
      (cfg.terminators.getControl third.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl third.user).gcInterval = 0 ∧
      LenExitFacts.Stable machine third ∧
      third.memory = machine.memory ∧ third.borrowTracker = machine.borrowTracker ∧ third.threads = machine.threads := by
  intro cfg before first second third
  obtain ⟨result, trace, body, _, _, extra, destination, continuation, varargs, _, _,
    location, slot, immediate⟩ := RootRejectedPrefix.executes options limits remaining span source debugOff fuel fuelEq
      #[] frame machine length count rejected entry.size entry.temp entry.live12 entry.live13 entry.cache13
      entry.live0 entry.cache0 entry.live7 entry.live8 entry.cache8 entry.live9 entry.cache9 entry.live10 entry.cache10
      entry.live11 entry.cache11 entry.body entry.identity entry.callee entry.location entry.immediate entry.noClocks
      ready.tracker ready.tracked defaultMode entry.ghost entry.shallow unchecked gc entry.fixed
  have ghost : third.user.payload.ghost = false :=
    (RootZeroCompleteState.tick_ghost options remaining span second).trans
      ((RootZeroCompleteState.tick_ghost options remaining span first).trans
        ((RootZeroCompleteState.tick_ghost options remaining span machine).trans entry.ghost))
  have shallow : third.user.payload.validation = .Shallow :=
    (RootZeroCompleteState.tick_shallow options remaining span second).trans
      ((RootZeroCompleteState.tick_shallow options remaining span first).trans
        ((RootZeroCompleteState.tick_shallow options remaining span machine).trans entry.shallow))
  have flagsFirst := RootZeroCompleteState.tick_flags options remaining span machine
  have flagsSecond := RootZeroCompleteState.tick_flags options remaining span first
  have flagsThird := RootZeroCompleteState.tick_flags options remaining span second
  refine ⟨result,trace,body.trans entry.body,location,slot,extra,destination,continuation,varargs,immediate,
    ghost,shallow,flagsThird.1.trans (flagsSecond.1.trans (flagsFirst.1.trans unchecked)),
    flagsThird.2.trans (flagsSecond.2.trans (flagsFirst.2.trans gc)),?_,rfl,rfl,rfl⟩
  dsimp only [third,second,first]
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

#print axioms rejectsBeforePhysicalReturn
end DuplicatePrefix.RootZeroShallowReturn

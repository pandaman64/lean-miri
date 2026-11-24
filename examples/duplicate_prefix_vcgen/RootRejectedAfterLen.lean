import RootZeroShallowReturn
import duplicate_prefix.RootRejectedPrefix

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.Verification

set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
set_option linter.unusedVariables false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame

/-- State immediately after the canonical slice-length call. The length and
count are the initialized operands consumed by the emitted rejection guard. -/
structure RejectionEntry (frame : Frame) (machine : MachineState) (length count : UInt64) where
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  location : frame.location = .mir ⟨3, 0⟩
  size : frame.locals.size = 25
  temp : Immediate Provenance
  live12 : (frame.locals[12]'(by rw [size]; decide)).value = .live (.immediate temp)
  live13 : (frame.locals[13]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  cache13 : (frame.locals[13]'(by rw [size]; decide)).layout = none
  live0 : (frame.locals[0]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  cache0 : (frame.locals[0]'(by rw [size]; decide)).layout = none
  live7 : (frame.locals[7]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  live8 : (frame.locals[8]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  cache8 : (frame.locals[8]'(by rw [size]; decide)).layout = none
  live9 : (frame.locals[9]'(by rw [size]; decide)).value =
    .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count))))
  cache9 : (frame.locals[9]'(by rw [size]; decide)).layout = some RootCompilerFacts.usizeLayout
  live10 : (frame.locals[10]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  cache10 : (frame.locals[10]'(by rw [size]; decide)).layout = none
  live11 : (frame.locals[11]'(by rw [size]; decide)).value =
    .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 length))))
  cache11 : (frame.locals[11]'(by rw [size]; decide)).layout = some RootCompilerFacts.usizeLayout
  immediate : ZeroImmediateFacts.AllImmediate frame
  noClocks : frame.extra.dataRace = none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  fixed : machine.threads.fixedScheduling = true

theorem executesRejectionReturn (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1)
    (older : Array Frame) (caller frame : Frame) (machine : MachineState)
    (length count : UInt64) (rejected : count > length / 2)
    (entry : RejectionEntry frame machine length count) (ready : ActiveCaller older caller frame machine)
    (defaultMode : ready.tracker.retagMode = .Default)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent (older.push caller) frame machine
    ∃ popped,
      SuccessfulTrace.Trace config limits before
        (Storage.withCurrent older {putBool caller ready.destinationIndex ready.destinationBound false with
          location := .mir ⟨ready.target, 0⟩} popped) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let olderFrames := older.push caller
  obtain ⟨result, trace, body, identity, instanceEq, extra, destination, continuation, varargs, localsId, size,
      location, slot, immediate⟩ := RootRejectedPrefix.executes options limits remaining span source debugOff fuel fuelEq
        olderFrames frame machine length count rejected entry.size entry.temp entry.live12 entry.live13 entry.cache13
        entry.live0 entry.cache0 entry.live7 entry.live8 entry.cache8 entry.live9 entry.cache9 entry.live10 entry.cache10
        entry.live11 entry.cache11 entry.body entry.identity entry.callee entry.location entry.immediate entry.noClocks
        ready.tracker ready.tracked defaultMode entry.ghost entry.shallow unchecked gc entry.fixed
  let first := RootZeroCompleteState.tick options remaining span machine
  let second := RootZeroCompleteState.tick options remaining span first
  let third := RootZeroCompleteState.tick options remaining span second
  let firstReady : ActiveCaller older caller frame first := {ready with}
  let finalReady := firstReady.afterPrefix options remaining span extra destination continuation varargs
  have bound : 0 < result.locals.size := by rw [size]; decide
  have localSlot : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool false))), some boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans slot)
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
  obtain ⟨popped, last⟩ := stepReturnToCaller options limits remaining span debugOff fuel fuelEq false
    older caller result third finalReady (body.trans entry.body) location bound (congrArg (·.value) localSlot)
    (congrArg (·.layout) localSlot) (congrArg (·.dataRace) extra |>.trans entry.noClocks) immediate
    ghost shallow entry.fixed (flagsThird.2.trans (flagsSecond.2.trans (flagsFirst.2.trans gc)))
    (flagsThird.1.trans (flagsSecond.1.trans (flagsFirst.1.trans unchecked)))
  exact ⟨popped, SuccessfulTrace.append trace (.next last (.refl _))⟩

#print axioms executesRejectionReturn
end DuplicatePrefix.RootZeroShallowReturn

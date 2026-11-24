import duplicate_prefix.AsMutDispatchExact
import duplicate_prefix.CallEntryLocals
import duplicate_prefix.CallUncachedLocal
import duplicate_prefix.CompilerFrameLayout
import NestedGuardDriver

namespace DuplicatePrefix.AsMutCurrentCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev term := AsMutEvaluateCall.terminator

def sourceKind : CallSource := .Normal
def functionSpan : MIR.SpanRef := ⟨39⟩

theorem code : term.kind = .Call HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument]
    ⟨15,#[]⟩ (some 7) .Unreachable sourceKind functionSpan := by
  with_unfolding_all rfl

def cacheCaller (frame : CompilerFrameContext.ActualFrame) (valid : 15 < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 15 CopyCompilerFacts.destPointerLayout valid

private theorem local15 (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 15 (Storage.withCurrent frames frame machine) =
      .ok CopyCompilerFacts.destPointerLayout (Storage.withCurrent frames frame machine) := by
  apply PointerAddFacts.compute_local frames frame machine 15 8 CopyCompilerFacts.destPointerLayout _
    CopyCompilerFacts.dest_pointer_layout_eq
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

theorem call
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debugOff : options.place.debugAssertions = false)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine nextMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entered : CompilerFrameContext.ActualFrame) (value : Immediate Provenance)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (valid : 16 < caller.locals.size)
    (argument : caller.locals[16].value = .live (.immediate value))
    (argLayout : caller.locals[16].layout = some RootCompilerFacts.sliceLayout)
    (uncached : (caller.locals[15]'(by omega)).layout = none)
    (clocks : caller.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let h := ExecutionMachine.callHooks cfg limits
    let before := Storage.withCurrent frames caller machine
    let cached := cacheCaller caller (by omega)
    let prepared := Storage.withCurrent frames cached machine
    let destination := (LocalPlaces.localRuntimePlace frames.size cached 15 CopyCompilerFacts.destPointerLayout).stackView
    let after := Storage.withCurrent (frames.push cached) entered nextMachine
    AsMutCallCore.core h ⟨.immediate value,RootCompilerFacts.sliceLayout⟩ destination prepared = .ok () after →
    Call.evalCallTerminator h () limits.callDispatch term before = .ok () after := by
  intro cfg h before cached prepared destination after installed
  have validArg : 16 < cached.locals.size := by
    simpa [cached, cacheCaller, LocalPlaces.cachePlaceLayout] using valid
  have argStill : cached.locals[16].value = .live (.immediate value) := by
    simpa [cached, cacheCaller, LocalPlaces.cachePlaceLayout, Array.getElem_set] using argument
  have layoutStill : cached.locals[16].layout = some RootCompilerFacts.sliceLayout := by
    simpa [cached, cacheCaller, LocalPlaces.cachePlaceLayout, Array.getElem_set] using argLayout
  have evaluated := AsMutEvaluateCall.evaluate options limits remaining span debugOff source cmp
    frames cached machine value body identity callee located validArg argStill layoutStill clocks ghost
  have placed := CallUncachedLocal.uncached options limits remaining span debugOff frames caller machine
    15 CopyCompilerFacts.destPointerLayout (show (15 : Nat) < caller.locals.size by omega) uncached (by decide +kernel)
    (local15 frames caller machine body identity callee)
  have dispatched := AsMutDispatchExact.dispatch options limits remaining budget span value prepared after destination
    backend race installed
  have oldIndex : h.frameIndex before = .ok frames.size before := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) before = _
    simp [before,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  apply GenericCallStages.call_terminator h () limits.callDispatch term
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ 7 .Unreachable sourceKind functionSpan
    before prepared prepared after caller frames.size (frames.size+1) destination
    ⟨.Instance HelperCompilerFacts.asMutPtrCall.callee,#[.Copy ⟨.immediate value,RootCompilerFacts.sliceLayout⟩],
      .Rust,some HelperCompilerFacts.asMutPtrAbi,false⟩
    code (CallEntryLocals.get_frame options limits remaining span frames caller machine) oldIndex placed evaluated
  · have canUnwind : h.abiCanUnwind HelperCompilerFacts.asMutPtrAbi = false := AsMutCallFacts.abi_flags.2.1
    simpa only [dispatchFuel, Option.any, canUnwind, Bool.false_eq_true, ite_false] using dispatched
  · change (do let state ← get; pure state.stack.frames.isEmpty : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) after = _
    simp [after, Storage.withCurrent, Array.isEmpty_push, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  · exact newIndex
  · omega

noncomputable def charged (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  let user := NestedGuardDriver.nextTerminatorUser
    (PreparedContracts.actualConfig options () remaining span).terminators machine.user
  {machine with user}

theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debugOff : options.place.debugAssertions = false)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine nextMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entered : CompilerFrameContext.ActualFrame) (value : Immediate Provenance)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (valid : 16 < caller.locals.size)
    (argument : caller.locals[16].value = .live (.immediate value))
    (argLayout : caller.locals[16].layout = some RootCompilerFacts.sliceLayout)
    (uncached : (caller.locals[15]'(by omega)).layout = none)
    (clocks : caller.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl machine.user).gcInterval = 0) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let h := ExecutionMachine.callHooks cfg limits
    let before := Storage.withCurrent frames caller machine
    let cached := cacheCaller caller (by omega)
    let prepared := Storage.withCurrent frames cached (charged options remaining span machine)
    let destination := (LocalPlaces.localRuntimePlace frames.size cached 15 CopyCompilerFacts.destPointerLayout).stackView
    let after := Storage.withCurrent (frames.push cached) entered nextMachine
    AsMutCallCore.core h ⟨.immediate value,RootCompilerFacts.sliceLayout⟩ destination prepared = .ok () after →
    ExecutionMachine.step cfg limits () before = (after,.ok true) := by
  intro cfg h before cached prepared destination after installed
  have chargedGhost : (charged options remaining span machine).user.payload.ghost = false := by
    unfold charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).terminators]
    exact ghost
  have chargedBackend : (charged options remaining span machine).user.payload.payload.user.backend = .none := by
    unfold charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).terminators]
    exact backend
  have called := call options limits remaining budget dispatchFuel span debugOff source cmp frames caller
    (charged options remaining span machine) nextMachine entered value body identity callee located
    valid argument argLayout uncached clocks chargedGhost race chargedBackend installed
  have selected : Miri.Verification.StepWP.currentTerminator before = some term := by
    unfold Miri.Verification.StepWP.currentTerminator
    simp only [before,Storage.withCurrent,Stack.currentFrame?,Array.back?_push]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [located,body]
    with_unfolding_all rfl
  have lens := CanonicalConfigFacts.actual_term_get_set options () remaining span
  exact NestedGuardDriver.stepFixedCall cfg limits () before after term HelperCompilerFacts.asMutPtrCall.function
    #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Unreachable sourceKind functionSpan
    code selected lens fixed unchecked noGc (by simp [after,before,Storage.withCurrent]) called

end DuplicatePrefix.AsMutCurrentCall

#print axioms DuplicatePrefix.AsMutCurrentCall.call

#print axioms DuplicatePrefix.AsMutCurrentCall.step

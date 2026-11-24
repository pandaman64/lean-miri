import duplicate_prefix.AsMutReturnExclusive
import duplicate_prefix.AsMutCurrentCall

namespace DuplicatePrefix.AsMutReturnStep
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem returns
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length base : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent (frames.push caller) frame machine) length)
    (region : ExclusiveRegion (Storage.withCurrent (frames.push caller) frame machine) length storage tag)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (loc : frame.location = .mir ⟨0,10⟩)
    (valid0 : 0 < frame.locals.size)
    (cached0 : frame.locals[0].layout = some CopyCompilerFacts.destPointerLayout)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base + storage.relativeStart.bytes)))))))
    (noClocks : frame.extra.dataRace = none)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (destCached : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (continuation : frame.returnContinuation = .goto (some 7) .Unreachable)
    (direct : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (noVarargs : frame.vaList = #[])
    (owned : FrameState) (ledger : frame.extra.borrowTracker = some owned)
    (one : owned.protectedTags = #[(storage.id,tag)])
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (node : TreeNode) (nodeFound : storage.entry.allocation.extra.nodeAt region.source = some node)
    (unexposed : node.isExposed = false)
    (materialized : RetagReleaseFootprint.MaterializedWithin storage.entry.allocation.extra region.source
      storage.relativeStart.bytes (storage.relativeStart.bytes + length))
    (vacant : RetagReleaseFootprint.VacantRows storage.entry.allocation.extra)
    (fits : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (thread : ThreadRecord) (relevance : Nat)
    (current : machine.threads.activeThread? = some thread)
    (cached : FrameRelevance.top ⟨(frames.push caller).push frame⟩ thread.topUserRelevantFrame = some relevance)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent (frames.push caller) frame machine
    let pointer := Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes))
    let value := Scalar.fromPointer cfg.access.runtime.base pointer
    let returned := {AsMutPtrReturn.writeFrame caller callerId (.scalar value) callerValid with location := FrameLocation.mir ⟨7,0⟩}
    ∃ popped : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ExecutionMachine.step cfg limits () before = (Storage.withCurrent frames returned popped,.ok true) ∧
      popped.user.addresses = machine.user.addresses ∧ popped.dataRace = machine.dataRace ∧
      popped.user = (AsMutCurrentCall.charged options (remaining+1) span machine).user ∧
      popped.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      (∃ presentThread, popped.threads.activeThread? = some presentThread) ∧
      ∃ next : InitializedRegion (Storage.withCurrent frames returned popped) length,
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        ∃ right : ExclusiveRegion (Storage.withCurrent frames returned popped) length next tag,
          right.tracker.retagMode = region.tracker.retagMode := by
  intro cfg before pointer value returned
  let charged := AsMutCurrentCall.charged options (remaining+1) span machine
  let staged := Storage.withCurrent (frames.push caller) frame charged
  let live : InitializedRegion staged length := {storage with live := storage.live}
  let permission : ExclusiveRegion staged length live tag := {region with tracked := region.tracked}
  obtain ⟨popped, poppedEq, poppedUser, race, fixedStill, activeThread, next, idEq, offsetEq, rights, mode⟩ :=
    AsMutReturnExclusive.pop options (remaining+1) span frames caller frame charged length tag live permission
      owned ledger one root roots node nodeFound unexposed materialized vacant fits thread relevance current cached
  have ghostStill : charged.user.payload.ghost = false := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ghost
  have validateStill : charged.user.payload.validation = .Shallow := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact shallow
  have addrStill : charged.user.addresses = machine.user.addresses := by
    unfold charged AsMutCurrentCall.charged NestedGuardDriver.nextTerminatorUser
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have popEq : (GenericCallReturn.sourceControl cfg limits).popFrame () staged =
      (Storage.withCurrent frames caller popped,.ok frame) := by
    change MachineHooks.run (TypedMachineBindings.popRaw (TypedMachineBindings.retagHooks cfg.access cfg.retag))
      staged = _
    unfold MachineHooks.run Call.run
    rw [poppedEq]
  have effect := AsMutPtrReturn.return_driver_of_pop options limits remaining span debugOff fuel validationFuel
    frames caller frame charged value callerId body loc valid0 live0 cached0 noClocks
    callerValid destLive destCached callerClocks destination 7 .Unreachable continuation direct noVarargs
    popped (by rw [poppedUser]; exact ghostStill) (by rw [poppedUser]; exact validateStill) ghostStill popEq
  let term := AsMutPtrFacts.block.terminator
  have selected : Miri.Verification.StepWP.currentTerminator before = some term := by
    unfold Miri.Verification.StepWP.currentTerminator
    simp only [before,Storage.withCurrent,Stack.currentFrame?,Array.back?_push]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [loc,body]
    with_unfolding_all rfl
  have exactStep := NestedGuardDriver.stepFixedReturn cfg limits () before term selected
    AsMutPtrFacts.terminator_return (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    fixed unchecked noGc
  have exactReturn : ControlFlow.returnFromCurrentFrame
      (ExecutionMachine.terminatorHooks cfg limits).toControlHooks () false staged =
        (Storage.withCurrent frames returned popped,.ok ()) := effect
  let final := Storage.withCurrent frames returned popped
  let finalStorage : InitializedRegion final length := {next with live := next.live}
  let finalRights : ExclusiveRegion final length finalStorage tag := {rights with tracked := rights.tracked}
  refine ⟨popped, ?_, ?_,race,poppedUser,fixedStill,activeThread,finalStorage,idEq,offsetEq,finalRights,mode⟩
  · change ExecutionMachine.step cfg limits () before = (final,.ok true)
    dsimp only at exactStep
    erw [exactStep]
    change ((ControlFlow.returnFromCurrentFrame _ () false staged).1,
      (ControlFlow.returnFromCurrentFrame _ () false staged).2.map fun _ => true) = _
    rw [exactReturn]
    rfl
  · rw [poppedUser,addrStill]

end DuplicatePrefix.AsMutReturnStep

#print axioms DuplicatePrefix.AsMutReturnStep.returns

import duplicate_prefix.RelevanceCurrent
import duplicate_prefix.EmptyWildcardLenCallReturn
namespace DuplicatePrefix.EmptyWildcardRootLenCall
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts EmptyReferenceContext LenUncachedFrontend EmptyWildcardLenCallReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem returns_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : EmptyReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (older : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (unresolved : EmptyWildcardLocalValidator.Unresolved beforeMachine.user.addresses beforeMachine.memory address)
    (tracker : MachineHooks.BorrowState) (enabled : beforeMachine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : beforeMachine.user.payload.ghost = false) (shallow : beforeMachine.user.payload.validation = .Shallow)
    (race : beforeMachine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : beforeMachine.threads.activeThread? = some thread)
    (cacheBound : ∀ i, thread.topUserRelevantFrame = some i → i < older.size+1)
    (metadata : beforeMachine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : beforeMachine.user.payload.payload.user.types.entries.any (·.value.ty == 2) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent older caller beforeMachine)
        (Storage.withCurrent older (resultFrame caller valid 0) finalMachine) ∧
      finalMachine.memory = beforeMachine.memory ∧
      finalMachine.borrowTracker = some (EmptyReferenceAllocation.allocatedTracker tracker fresh) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let next := PtrMetadataReturn.accountedMachine options remaining span beforeMachine
  let root := cachedCaller caller valid
  have nextTracked : next.borrowTracker = some tracker := enabled
  have nextGhost : next.user.payload.ghost = false := by rw [PtrMetadataReturn.accounted_ghost];exact ghost
  have nextShallow : next.user.payload.validation = .Shallow := by rw [PtrMetadataReturn.accounted_validation];exact shallow
  have nextActive : next.threads.activeThread? = some thread := active
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  let state := Storage.withCurrent older root next
  let destination := (LocalPlaces.localRuntimePlace older.size root 11 RootCompilerFacts.usizeLayout).stackView
  let pushed := LenPush.pushed options.userRelevantCrates state destination
  have pushedSize : pushed.stack.frames.size = older.size+2 := by
    simp [pushed, LenPush.pushed, state, Storage.withCurrent, Nat.add_assoc]
  obtain ⟨index,current,topKnown,presentKnown⟩ := RelevanceCurrent.exists_current
    pushed.stack.frames thread (by rw [pushedSize]; omega) (by
      intro i atIndex
      have bounded := cacheBound i atIndex
      rw [pushedSize]
      omega)
  have typeEq : (LenPush.completed options.userRelevantCrates state destination current).machine.user.payload.payload.user.types =
      beforeMachine.user.payload.payload.user.types := by
    exact EmptyLenPushFacts.types_eq options remaining span older root beforeMachine current
  have postMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination current)).metadata = PreparedReflection.actual.runtime := by
    change (LenPush.completed options.userRelevantCrates state destination current).machine.user.payload.payload.user.types.metadata = _
    rw [typeEq]
    exact metadata
  have postNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination current)).entries.any (·.value.ty == 2) = false := by
    change (LenPush.completed options.userRelevantCrates state destination current).machine.user.payload.payload.user.types.entries.any (·.value.ty == 2) = false
    rw [typeEq]
    exact notConstructed
  have nextUnresolved : EmptyWildcardLocalValidator.Unresolved next.user.addresses next.memory address := by
    unfold next PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact unresolved
  exact EmptyWildcardLenCallReturn.wildcard_zero options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq address nonzero older caller next nextUnresolved tracker nextTracked defaultMode fresh valid live uncached noClocks nextGhost nextShallow race thread index current nextActive topKnown presentKnown postMetadata postNotConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached nextBackend beforeMachine rfl unchecked noGc fixed
end
end DuplicatePrefix.EmptyWildcardRootLenCall
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.EmptyWildcardRootLenCall.returns_zero) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved root singleton len call {dependency}"

import duplicate_prefix.AddCallStep
import duplicate_prefix.AddInstalledFrame
import duplicate_prefix.PointerAddGuardBoundary

namespace DuplicatePrefix.RootCurrentAddCall
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
open AddUncachedCall AddEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- The exact state pushed by the root's emitted ptr.add call terminator. -/
noncomputable def entered
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 21 < caller.locals.size) (noRace : machine.dataRace = none)
    (pointer : Scalar Provenance) (count : UInt64) :=
  let current := cachedCaller caller valid
  let charged := AddCallStep.accountedMachine options remaining span machine
  initialized (Storage.withCurrent frames current charged)
    (LocalPlaces.localRuntimePlace frames.size current 21 CopyCompilerFacts.destPointerLayout).stackView
    (.goto (some 8) .Unreachable) noRace pointer count

noncomputable def enteredMachine (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  (CallEntryFacts.freshRoot (AddCallStep.accountedMachine options remaining span machine)).1

theorem entered_addresses (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (enteredMachine options remaining span machine).user.addresses = machine.user.addresses := by
  unfold enteredMachine CallEntryFacts.freshRoot AddCallStep.accountedMachine
    PointerAddCurrentReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

/-- Compose the actual root call, its language-check trace, and the exact
positive pointer offset and return. -/
theorem from_call
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (pointer : Scalar Provenance) (n : UInt64) (valid : 21 < caller.locals.size)
    (live : caller.locals[21].value = .live (.immediate .uninit))
    (uncached : caller.locals[21].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨7,RootCallerLocation.statementCount 7⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size)
    (relevant : caller.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (source : PreparedContracts.SourceComparator)
    (valid22 : 22 < caller.locals.size) (valid23 : 23 < caller.locals.size)
    (live22 : caller.locals[22].value = .live (.immediate (.scalar pointer)))
    (cache22 : caller.locals[22].layout = some CopyCompilerFacts.destPointerLayout)
    (live23 : caller.locals[23].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache23 : caller.locals[23].layout = some RootCompilerFacts.usizeLayout)
    (id : AllocId) (tag : BorTag) (base offset : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (raw : pointer = Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (positive : 0 < n.toNat) (fits : n.toNat < 2^63)
    (bounds : offset.toNat + n.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (mode : tracker.retagMode = .Default)
    (guard : PointerAddGuardBoundary.Reaches options limits remaining span frames
      (cachedCaller caller valid) (entered options remaining span frames caller machine valid noRace pointer n)
      (enteredMachine options remaining span machine) pointer n) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let current := cachedCaller caller valid
    let advanced := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset+n)))
    ∃ done finalMachine,
      finalMachine = PointerAddCurrentReturn.poppedMachine frames current done
        (PointerAddCurrentReturn.accountedMachine options remaining span guard.machine)
        (guard.thread.topUserRelevantFrame.getD (frames.push current).size) ∧
      finalMachine.memory = machine.memory ∧ finalMachine.borrowTracker = machine.borrowTracker ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames
          {PointerAddCurrentReturn.writeFrame current 21 (.scalar advanced)
            (by simpa [current,cachedCaller,LocalPlaces.cachePlaceLayout] using valid)
            with location := .mir ⟨8,0⟩} finalMachine) := by
  subst pointer
  let pointer : Scalar Provenance := Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))
  let current := cachedCaller caller valid
  let charged := AddCallStep.accountedMachine options remaining span machine
  let state := Storage.withCurrent frames current charged
  let destination := (LocalPlaces.localRuntimePlace frames.size current 21 CopyCompilerFacts.destPointerLayout).stackView
  let root := rawRoot state destination (.goto (some 8) .Unreachable) noRace
  let initial := enteredMachine options remaining span machine
  let frame := entered options remaining span frames caller machine valid noRace pointer n
  have start := AddCallStep.step options limits remaining span debug frames caller machine tracker tracked pointer n
    valid .uninit live uncached noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow
    thread active top relevant budget budgetEq backend unchecked noGc fixed source
    valid22 valid23 live22 cache22 live23 cache23
  have saved := AddInstalledFrame.metadata root pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span
  have callerDestination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size current 21 CopyCompilerFacts.destPointerLayout := by
    change (AddInstalledFrame.installed root pointer n AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span).returnPlace.toRuntimePlace = _
    rw [saved.2.2.2.2.1]
    rfl
  have callerContinuation : frame.returnContinuation = .goto (some 8) .Unreachable := by
    exact saved.2.2.2.1
  have validCurrent : 21 < current.locals.size := by simpa [current,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have liveCurrent : current.locals[21].value = .live (.immediate .uninit) := by
    simpa [current,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have layoutCurrent : current.locals[21].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [current,cachedCaller,LocalPlaces.cachePlaceLayout]
  have initialGhost : initial.user.payload.ghost = false := by
    exact (PointerAddCurrentReturn.accounted_ghost options remaining span machine).trans ghost
  have initialShallow : initial.user.payload.validation = .Shallow := by
    exact (PointerAddCurrentReturn.accounted_validation options remaining span machine).trans shallow
  have initialAddresses : initial.user.addresses = machine.user.addresses :=
    entered_addresses options remaining span machine
  have initialAddress : initial.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [initialAddresses]
    exact address
  obtain ⟨done,finalMachine,shape,memory,trackerEq,addresses,tail⟩ :=
    PointerAddGuardBoundary.returns options limits remaining span debug fuel validationFuel frames current frame initial
      id tag base offset n entry guard tracker tracked mode initialGhost initialShallow initialAddress present positive fits bounds
      21 validCurrent liveCurrent layoutCurrent noClocks callerDestination 8 .Unreachable callerContinuation
  have finalGhost : finalMachine.user.payload.ghost = false := by
    rw [shape, PointerAddCurrentReturn.popped_user, PointerAddCurrentReturn.accounted_ghost]
    exact guard.ghost.trans initialGhost
  have finalShallow : finalMachine.user.payload.validation = .Shallow := by
    rw [shape, PointerAddCurrentReturn.popped_user, PointerAddCurrentReturn.accounted_validation]
    exact guard.validation.trans initialShallow
  exact ⟨done,finalMachine,shape,memory,trackerEq,addresses.trans initialAddresses,finalGhost,finalShallow,.next start tail⟩

#print axioms from_call

end DuplicatePrefix.RootCurrentAddCall

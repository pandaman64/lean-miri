import duplicate_prefix.RootCurrentAddCall
import duplicate_prefix.CopyRootGuardState

namespace DuplicatePrefix.RootCurrentAddCallExact
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
open RootCurrentAddCall AddUncachedCall
set_option maxRecDepth 65536
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

structure Preserves (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (thread : ThreadRecord) : Prop where
  race : after.dataRace = before.dataRace
  backend : after.user.payload.payload.user.backend = before.user.payload.payload.user.backend
  extras : after.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras
  fixed : after.threads.fixedScheduling = true
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
    after.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
    after.user).gcInterval = 0
  active : after.threads.activeThread? = some thread

/-- The actual caller resumes with the same scheduler cache and physical
backing after offset, once the guard scope retains the root's cached thread. -/
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
      (enteredMachine options remaining span machine) pointer n)
    (backendSame : guard.machine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend)
    (extrasSame : guard.machine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras)
    (sameThread : guard.thread = thread) :
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
      Preserves options remaining span machine finalMachine thread ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames
          {PointerAddCurrentReturn.writeFrame current 21 (.scalar advanced)
            (by simpa [current,cachedCaller,LocalPlaces.cachePlaceLayout] using valid)
            with location := .mir ⟨8,0⟩} finalMachine) := by
  obtain ⟨done,finalMachine,finalShape,mem,bt,addresses,lastGhost,lastShallow,trace⟩ :=
    RootCurrentAddCall.from_call options limits remaining span debug frames caller machine tracker tracked pointer n valid live uncached
      noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow thread active top relevant
      budget budgetEq backend unchecked noGc fixed source valid22 valid23 live22 cache22 live23 cache23
      id tag base offset entry raw address present positive fits bounds mode guard
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let next := PointerAddCurrentReturn.accountedMachine options remaining span guard.machine
  have finalEq : finalMachine = next := by
    rw [finalShape]
    unfold PointerAddCurrentReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    rw [sameThread,top]
    simp [Array.size_push]
    rfl
  obtain ⟨m,t,ts,dr,a,g,v,bk,e,k⟩ := CopyRootGuardState.accounted_fields options remaining span guard.machine
  have clock : cfg.terminators.getControl next.user = TerminatorClock.advance (cfg.terminators.getControl guard.machine.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have steady : Preserves options remaining span machine finalMachine thread := by
    rw [finalEq]
    refine ⟨dr.trans guard.dataRace,bk.trans backendSame,e.trans extrasSame,guard.fixed,?_,?_,?_⟩
    · change (cfg.terminators.getControl next.user).checkedArithmetic = _
      rw [clock]
      exact guard.checked
    · change (cfg.terminators.getControl next.user).gcInterval = _
      rw [clock]
      exact guard.noGc
    · exact guard.active.trans (congrArg some sameThread)
  exact ⟨done,finalMachine,finalShape,mem,bt,addresses,lastGhost,lastShallow,steady,trace⟩

end DuplicatePrefix.RootCurrentAddCallExact

#print axioms DuplicatePrefix.RootCurrentAddCallExact.from_call

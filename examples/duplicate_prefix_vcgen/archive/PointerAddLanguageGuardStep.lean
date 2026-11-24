import duplicate_prefix.PointerAddLanguageGuardUncached
import duplicate_prefix.PointerAddCurrentReturn
namespace DuplicatePrefix.PointerAddLanguageGuardStep
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix PointerAddLanguageGuardUncached
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def accountedMachine := PointerAddCurrentReturn.accountedMachine
theorem step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (original : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : original.body = PointerAddCurrentFacts.body.body)
    (identity : original.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : original.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : original.location = .mir ⟨0,2⟩)
    (originalSize : 4 < original.locals.size)
    (originalLive : original.locals[4].value = .live (.immediate .uninit))
    (originalUncached : original.locals[4].layout = none)
    (originalNoClocks : original.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine)) (LanguageGuardEntryAt.destination frames original 4)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine)) (LanguageGuardEntryAt.destination frames original 4)).stack.frames[threadIndex]? = some current)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames original machine) =
      (Storage.withCurrent (frames.push (cachedCaller original originalSize))
        (LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine))
          (LanguageGuardEntryAt.destination frames original 4)))
        (LanguageZeroEntry.pushedMachine options (Storage.withCurrent frames (cachedCaller original originalSize) (accountedMachine options remaining span machine))
          (LanguageGuardEntryAt.destination frames original 4) current), .ok true) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent frames original machine
  let next := accountedMachine options remaining span machine
  let nextState := Storage.withCurrent frames original next
  have nextTracked : next.borrowTracker = some tracker := tracked
  have nextRace : next.dataRace = none := noRace
  have nextActive : next.threads.activeThread? = some thread := active
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    change (PointerAddCurrentReturn.accountedMachine options remaining span machine).user.payload.payload.user.backend = _
    unfold PointerAddCurrentReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextGhost : next.user.payload.ghost = false := by
    change (PointerAddCurrentReturn.accountedMachine options remaining span machine).user.payload.ghost = false
    rw [PointerAddCurrentReturn.accounted_ghost]; exact ghost
  have effect := PointerAddLanguageGuardUncached.call_uncached options limits remaining budget dispatchFuel span source debugOff frames original next
    body identity callee location originalSize originalLive originalUncached originalNoClocks nextRace nextBackend nextGhost
    tracker nextTracked thread threadIndex current nextActive top present
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := PointerAddCurrentFacts.body.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  have blockAt : original.body.basicBlocks[0]? = some block := by rw [body]; simp [block]
  have noStatement : block.statements[2]? = none := by with_unfolding_all rfl
  have sourceCall : block.terminator.kind = .Call PointerAddLanguageGuardUncached.function #[] ⟨4,#[]⟩ (some 1) .Unreachable .Normal ⟨86⟩ := by
    with_unfolding_all rfl
  apply GenericCallStages.source_step cfg limits () before nextState _ original ⟨0,2⟩ block
    PointerAddLanguageGuardUncached.function #[] ⟨4,#[]⟩ (some 1) .Unreachable .Normal ⟨86⟩
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement sourceCall accounting' effect
  simp [Storage.withCurrent,nextState]
end DuplicatePrefix.PointerAddLanguageGuardStep
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PointerAddLanguageGuardStep.step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved language actual step dependency {dependency}"

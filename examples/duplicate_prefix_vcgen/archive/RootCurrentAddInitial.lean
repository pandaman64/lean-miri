import duplicate_prefix.RootCurrentAddCall
import duplicate_prefix.PointerAddCurrentFullGuard
import duplicate_prefix.CopyPushPreserves

namespace DuplicatePrefix.RootCurrentAddInitial
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem shape
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 21 < caller.locals.size) (noRace : machine.dataRace = none)
    (pointer : Scalar Provenance) (count : UInt64)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker) :
    PointerAddCurrentFullGuard.Initial (RootCurrentAddCall.entered options remaining span frames caller machine valid noRace pointer count) pointer count := by
  let cached := AddUncachedCall.cachedCaller caller valid
  let charged := AddCallStep.accountedMachine options remaining span machine
  let state := Storage.withCurrent frames cached charged
  let dest := (LocalPlaces.localRuntimePlace frames.size cached 21 CopyCompilerFacts.destPointerLayout).stackView
  let raw := AddEntry.rawRoot state dest (.goto (some 8) .Unreachable) noRace
  let preamble := AddEntryFacts.addPreamble
  let spanAt := (RootCallerLocation.sourceInfo 7).span
  let frame := AddInstalledFrame.installed raw pointer count preamble spanAt
  change PointerAddCurrentFullGuard.Initial frame pointer count
  have rawLocals : raw.frame.locals = Array.replicate 12 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    AddEntry.raw_locals state dest (.goto (some 8) .Unreachable) noRace
  have size := AddInstalledFrame.size raw pointer count preamble spanAt
  obtain ⟨b,ident,fn,cont,place,va,clocks,borrow,pc⟩ := AddInstalledFrame.metadata raw pointer count preamble spanAt
  have slot (i : Fin 12) : frame.locals[i.val]? = some
      (if 0 = i.val then ⟨.live (.immediate .uninit),none⟩
       else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
       else if 1 = i.val then ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩
       else ⟨.dead,none⟩) := by
    have bound : i.val < frame.locals.size := by rw [size]; exact i.isLt
    rw [getElem?_pos frame.locals i.val bound]
    exact congrArg some (AddInstalledFrame.slot raw rawLocals pointer count preamble spanAt i)
  have rawBorrow : raw.frame.extra.borrowTracker = some ({} : FrameState) := by
    change (machine.borrowTracker.map (fun _ => ({} : FrameState))) = _
    rw [tracked]
    rfl
  refine ⟨size, b.trans raw.body, ident.trans raw.identity, fn.trans raw.callee, pc, clocks.trans raw.noClocks,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, AddInstalledFrame.immediate raw rawLocals pointer count preamble spanAt, va, borrow.trans rawBorrow⟩
  all_goals first
    | simpa only [Nat.reduceEqDiff,ite_false,ite_true,eq_self_iff_true] using slot ⟨0,by decide⟩
    | simpa only [Nat.reduceEqDiff,ite_false,ite_true,eq_self_iff_true] using slot ⟨1,by decide⟩
    | simpa only [Nat.reduceEqDiff,ite_false,ite_true,eq_self_iff_true] using slot ⟨2,by decide⟩
    | simpa only [Nat.reduceEqDiff,ite_false,ite_true,eq_self_iff_true] using slot ⟨3,by decide⟩
    | simpa only [Nat.reduceEqDiff,ite_false,ite_true,eq_self_iff_true] using slot ⟨4,by decide⟩
    | simpa only [Nat.reduceEqDiff,ite_false,ite_true,eq_self_iff_true] using slot ⟨10,by decide⟩
    | simpa only [Nat.reduceEqDiff,ite_false,ite_true,eq_self_iff_true] using slot ⟨11,by decide⟩

/-- Discharge the pointer-add guard premise at the actual state built by root call initialization. -/
theorem actual_guard_profile
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (callFuel : limits.callDispatch = budget+1)
    (validationFuel : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 21 < caller.locals.size) (noRace : machine.dataRace = none)
    (pointer : Scalar Provenance) (count : UInt64)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size) :
    ∃ result : PointerAddGuardBoundary.Reaches options limits remaining span frames
      (AddUncachedCall.cachedCaller caller valid)
      (RootCurrentAddCall.entered options remaining span frames caller machine valid noRace pointer count)
      (RootCurrentAddCall.enteredMachine options remaining span machine) pointer count,
      result.machine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      result.machine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (LanguageZeroEntryFacts.rank options.userRelevantCrates < caller.extra.userRelevance →
        RuntimeZeroEntryFacts.rank options.userRelevantCrates < caller.extra.userRelevance → result.thread = thread) := by
  let enteredMachine := RootCurrentAddCall.enteredMachine options remaining span machine
  have fields := CopyPushPreserves.fields options remaining span machine
  have control := CopyPushPreserves.control options remaining span machine
  have check' : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      enteredMachine.user).checkedArithmetic = false := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (CopyPushPreserves.post options remaining span machine).user).checkedArithmetic = false
    rw [control]
    exact unchecked
  have gc' : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      enteredMachine.user).gcInterval = 0 := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (CopyPushPreserves.post options remaining span machine).user).gcInterval = 0
    rw [control]
    exact noGc
  obtain ⟨result,bk,extras,stable⟩ :=
    PointerAddCurrentFullGuard.reaches_offset_profile options limits remaining budget fuel callFuel validationFuel statementFuel
    span source debug frames (AddUncachedCall.cachedCaller caller valid)
    (RootCurrentAddCall.entered options remaining span frames caller machine valid noRace pointer count) enteredMachine pointer count
    (shape options remaining span frames caller machine valid noRace pointer count tracker tracked)
    tracker (fields.2.1.trans tracked) mode (fields.2.2.2.1.trans noRace)
    (fields.2.2.2.2.2.2.2.1.trans backend) (fields.2.2.2.2.2.1.trans ghost)
    (fields.2.2.2.2.2.2.1.trans shallow) check' gc' fixed thread active top
  exact ⟨result,bk.trans fields.2.2.2.2.2.2.2.1,extras.trans fields.2.2.2.2.2.2.2.2.1,stable⟩

theorem actual_guard
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (callFuel : limits.callDispatch = budget+1)
    (validationFuel : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 21 < caller.locals.size) (noRace : machine.dataRace = none)
    (pointer : Scalar Provenance) (count : UInt64)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size) :
    Nonempty (PointerAddGuardBoundary.Reaches options limits remaining span frames
      (AddUncachedCall.cachedCaller caller valid)
      (RootCurrentAddCall.entered options remaining span frames caller machine valid noRace pointer count)
      (RootCurrentAddCall.enteredMachine options remaining span machine) pointer count)  := by
  obtain ⟨result,_,_,_⟩ := actual_guard_profile options limits remaining budget fuel callFuel validationFuel
    statementFuel span source debug frames caller machine valid noRace pointer count tracker tracked mode
    backend ghost shallow unchecked noGc fixed thread active top
  exact ⟨result⟩

end DuplicatePrefix.RootCurrentAddInitial

#print axioms DuplicatePrefix.RootCurrentAddInitial.actual_guard
#print axioms DuplicatePrefix.RootCurrentAddInitial.actual_guard_profile

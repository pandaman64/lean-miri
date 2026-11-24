import RootRejectedAfterLen
import duplicate_prefix.RootAcceptedPreparation
import duplicate_prefix.EmptyRootSafetyPrelude

namespace DuplicatePrefix.RootAcceptedAfterLen
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open CanonicalConfigFacts RootZeroCompleteState RootZeroShallowReturn

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem prepared
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (accepted : ¬ count > len / 2)
    (entry : RejectionEntry frame machine len count)
    (none7 : (frame.locals[7]'(by rw [entry.size]; decide)).layout = none)
    (slot15 : frame.locals[15]? = some ⟨.dead,none⟩)
    (slot16 : frame.locals[16]? = some ⟨.dead,none⟩)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ (done : CompilerFrameContext.ActualFrame) (charged : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent older frame machine) (Storage.withCurrent older done charged) ∧
      done.location = .mir ⟨6,7⟩ ∧
      done.locals[0]? = frame.locals[0]? ∧ done.locals[1]? = frame.locals[1]? ∧ done.locals[2]? = frame.locals[2]? ∧ done.locals.size = 25 ∧
      done.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      done.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧ done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧
      charged.memory = machine.memory ∧ charged.borrowTracker = machine.borrowTracker ∧
      charged.dataRace = machine.dataRace ∧ charged.threads = machine.threads ∧
      charged.user.addresses = machine.user.addresses ∧ charged.user.payload.ghost = false ∧
      charged.user.payload.validation = .Shallow ∧
      (EvalProjectionMachine.arrays.get (Storage.withCurrent older done charged)) =
        (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)) ∧
      (cfg.terminators.getControl charged.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl charged.user).gcInterval = 0 ∧
      charged.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      charged.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∀ i, 17 ≤ i → done.locals[i]? = frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate done ∧
      done.trackCallerArg = frame.trackCallerArg ∧
      done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity := by
  intro cfg
  obtain ⟨loc,trace,locDirect,sameBody,sameId,sameCallee,sameExtra,destination,continuation,vaList,localsId,size,kept,_,trackedCaller⟩ :=
    EmptyRootSafetyPrelude.executesWithCaller options limits remaining span source debug fuel budget older frame machine
      entry.immediate entry.size entry.temp entry.live12 entry.live13 entry.cache13
      entry.body entry.identity entry.callee entry.location entry.noClocks entry.ghost entry.shallow unchecked noGc entry.fixed
  let after := {loc with location := FrameLocation.mir ⟨4,0⟩}
  let next := tick options remaining span machine
  have keptAt (index : Nat) (bounds : index < 25) (n12 : index ≠ 12) (n13 : index ≠ 13) :
      after.locals[index]'(by change index < loc.locals.size; omega) = frame.locals[index]'(by rw [entry.size]; exact bounds) := by
    have saved := kept index n12 n13
    have beforeBound : index < frame.locals.size := by rw [entry.size]; exact bounds
    have afterBound : index < loc.locals.size := by rwa [size]
    rw [Array.getElem?_eq_getElem beforeBound,Array.getElem?_eq_getElem afterBound] at saved
    exact Option.some.inj saved
  have nextClocks : after.extra.dataRace = none := by
    change loc.extra.dataRace = none
    rw [sameExtra]
    exact entry.noClocks
  have nextGhost : next.user.payload.ghost = false := (tick_ghost options remaining span machine).trans entry.ghost
  have nextShallow : next.user.payload.validation = .Shallow := (tick_shallow options remaining span machine).trans entry.shallow
  have controls := tick_flags options remaining span machine
  have exactSize : after.locals.size = 25 := size
  have group := RootAcceptedPreparation.prepares options limits remaining span source debug fuel budget older after next
    len count accepted exactSize
    ⟨.uninit,by rw [keptAt 7 (by decide) (by decide) (by decide)]; exact entry.live7⟩
    (by rw [keptAt 7 (by decide) (by decide) (by decide)]; exact none7)
    (by rw [keptAt 11 (by decide) (by decide) (by decide)]; exact entry.live11)
    (by rw [keptAt 9 (by decide) (by decide) (by decide)]; exact entry.live9)
    (by rw [keptAt 11 (by decide) (by decide) (by decide)]; exact entry.cache11)
    (by rw [keptAt 9 (by decide) (by decide) (by decide)]; exact entry.cache9)
    (by rw [keptAt 10 (by decide) (by decide) (by decide)]; exact entry.live10)
    (by rw [keptAt 10 (by decide) (by decide) (by decide)]; exact entry.cache10)
    (by rw [keptAt 8 (by decide) (by decide) (by decide)]; exact entry.live8)
    (by rw [keptAt 8 (by decide) (by decide) (by decide)]; exact entry.cache8)
    ((kept 15 (by decide) (by decide)).trans slot15) ((kept 16 (by decide) (by decide)).trans slot16)
    (sameBody.trans entry.body) (sameId.trans entry.identity) (sameCallee.trans entry.callee) rfl
    nextClocks tracker tracked mode nextGhost nextShallow entry.fixed (controls.1.trans unchecked) (controls.2.trans noGc)
  obtain ⟨done,run,shape,zero,one,two,body,identity,callee,extra,memory,borrow,race,threads,addresses,ghost,shallow,arrays,flag,gc,backend,extras,keptTail,immediate,doneTrack,donePlace,doneCont,doneVaList,doneLocalsId⟩ := group
  have first : SuccessfulTrace.Trace cfg limits
      (Storage.withCurrent older frame machine) (Storage.withCurrent older after next) := by
    simpa only [cfg,after,next,tick,SourceControl.accounted,Storage.withCurrent] using trace
  have unchanged : next.user.addresses = machine.user.addresses := by
    unfold next tick
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have arraysBefore : (EvalProjectionMachine.arrays.get (Storage.withCurrent older after next)) =
      (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)) := by
    unfold next tick
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have backendBefore : next.user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
    unfold next tick
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have extrasBefore : next.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    unfold next tick
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  refine ⟨done,_,SuccessfulTrace.append first run,shape.location,zero.trans (kept 0 (by decide) (by decide)),one.trans (kept 1 (by decide) (by decide)),
    two.trans (kept 2 (by decide) (by decide)),shape.size,shape.slot15,shape.slot16,
    body.trans sameBody,identity.trans sameId,callee.trans sameCallee,extra.trans sameExtra,
    memory,borrow,race,threads,addresses.trans unchanged,ghost,shallow,arrays.trans arraysBefore,flag,gc,backend.trans backendBefore,extras.trans extrasBefore,?_,immediate locDirect,
    doneTrack.trans trackedCaller,donePlace.trans destination,doneCont.trans continuation,
    doneVaList.trans vaList,doneLocalsId.trans localsId⟩
  intro i above
  exact (keptTail i above).trans (kept i (by omega) (by omega))

end DuplicatePrefix.RootAcceptedAfterLen

#print axioms DuplicatePrefix.RootAcceptedAfterLen.prepared

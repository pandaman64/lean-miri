import duplicate_prefix.RootCurrentDecision
import duplicate_prefix.RootMutPreparation
import duplicate_prefix.RootTwoPhaseComplete

namespace DuplicatePrefix.RootAcceptedPreparation
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open CanonicalConfigFacts PreparedArguments

set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

private def word (value : UInt64) : Immediate Provenance := .scalar (.fromScalarInt (.ofUInt64 value))

theorem prepares
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len count : UInt64) (accepted : ¬ count > len / 2)
    (size : frame.locals.size = 25)
    (live7 : ∃ temp, (frame.locals[7]'(by omega)).value = .live (.immediate temp))
    (none7 : (frame.locals[7]'(by omega)).layout = none)
    (hasLength : (frame.locals[11]'(by omega)).value = .live (.immediate (word len)))
    (hasCount : (frame.locals[9]'(by omega)).value = .live (.immediate (word count)))
    (lengthCached : (frame.locals[11]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (countCached : (frame.locals[9]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (halfLive : (frame.locals[10]'(by omega)).value = .live (.immediate .uninit))
    (halfUncached : (frame.locals[10]'(by omega)).layout = none)
    (boundLive : (frame.locals[8]'(by omega)).value = .live (.immediate .uninit))
    (boundUncached : (frame.locals[8]'(by omega)).layout = none)
    (slot15 : frame.locals[15]? = some ⟨.dead,none⟩)
    (slot16 : frame.locals[16]? = some ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨4,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let decided := RootCurrentDecision.decisionFrame frame len count (by omega)
    let charged := RootCurrentDecision.decisionMachine config older frame machine len count (by omega)
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent older frame machine) (Storage.withCurrent older done charged) ∧
      RootMutPreparationFacts.Shape decided done ∧
      done.locals[0]? = frame.locals[0]? ∧ done.locals[1]? = frame.locals[1]? ∧ done.locals[2]? = frame.locals[2]? ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧ done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧
      charged.memory = machine.memory ∧ charged.borrowTracker = machine.borrowTracker ∧
      charged.dataRace = machine.dataRace ∧ charged.threads = machine.threads ∧
      charged.user.addresses = machine.user.addresses ∧ charged.user.payload.ghost = false ∧
      charged.user.payload.validation = .Shallow ∧
      (EvalProjectionMachine.arrays.get (Storage.withCurrent older done charged)) =
        (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)) ∧
      (config.terminators.getControl charged.user).checkedArithmetic = false ∧
      (config.terminators.getControl charged.user).gcInterval = 0 ∧
      charged.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      charged.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∀ i, 17 ≤ i → done.locals[i]? = frame.locals[i]?) ∧
      (CopyHelperCleanup.AllImmediate frame → CopyHelperCleanup.AllImmediate done) ∧
      done.trackCallerArg = frame.trackCallerArg ∧
      done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity := by
  intro cfg decided charged
  have cap : 11 < frame.locals.size := by omega
  have branched := RootCurrentDecision.evaluateCurrentBounds options limits remaining span source debug fuel budget older frame machine
    len count cap hasLength hasCount lengthCached countCached halfLive halfUncached boundLive boundUncached body identity callee
    located noClocks ghost shallow fixed unchecked noGc
  obtain ⟨decidedSize,decidedBody,decidedIdentity,decidedCallee,decidedExtra,kept,result,half⟩ :=
    RootCurrentDecision.decisionFrameShape frame len count cap
  obtain ⟨keptMemory,keptTrack,keptRace,keptThreads,keptAddr,keptGhost,keptShallow⟩ :=
    RootCurrentDecision.decisionMachineShape options (remaining+1) span older frame machine len count cap
  have loc : decided.location = .mir ⟨6,0⟩ := by
    simp [decided,RootCurrentDecision.decisionFrame,accepted]
  have exactSize : decided.locals.size = 25 := decidedSize.trans size
  have readOld (id : Nat) (bounded : id < 25) (d8 : id ≠ 8) (d10 : id ≠ 10) (d11 : id ≠ 11) :
      decided.locals[id]'(by omega) = frame.locals[id]'(by omega) := by
    apply Option.some.inj
    have output := kept id d8 d10 d11
    rw [Array.getElem?_eq_getElem (show id < decided.locals.size by omega),
      Array.getElem?_eq_getElem (show id < frame.locals.size by omega)] at output
    exact output
  have readNew (id : Nat) (bounded : id < 25) (slot : LocalState Provenance LocalLayout)
      (eq : decided.locals[id]? = some slot) : decided.locals[id]'(by omega) = slot :=
    Option.some.inj ((Array.getElem?_eq_getElem (show id < decided.locals.size by omega)).symm.trans eq)
  obtain ⟨temp7,live⟩ := live7
  have old15 := readNew 15 (by decide) _ ((kept 15 (by decide) (by decide) (by decide)).trans slot15)
  have old16 := readNew 16 (by decide) _ ((kept 16 (by decide) (by decide) (by decide)).trans slot16)
  have result8 := readNew 8 (by decide) _ result
  have result10 := readNew 10 (by decide) _ half
  obtain ⟨done, steps, shape⟩ := RootMutPreparation.executes options limits remaining span source debug fuel budget
    older decided charged exactSize temp7 (.scalar (.fromBool false)) (word count) (word (len/2))
    (by rw [readOld 7 (by decide) (by decide) (by decide) (by decide),live])
    (by rw [readOld 7 (by decide) (by decide) (by decide) (by decide),none7])
    (by rw [result8]; simp [accepted])
    (by rw [readOld 9 (by decide) (by decide) (by decide) (by decide),hasCount])
    (by rw [result10] <;> rfl) (by rw [old15]) (by rw [old15]) (by rw [old16]) (by rw [old16])
    (decidedBody.trans body) (decidedIdentity.trans identity) (decidedCallee.trans callee) loc
    (by rw [decidedExtra]; exact noClocks) tracker (keptTrack.trans tracked) mode (keptGhost.trans ghost) (keptShallow.trans shallow)
  obtain ⟨arrays, flag, gc, backend, extras⟩ := RootCurrentDecision.decisionPolicy options (remaining+1) span older frame done
    machine len count cap
  obtain ⟨track,place,cont,varargs,locals⟩ := RootCurrentDecision.decisionStatic frame len count cap
  refine ⟨done,SuccessfulTrace.append branched steps,shape,
    shape.slot0.trans (kept 0 (by decide) (by decide) (by decide)),
    shape.slot1.trans (kept 1 (by decide) (by decide) (by decide)),
    shape.slot2.trans (kept 2 (by decide) (by decide) (by decide)),
    shape.body.trans decidedBody, shape.identity.trans decidedIdentity, shape.callee.trans decidedCallee,
    shape.extra.trans decidedExtra, keptMemory,keptTrack,keptRace,keptThreads,keptAddr,
    keptGhost.trans ghost,keptShallow.trans shallow,arrays,flag.trans unchecked,gc.trans noGc,backend,extras,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i above
    exact (shape.kept i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (kept i (by omega) (by omega) (by omega))
  · intro all
    apply shape.immediate
    change CopyHelperCleanup.AllImmediate (RootCurrentDecision.decisionFrame frame len count cap)
    exact RootCurrentDecision.decisionImmediate frame len count cap all
  · exact shape.trackedCaller.trans track
  · exact shape.destination.trans place
  · exact shape.continuation.trans cont
  · exact shape.varargs.trans varargs
  · exact shape.localsIdentity.trans locals


end DuplicatePrefix.RootAcceptedPreparation

#print axioms DuplicatePrefix.RootAcceptedPreparation.prepares

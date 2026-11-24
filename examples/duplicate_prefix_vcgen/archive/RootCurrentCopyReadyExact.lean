import duplicate_prefix.RootCurrentAddPipelineExact
import duplicate_prefix.RootCopyPreparation

namespace DuplicatePrefix.RootCurrentCopyReadyExact
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

/-- Prepare the actual copy call after the emitted pointer-add return. -/
theorem from_bb7
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationFuel : options.limits.validation=fuel+1)
    (statementFuel : limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (pointer : Scalar Provenance) (count : UInt64) (temp16 : Immediate Provenance)
    (size : frame.locals.size=25)
    (live15 : (frame.locals[15]'(by omega)).value=.live (.immediate (.scalar pointer)))
    (cache15 : (frame.locals[15]'(by omega)).layout=some CopyCompilerFacts.destPointerLayout)
    (live16 : (frame.locals[16]'(by omega)).value=.live (.immediate temp16))
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (unused : ∀i(v:i<frame.locals.size),17≤i→i≤23→(frame.locals[i]'v)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨7,0⟩)
    (noClocks : frame.extra.dataRace=none) (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (mode : tracker.retagMode=.Default) (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (all : CopyHelperCleanup.AllImmediate frame)
    (id : AllocId) (tag : BorTag) (baseAddr offset : UInt64)
    (allocation : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (pointerEq : pointer = Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (baseAddr+offset))))
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,baseAddr⟩)
    (present : machine.memory.live[id]? = some allocation)
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounded : offset.toNat + count.toNat ≤ allocation.allocation.byteSize.bytes.toNat)
    (noRace : machine.dataRace = none) (trackNone : frame.trackCallerArg = none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size) (relevant : frame.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (source : PreparedContracts.SourceComparator)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (dead24 : frame.locals[24]? = some ⟨.dead,none⟩)
:
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let advanced := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (baseAddr+offset+count)))
    ∃ result finalMachine,
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames frame machine)
        (Storage.withCurrent frames result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals.size = 25 ∧ result.location = .mir ⟨8,4⟩ ∧
      result.locals[17]? = some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]? = some ⟨.live (.immediate (.scalar advanced)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[24]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ i, i < 16 ∨ 24 < i → result.locals[i]? = frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory = machine.memory ∧ finalMachine.borrowTracker = machine.borrowTracker ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      RootCurrentAddCallExact.Preserves options remaining span machine finalMachine thread := by
  obtain ⟨middle, nextMachine, addTrace, bodyEq,idEq,fnEq,extraEq,placeEq,contEq,vaEq,localsEq,trackEq,
    sz,pc,h17,h18,h19,h21,h22,h23,kept,direct,memEq,trackerEq,addressesEq,finalGhost,finalShallow,machineFields⟩ :=
    RootCurrentAddPipelineExact.from_bb7 options limits remaining span debugOff fuel validationFuel statementFuel frames frame machine pointer count
      temp16 size live15 cache15 live16 live2 cache2 unused body identity callee location noClocks tracker tracked mode ghost shallow all
      id tag baseAddr offset allocation pointerEq address present positive fits bounded noRace trackNone thread active top relevant
      budget budgetEq backend unchecked noGc fixed source outerRank innerRank
  have slot2 : middle.locals[2]? = frame.locals[2]? := kept 2 (by omega)
  have original2 : frame.locals[2]? =
      some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))), some RootCompilerFacts.usizeLayout⟩ := by
    rw [getElem?_pos frame.locals 2 (by omega)]
    congr 1
    cases observed : frame.locals[2] with
    | mk value layout =>
      rw [observed] at live2 cache2
      simp only at live2 cache2
      rw [live2,cache2]
  have at2 := (Array.getElem?_eq_some_iff.mp (slot2.trans original2)).2
  have at22 := (Array.getElem?_eq_some_iff.mp h22).2
  have at23 := (Array.getElem?_eq_some_iff.mp h23).2
  have at24 := (Array.getElem?_eq_some_iff.mp ((kept 24 (by omega)).trans dead24)).2
  obtain ⟨result, preparedTrace, prepared⟩ :=
    RootCopyPreparation.executes options limits remaining span debugOff fuel validationFuel frames middle nextMachine count
      (.scalar pointer) (.scalar (.fromScalarInt (.ofUInt64 count))) sz
      (by rw [at2]) (by rw [at2]) (by rw [at22]) (by rw [at23]) (by rw [at24]) (by rw [at24])
      (bodyEq.trans body) (idEq.trans identity) (fnEq.trans callee) pc (by rw [extraEq]; exact noClocks)
      tracker (trackerEq.trans tracked) mode finalGhost finalShallow
  exact ⟨result,nextMachine,SuccessfulTrace.append addTrace preparedTrace,
    prepared.body.trans bodyEq,prepared.identity.trans idEq,prepared.callee.trans fnEq,prepared.extra.trans extraEq,
    prepared.destination.trans placeEq,prepared.continuation.trans contEq,prepared.varargs.trans vaEq,
    prepared.localsIdentity.trans localsEq,prepared.trackedCaller.trans trackEq,prepared.size,prepared.location,
    (prepared.kept 17 (by decide) (by decide) (by decide)).trans h17,
    (prepared.kept 18 (by decide) (by decide) (by decide)).trans h18,
    (prepared.kept 19 (by decide) (by decide) (by decide)).trans h19,
    (prepared.kept 21 (by decide) (by decide) (by decide)).trans h21,
    prepared.count,(fun i outside => (prepared.kept i (by omega) (by omega) (by omega)).trans (kept i (by omega))),
    prepared.immediate direct,memEq,trackerEq,addressesEq,finalGhost,finalShallow,machineFields⟩

#print axioms from_bb7
end DuplicatePrefix.RootCurrentCopyReadyExact

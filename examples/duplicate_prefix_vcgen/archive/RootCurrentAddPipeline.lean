import duplicate_prefix.RootAddPreparation
import duplicate_prefix.RootCurrentAddCall

namespace DuplicatePrefix.RootCurrentAddPipeline
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

structure Prepared (before frame : CompilerFrameContext.ActualFrame)
    (pointer : Scalar Provenance) (count : UInt64) : Prop where
  body : frame.body = before.body
  identity : frame.bodyIdentity = before.bodyIdentity
  callee : frame.functionInstance = before.functionInstance
  extra : frame.extra = before.extra
  place : frame.returnPlace = before.returnPlace
  continuation : frame.returnContinuation = before.returnContinuation
  varargs : frame.vaList = before.vaList
  localsIdentity : frame.localsIdentity = before.localsIdentity
  track : frame.trackCallerArg = before.trackCallerArg
  size : frame.locals.size = 25
  location : frame.location = .mir ⟨7,13⟩
  unit17 : frame.locals[17]? = some ⟨.live (.immediate .uninit),none⟩
  unit18 : frame.locals[18]? = some ⟨.live (.immediate .uninit),none⟩
  sourcePointer : frame.locals[19]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩
  destination : frame.locals[21]? = some ⟨.live (.immediate .uninit),none⟩
  pointerArg : frame.locals[22]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩
  countArg : frame.locals[23]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  unchanged : ∀ i, i < 16 ∨ 23 < i → frame.locals[i]? = before.locals[i]?
  direct : CopyHelperCleanup.AllImmediate frame

/-- From the actual returned as_mut_ptr destination at the root, prepare the
arguments, execute the emitted ptr.add call, and return at root bb8.0. -/
theorem from_bb7
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationFuel : options.limits.validation=fuel+1)
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
    (guard : ∀ (prepared : CompilerFrameContext.ActualFrame) (valid : 21 < prepared.locals.size),
      Prepared frame prepared pointer count →
      Nonempty (PointerAddGuardBoundary.Reaches options limits remaining span frames
        (AddUncachedCall.cachedCaller prepared valid)
        (RootCurrentAddCall.entered options remaining span frames prepared machine valid noRace pointer count)
        (RootCurrentAddCall.enteredMachine options remaining span machine) pointer count)) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let advanced : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (baseAddr+offset+count)))
    ∃ result finalMachine,
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames frame machine)
        (Storage.withCurrent frames result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals.size = 25 ∧ result.location = .mir ⟨8,0⟩ ∧
      result.locals[17]? = some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]? = some ⟨.live (.immediate (.scalar advanced)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[22]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[23]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ i, i < 16 ∨ 23 < i → result.locals[i]? = frame.locals[i]?) ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory = machine.memory ∧ finalMachine.borrowTracker = machine.borrowTracker ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let advanced : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
    (Pointer.new (.concrete id tag) (Size.ofBytes (baseAddr+offset+count)))
  obtain ⟨pre, prepTrace, hBody,hId,hFn,hExtra,hPlace,hCont,hVa,hLocalsId,hTrack,hSize,hPC,h17,h18,h19,h21,h22,h23,hSame,hDirect⟩ :=
    RootAddPreparation.executes_tracked options limits remaining span debugOff fuel validationFuel
      frames frame machine pointer count temp16 size live15 cache15 live16 live2 cache2 unused body identity callee
      location noClocks tracker tracked mode ghost shallow all
  let shape : Prepared frame pre pointer count :=
    ⟨hBody,hId,hFn,hExtra,hPlace,hCont,hVa,hLocalsId,hTrack,hSize,hPC,h17,h18,h19,h21,h22,h23,hSame,hDirect⟩
  have valid : (21 : MIR.LocalId) < pre.locals.size := by rw [hSize]; decide
  have at21 := (Array.getElem?_eq_some_iff.mp h21).2
  have at22 := (Array.getElem?_eq_some_iff.mp h22).2
  have at23 := (Array.getElem?_eq_some_iff.mp h23).2
  have b22 : 22 < pre.locals.size := by rw [hSize]; decide
  have b23 : 23 < pre.locals.size := by rw [hSize]; decide
  obtain ⟨reached⟩ := guard pre valid shape
  obtain ⟨_, finalMachine, _, memoryEq, trackerEq, addressEq, finalGhost, finalShallow, afterCall⟩ :=
    RootCurrentAddCall.from_call options limits remaining span debugOff frames pre machine tracker tracked
      pointer count valid (by rw [at21]) (by rw [at21]) (by rw [hExtra]; exact noClocks) noRace
      (hBody.trans body) (hId.trans identity) (hFn.trans callee) (hTrack.trans trackNone)
      (by exact hPC) fuel validationFuel ghost shallow thread active top (by rw [hExtra]; exact relevant)
      budget budgetEq backend unchecked noGc fixed source b22 b23 (by rw [at22]) (by rw [at22])
      (by rw [at23]) (by rw [at23])
      id tag baseAddr offset allocation pointerEq address present positive fits bounded mode reached
  let current := AddUncachedCall.cachedCaller pre valid
  have currentValid : (21 : MIR.LocalId) < current.locals.size := by
    simpa [current, AddUncachedCall.cachedCaller, LocalPlaces.cachePlaceLayout] using valid
  let result := {PointerAddCurrentReturn.writeFrame current 21 (.scalar advanced) currentValid with location := .mir ⟨8,0⟩}
  have same (i : Nat) (not21 : i ≠ 21) : result.locals[i]? = pre.locals[i]? := by
    simp [result,current,PointerAddCurrentReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,
      Array.getElem?_set,Ne.symm not21]
  have r21 : result.locals[21]? = some ⟨.live (.immediate (.scalar advanced)),some CopyCompilerFacts.destPointerLayout⟩ := by
    simp [result,current,PointerAddCurrentReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have cachedDirect : CopyHelperCleanup.AllImmediate current :=
    CopyHelperCleanup.all_immediate_cache pre 21 CopyCompilerFacts.destPointerLayout valid hDirect
  have resultDirect : CopyHelperCleanup.AllImmediate result :=
    CopyHelperCleanup.all_immediate_set current 21 _ currentValid cachedDirect (by intro memory; simp)
  have resultSize : result.locals.size = 25 := by
    simp [result,current,PointerAddCurrentReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,hSize]
  exact ⟨result,finalMachine,SuccessfulTrace.append prepTrace afterCall,
    hBody,hId,hFn,hExtra,hPlace,hCont,hVa,hLocalsId,hTrack,resultSize,rfl,
    (same 17 (by decide)).trans h17,(same 18 (by decide)).trans h18,(same 19 (by decide)).trans h19,r21,
    (same 22 (by decide)).trans h22,(same 23 (by decide)).trans h23,
    fun i h => (same i (by omega)).trans (hSame i h),resultDirect,memoryEq,trackerEq,addressEq,finalGhost,finalShallow⟩

#print axioms from_bb7
end DuplicatePrefix.RootCurrentAddPipeline

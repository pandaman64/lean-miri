import duplicate_prefix.RootCurrentCopyReadyExact
import duplicate_prefix.CopyRootPositiveRoundtripExact

namespace DuplicatePrefix.RootPositiveCopyFromBB7
open Miri Miri.ABI Miri.MIR Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.Concurrency Miri.DataStructures
open PreparedArguments SourceDomain CopyRootPositiveRoundtrip
set_option maxRecDepth 65536
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false

/-- The accepted positive branch resumes in the real root after the copy.
Its original cached scheduler context, exclusive source grant, and computed
allocation updates account for both nested guard scopes. -/
theorem completes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (incoming : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      before (Storage.withCurrent frames frame machine))
    (length count base : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent frames frame machine) length)
    (rights : ExclusiveRegion (Storage.withCurrent frames frame machine) length storage tag)
    (positive : 0 < count.toNat) (countFits : count.toNat < 2^63)
    (disjoint : count.toNat + count.toNat ≤ length.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id,base⟩)
    (size : frame.locals.size = 25)
    (pointerSlot : frame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes)))))),
      some CopyCompilerFacts.destPointerLayout⟩)
    (temp16 : Immediate Provenance)
    (live16 : (frame.locals[16]'(by omega)).value = .live (.immediate temp16))
    (countSlot : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (unused : ∀i(v:i<frame.locals.size),17≤i→i≤23→(frame.locals[i]'v)=⟨.dead,none⟩)
    (unused24 : frame.locals[24]? = some ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,0⟩) (noClocks : frame.extra.dataRace = none)
    (mode : rights.tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (all : CopyHelperCleanup.AllImmediate frame) (noRace : machine.dataRace = none)
    (trackNone : frame.trackCallerArg = none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size) (relevant : frame.extra.userRelevance > 0)
    (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (source : PreparedContracts.SourceComparator)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (maskLen : storage.entry.allocation.initializationMask.len = storage.entry.allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed storage.entry.allocation.initializationMask)
    (initialized : InitMaskCopy.InitializedOn storage.entry.allocation.initializationMask storage.relativeStart
      (Size.ofBytes (storage.relativeStart.bytes+count)))
    (provenance : ProvenanceCopy.WellFormed storage.entry.allocation.provenanceMap storage.entry.allocation.len)
    (storageFits : storage.entry.allocation.len+64 < 18446744073709551616)
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (rangeCapacity : storage.relativeStart.bytes.toNat+length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) =
      some (storage.id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) storage.id)})) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let offset := storage.relativeStart.bytes
    let pointer := fromPtr options remaining span storage.id tag (base+offset)
    let advanced := fromPtr options remaining span storage.id tag (base+(offset+count))
    let readAccess := storage.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes count) .Read rights.tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write rights.tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ result finalMachine allocation,
      SuccessfulTrace.Trace cfg limits before (Storage.withCurrent frames result finalMachine) ∧
      result.location = .mir ⟨9,0⟩ ∧ result.locals.size = 25 ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals[17]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[18]? = some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ ∧
      result.locals[19]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]? = some ⟨.live (.immediate (.scalar advanced)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[24]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ i, i < 16 ∨ 24 < i → result.locals[i]? = frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate result ∧
      finalMachine.borrowTracker = machine.borrowTracker ∧ finalMachine.dataRace = none ∧ finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.user.payload.payload.user.backend = .none ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      finalMachine.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl finalMachine.user).gcInterval = 0 ∧
      (∃ thread, finalMachine.threads.activeThread? = some thread) ∧
      (∀ unrelated, unrelated ≠ storage.id → finalMachine.memory.live[unrelated]? = machine.memory.live[unrelated]?) ∧
      finalMachine.memory.live[storage.id]? = some ⟨storage.entry.kind,allocation⟩ ∧
      allocation.byteSize = storage.entry.allocation.byteSize ∧ allocation.len = storage.entry.allocation.len ∧
      allocation.extra = writeAccess.tree ∧
      AllocationCopy.snapshot allocation =
        (AllocationCopy.snapshot storage.entry.allocation).extract 0 (offset+count).toNat ++
        (AllocationCopy.snapshot storage.entry.allocation).extract offset.toNat (offset+count).toNat ++
        (AllocationCopy.snapshot storage.entry.allocation).extract (offset+count+count).toNat storage.entry.allocation.len := by
  let offset := storage.relativeStart.bytes
  let pointer := fromPtr options remaining span storage.id tag (base+offset)
  let advanced := fromPtr options remaining span storage.id tag (base+(offset+count))
  have at15 := (Array.getElem?_eq_some_iff.mp pointerSlot).2
  have at2 := (Array.getElem?_eq_some_iff.mp countSlot).2
  have bound : offset.toNat+count.toNat ≤ storage.entry.allocation.byteSize.bytes.toNat :=
    Nat.le_trans (Nat.add_le_add_left (by omega) _) storage.fits
  obtain ⟨prepared,firstMachine,prepTrace,b,id,f,e,r,c,a,locId,track,sz,pc,h17,h18,h19,h21,h24,kept,direct,memEq,
      trackedEq,addrEq,ghost1,shallow1,profile⟩ :=
    RootCurrentCopyReadyExact.from_bb7 options limits remaining span debug fuel validation statementFuel frames frame machine
      pointer count temp16 size (by rw [at15] <;> rfl) (by rw [at15]) live16 (by rw [at2]) (by rw [at2]) unused body identity callee location
      noClocks rights.tracker rights.tracked mode ghost shallow all storage.id tag base offset storage.entry rfl address storage.live
      positive countFits bound noRace trackNone thread active top relevant budget dispatch backend unchecked noGc fixed source
      outerRank innerRank unused24
  have advancedEq : fromPtr options remaining span storage.id tag (base+offset+count) = advanced := by
    unfold advanced
    rw [UInt64.add_assoc]
  have valid18 : 18 < prepared.locals.size := by rw [sz]; decide
  have h18' := (Array.getElem?_eq_some_iff.mp h18).2
  have h19' := (Array.getElem?_eq_some_iff.mp h19).2
  have h21a : prepared.locals[21]? = some ⟨.live (.immediate (.scalar advanced)),some CopyCompilerFacts.destPointerLayout⟩ := by
    rw [← advancedEq]
    exact h21
  have h21' := (Array.getElem?_eq_some_iff.mp h21a).2
  have h24' := (Array.getElem?_eq_some_iff.mp h24).2
  let copyInput : CopyRootEntry.Input options limits remaining span frames prepared firstMachine pointer advanced count :=
    { debug := debug
      tracker := rights.tracker
      tracked := trackedEq.trans rights.tracked
      valid := valid18
      old := .uninit
      live := by rw [h18']
      uncached := by rw [h18']
      noClocks := by rw [e];exact noClocks
      noRace := profile.race.trans noRace
      body := b.trans body
      identity := id.trans identity
      callee := f.trans callee
      trackNone := track.trans trackNone
      location := pc
      fuel := fuel
      validationFuel := validation
      ghost := ghost1
      shallow := shallow1
      thread := thread
      active := profile.active
      top := top
      relevant := by rw [e];exact relevant
      budget := budget
      budgetEq := dispatch
      backend := profile.backend.trans backend
      unchecked := profile.unchecked
      noGc := profile.noGc
      fixed := profile.fixed
      source := source
      valid19 := by rw [sz];decide
      valid21 := by rw [sz];decide
      valid24 := by rw [sz];decide
      live19 := by rw [h19']
      cache19 := by rw [h19']
      live21 := by rw [h21']
      cache21 := by rw [h21']
      live24 := by rw [h24']
      cache24 := by rw [h24'] }
  let owned : InitializedRegion (Storage.withCurrent frames prepared firstMachine) length :=
    CopyOwnershipTransport.storageAfter storage memEq
  let trusted : ExclusiveRegion (Storage.withCurrent frames prepared firstMachine) length owned tag :=
    CopyOwnershipTransport.rightsAfter rights memEq trackedEq
  obtain ⟨allocation,finalMachine,bTrack,dr,addr,g,v,be,ex,fix,arithmetic,gc,threadAfter,untouched,copyTrace,entry,sized,len,tree,snapshot⟩ :=
    CopyRootPositiveRoundtripExact.complete options limits remaining span frames prepared firstMachine length count base tag owned trusted
      copyInput statementFuel mode (UInt64.lt_iff_toNat_lt.mpr positive) disjoint maskLen maskValid initialized provenance storageFits
      root roots rangeCapacity bounded (by rw [addrEq];exact address) (by rw [profile.extras];exact extras)
  let current := CopyUncachedCall.cachedCaller prepared valid18
  have valid : 18 < current.locals.size := by simpa [current,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid18
  let result := {PointerAddCurrentReturn.writeFrame current 18 .uninit valid with location := .mir ⟨9,0⟩}
  have same (i : Nat) (not18 : i ≠ 18) : result.locals[i]? = prepared.locals[i]? := by
    simp [result,PointerAddCurrentReturn.writeFrame,current,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Ne.symm not18]
  have unit : result.locals[18]? = some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ := by
    simp [result,PointerAddCurrentReturn.writeFrame,current,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have resultSize : result.locals.size = 25 := by
    simpa [result,PointerAddCurrentReturn.writeFrame,current,CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using sz
  have copiedDirect : CopyHelperCleanup.AllImmediate result :=
    CopyHelperCleanup.all_immediate_set current 18 _ valid
      (CopyHelperCleanup.all_immediate_cache prepared 18 CopyHelperUnit.layout valid18 direct) (by intro mem; simp)
  have distinct (id : AllocId) (h : id ≠ storage.id) : finalMachine.memory.live[id]? = machine.memory.live[id]? := by
    exact (untouched id h).trans (by rw [memEq])
  exact ⟨result,finalMachine,allocation,
    SuccessfulTrace.append incoming (SuccessfulTrace.append prepTrace copyTrace),
    rfl,resultSize,b,id,f,e,r,c,a,locId,track,(same 17 (by decide)).trans h17,unit,(same 19 (by decide)).trans h19,
    (same 21 (by decide)).trans h21a,(same 24 (by decide)).trans h24,
    (fun i h => (same i (by omega)).trans (kept i h)),copiedDirect,
    bTrack.trans trackedEq,dr.trans (profile.race.trans noRace),addr.trans addrEq,g.trans ghost1,v.trans shallow1,
    be.trans (profile.backend.trans backend),ex.trans profile.extras,fix.trans profile.fixed,arithmetic,gc,threadAfter,
    distinct,entry,sized,len,tree,snapshot⟩

end DuplicatePrefix.RootPositiveCopyFromBB7

#print axioms DuplicatePrefix.RootPositiveCopyFromBB7.completes

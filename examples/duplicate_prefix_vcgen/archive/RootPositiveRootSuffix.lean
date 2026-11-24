import duplicate_prefix.RootPositiveCopyFromBB7
import duplicate_prefix.CopyRootPositiveRoundtripExact
import duplicate_prefix.RootPositiveReturnContinuation
import duplicate_prefix.InitializedRegionPrefix

namespace DuplicatePrefix.RootPositiveRootSuffix
open Miri Miri.ABI Miri.MIR Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.Concurrency Miri.DataStructures
open PreparedArguments SourceDomain CopyRootPositiveRoundtrip
set_option maxRecDepth 65536
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false

structure ReadyAfterCopy
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length count base : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent frames frame machine) length)
    (rights : ExclusiveRegion (Storage.withCurrent frames frame machine) length storage tag)
    (result : CompilerFrameContext.ActualFrame) (last : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (allocation : Allocation Provenance BorrowTree) : Prop where
  body : result.body = frame.body
  extra : result.extra = frame.extra
  returnPlace : result.returnPlace = frame.returnPlace
  returnContinuation : result.returnContinuation = frame.returnContinuation
  varargs : result.vaList = frame.vaList
  direct : CopyHelperCleanup.AllImmediate result
  tracker : last.borrowTracker = some rights.tracker
  race : last.dataRace = none
  addresses : last.user.addresses = machine.user.addresses
  ghost : last.user.payload.ghost = false
  shallow : last.user.payload.validation = .Shallow
  backend : last.user.payload.payload.user.backend = .none
  backing : last.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras
  fixed : last.threads.fixedScheduling = true
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl last.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl last.user).gcInterval = 0
  active : ∃ thread, last.threads.activeThread? = some thread
  disjoint : ∀ id, id ≠ storage.id → last.memory.live[id]? = machine.memory.live[id]?
  present : last.memory.live[storage.id]? = some ⟨storage.entry.kind,allocation⟩
  sized : allocation.byteSize = storage.entry.allocation.byteSize
  len : allocation.len = storage.entry.allocation.len
  copiedTree : let offset := storage.relativeStart.bytes
    let read := storage.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes count) .Read rights.tracker.global.protectedTags .VisitChildrenOfAccessed
    allocation.extra = (read.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write rights.tracker.global.protectedTags .VisitChildrenOfAccessed).tree
  storageValid : CopyProvenanceBounds.AllocationBacking allocation
  copiedBytes : let offset := storage.relativeStart.bytes
    AllocationCopy.snapshot allocation =
      (AllocationCopy.snapshot storage.entry.allocation).extract 0 (offset+count).toNat ++
      (AllocationCopy.snapshot storage.entry.allocation).extract offset.toNat (offset+count).toNat ++
      (AllocationCopy.snapshot storage.entry.allocation).extract (offset+count+count).toNat storage.entry.allocation.len

theorem runs_to_return
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
    (provenance : ProvenanceCopy.WellFormed storage.entry.allocation.provenanceMap storage.entry.allocation.len)
    (storageFits : storage.entry.allocation.len+64 < 18446744073709551616)
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (rangeCapacity : storage.relativeStart.bytes.toNat+length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) =
      some (storage.id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) storage.id)}))
    (zeroSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (post : MachineHooks.State MiriMemoryKind Machine.RootUser → Prop)
    (finish : ∀ result last allocation,
      ReadyAfterCopy options remaining span frames frame machine length count base tag storage rights
        result last allocation →
      ∀ done : CompilerFrameContext.ActualFrame,
        RootSuccessCleanupFacts.Shape result done RootCompilerFacts.boolLayout (.scalar (.fromBool true)) →
        let cfg := PreparedContracts.actualConfig options () (remaining+1) span
        let start := Storage.withCurrent frames {done with location := .mir ⟨10,0⟩}
          (SourceControl.accounted cfg.terminators (Storage.withCurrent frames done last)).machine
        ∃ final, ExecutionMachine.step cfg limits () start = (final,.ok true) ∧ post final) :
    ∃ final, SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits before final ∧
      post final := by
  have nonempty : length ≠ 0 := by
    intro empty
    subst length
    simp at disjoint
    omega
  have initialized := InitializedRegionPrefix.initialized length count storage nonempty (by omega) maskLen storageFits
  obtain ⟨result,last,allocation,trace,location9,size9,body9,identity9,callee9,extra,place,continuation,varargs,localsId,trackedCaller,
    a17,a18,a19,a21,a24,kept,direct,borrows,race,addresses,ghost9,shallow9,backend9,extras9,fixed9,arith,gc,active9,untouched,
    present,allocationSize,allocationLen,tree,allocationBacking,snapshot⟩ :=
    RootPositiveCopyFromBB7.completes options limits remaining span debug fuel validation statementFuel frames frame before machine incoming
      length count base tag storage rights positive countFits disjoint address size pointerSlot temp16 live16 countSlot
      unused unused24 body identity callee location noClocks mode ghost shallow all noRace trackNone thread active top relevant
      budget dispatch backend unchecked noGc fixed source outerRank innerRank maskLen maskValid initialized provenance storageFits root roots
      rangeCapacity bounded extras
  have stays0 : result.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ :=
    (kept 0 (.inl (by decide))).trans zeroSlot
  have stays15 := (kept 15 (.inl (by decide))).trans pointerSlot
  have tracked9 : last.borrowTracker = some rights.tracker := borrows.trans rights.tracked
  exact RootPositiveReturnContinuation.completes options limits remaining span source debug fuel validation frames result last size9
    _ _ _ _ _ stays0 stays15 a17 a18 a19 a21 a24 (body9.trans body) (identity9.trans identity) (callee9.trans callee) location9
    (by rw [extra]; exact noClocks) rights.tracker tracked9 mode ghost9 shallow9 arith gc fixed9 before trace post
    (finish result last allocation ⟨body9,extra,place,continuation,varargs,direct,tracked9,race,addresses,ghost9,shallow9,backend9,extras9,
      fixed9,arith,gc,active9,untouched,present,allocationSize,allocationLen,tree,allocationBacking,snapshot⟩)

#print axioms runs_to_return
end DuplicatePrefix.RootPositiveRootSuffix

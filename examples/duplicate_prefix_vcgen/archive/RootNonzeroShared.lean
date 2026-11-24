import duplicate_prefix.RootNonzeroEntry
import duplicate_prefix.RootSharedComplete
import duplicate_prefix.UnprotectedSharedRights

namespace DuplicatePrefix.RootNonzeroEntry
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures
open Miri.TreeBorrows.Tree
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild
open RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual nonzero root prefix reaches the emitted Len call, with its
earlier holder's writable scope intact after the shared Ref. -/
theorem reachesLenCallWithSlots
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64) (positive : n ≠ 0)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (uncached3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : ZeroImmediateFacts.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (sizing : options.place.dynamicFuel = sizeFuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut) (raceOff : machine.dataRace = none)
    (positiveLen : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).entries.any
      (·.value.ty == 2) = false)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes)
    (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tracker.global.nextPointerTag = none)
    (nodeFresh : ∀ index data, entry.allocation.extra.nodeAt index = some data → data.tag ≠ tracker.global.nextPointerTag)
    (unheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : VacantRows entry.allocation.extra)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (extent : MaterializedWithin entry.allocation.extra parent offset (offset+len))
    (sourceSlot : frame.locals[1]? = some ⟨.live (.immediate (.scalarPair
      (.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len)))), some RootCompilerFacts.sliceLayout⟩) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let tag := tracker.global.nextPointerTag
    let freshValue : Immediate Provenance := .scalarPair
      (.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len))
    let initialTree := entry.allocation.extra
    let read := initialTree.performNormalAccessRange parentTag (Size.ofBytes offset) (Size.ofBytes len) .Read
      tracker.global.protectedTags .VisitChildrenOfAccessed
    let inside := DedupRangeMap.new (Size.ofBytes len) sharedState
    let resultTree := (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag inside .Frozen false).tree
    ∃ result after,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent older frame machine) (Storage.withCurrent older result after) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.trackCallerArg = frame.trackCallerArg ∧ result.locals.size = 25 ∧ result.location = .mir ⟨2,12⟩ ∧
      result.locals[0]? = frame.locals[0]? ∧
      result.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]? = some ⟨.live (.immediate freshValue),some RootSharedStep.sharedLayout⟩ ∧
      result.locals[13]? = frame.locals[13]? ∧ ZeroImmediateFacts.AllImmediate result ∧
      after = {tick options remaining span machine with memory := after.memory, borrowTracker := after.borrowTracker} ∧
      after.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra resultTree} ∧
      OwnedOn (fun row => LocationRights resultTree row tracker.global.protectedTags parent)
        offset (offset+len) resultTree.locations ∧
      MaterializedWithin resultTree parent offset (offset+len) ∧ VacantRows resultTree ∧
      (∃ child, resultTree.indexOfTag tag = some child ∧
        SharedChildFrame initialTree read.tree resultTree parent child tag (Size.ofBytes offset) (Size.ofBytes len) inside) ∧
      ∃ newTracker, after.borrowTracker = some newTracker ∧ newTracker.retagMode = .Default ∧
        newTracker.global.protectedTags = tracker.global.protectedTags ∧
        tracker.global.newPointerTag = .ok (newTracker.global, tag) ∧
        (CurrentSharedRetag.ReadGrant after entry id tag root offset len tracker.global.protectedTags ∧
          (∀ index, index < 3 ∨ 13 ≤ index → result.locals[index]? = frame.locals[index]?)) := by
  intro cfg tag freshValue initialTree read inside resultTree
  let next := tick options remaining span machine
  obtain ⟨middle, leading, bodyM, idM, calleeM, extraM, placeM, contM, vaM, layoutM, callerM, sizeM,
    locM, slot0, slot1, slot7, slot8, slot9, slot10, slot11, slot12, slot13, immediateM, retained⟩ :=
    reachesSharedReferenceWithSlots options limits remaining span source debugOff fuel fuelEq older frame machine body identity callee
      location size n positive unused dead3 uncached3 dead4 dead5 uncached4 uncached5 live2 cached2 noClocks all tracker tracked
      defaultMode ghost shallow unchecked noGc fixed
  have available (i : Nat) (valid : i < middle.locals.size) {slot : LocalState Provenance LocalLayout}
      (optional : middle.locals[i]? = some slot) : middle.locals[i] = slot :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans optional)
  have valid12 : 12 < middle.locals.size := by rw [sizeM]; decide
  have part1 := available 1 (by rw [sizeM]; decide) (slot1.trans sourceSlot)
  have part12 := available 12 valid12 slot12
  have addressesNext : next.user.addresses = machine.user.addresses := by
    unfold next tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have cachedNext : next.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [addressesNext]
    exact cached
  have arrayNext : EvalProjectionMachine.arrays.get (Storage.withCurrent older middle next) =
      EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine) := by
    unfold next tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have metadataNext : (EvalProjectionMachine.arrays.get (Storage.withCurrent older middle next)).metadata =
      PreparedReflection.actual.runtime := by rw [arrayNext]; exact metadata
  have aliasNext : (EvalProjectionMachine.arrays.get (Storage.withCurrent older middle next)).entries.any
      (·.value.ty == 2) = false := by rw [arrayNext]; exact noAlias
  obtain ⟨result, after, sharedStep, locationR, slot12R, grant, newTracker, newTracked, newMode, protections,
    frameEq, afterEq, footprint, nextTag⟩ :=
    RootSharedComplete.stepDetailed options limits remaining fuel sizeFuel span debugOff fuelEq sizing preciseOff implicitOff
      older middle next id parentTag parent root base offset len entry tracker tracked defaultMode fresh cachedNext live allocationMut
      raceOff ((congrArg (·.dataRace) extraM).trans noClocks) positiveLen bounded memoryBounds notNull cmp metadataNext aliasNext
      ((tick_ghost options remaining span machine).trans ghost) ((tick_shallow options remaining span machine).trans shallow)
      coherent parentNode parentStored roots parentFound depth rank tagFresh room aligned reuse clean bounds owners valid12
      (bodyM.trans body) (idM.trans identity) (calleeM.trans callee) locM (congrArg (·.layout) part1)
      (congrArg (·.value) part12) (congrArg (·.layout) part12) (congrArg (·.value) part1)
  obtain ⟨heap, writable, materialized, vacant, frameGrant⟩ :=
    footprint.retainsHolder after entry id parentTag tag parent root offset len tracker.global.protectedTags
      parentNode parentStored parentFound coherent roots bounds nodeFresh unheld owners extent clean
  have fields : result.body = middle.body ∧ result.bodyIdentity = middle.bodyIdentity ∧
      result.functionInstance = middle.functionInstance ∧ result.extra = middle.extra ∧
      result.returnPlace = middle.returnPlace ∧ result.returnContinuation = middle.returnContinuation ∧
      result.vaList = middle.vaList ∧ result.localsIdentity = middle.localsIdentity ∧
      result.trackCallerArg = middle.trackCallerArg ∧ result.locals.size = middle.locals.size := by
    rw [frameEq]
    simp
  obtain ⟨bodyR,idR,calleeR,extraR,placeR,contR,vaR,layoutR,callerR,sizeR⟩ := fields
  have other (index : Nat) (different : index ≠ 12) : result.locals[index]? = middle.locals[index]? := by
    rw [frameEq]
    simp [Ne.symm different]
  have immediateR : ZeroImmediateFacts.AllImmediate result := by
    rw [frameEq]
    intro slot member memory
    rcases Array.mem_or_eq_of_mem_set (w := valid12) member with old | rfl
    · exact immediateM slot old memory
    · simp
  refine ⟨result, after, SuccessfulTrace.append leading (.next sharedStep (.refl _)),
    bodyR.trans bodyM, idR.trans idM, calleeR.trans calleeM, extraR.trans extraM, placeR.trans placeM, contR.trans contM,
    vaR.trans vaM, layoutR.trans layoutM, callerR.trans callerM, sizeR.trans sizeM, locationR,
    (other 0 (by decide)).trans slot0, (other 7 (by decide)).trans slot7, (other 8 (by decide)).trans slot8,
    (other 9 (by decide)).trans slot9, (other 10 (by decide)).trans slot10, (other 11 (by decide)).trans slot11,
    slot12R, (other 13 (by decide)).trans slot13, immediateR, afterEq, heap, writable, materialized, vacant, frameGrant,
    newTracker, newTracked, newMode, protections, nextTag, grant, ?_⟩
  intro index untouched
  have distinct : index ≠ 12 := by omega
  exact (other index distinct).trans (retained index untouched)

theorem reachesLenCall
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64) (positive : n ≠ 0)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (uncached3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : ZeroImmediateFacts.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (sizing : options.place.dynamicFuel = sizeFuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut) (raceOff : machine.dataRace = none)
    (positiveLen : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).entries.any
      (·.value.ty == 2) = false)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes)
    (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tracker.global.nextPointerTag = none)
    (nodeFresh : ∀ index data, entry.allocation.extra.nodeAt index = some data → data.tag ≠ tracker.global.nextPointerTag)
    (unheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : VacantRows entry.allocation.extra)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (extent : MaterializedWithin entry.allocation.extra parent offset (offset+len))
    (sourceSlot : frame.locals[1]? = some ⟨.live (.immediate (.scalarPair
      (.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len)))), some RootCompilerFacts.sliceLayout⟩) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let tag := tracker.global.nextPointerTag
    let freshValue : Immediate Provenance := .scalarPair
      (.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len))
    let initialTree := entry.allocation.extra
    let read := initialTree.performNormalAccessRange parentTag (Size.ofBytes offset) (Size.ofBytes len) .Read
      tracker.global.protectedTags .VisitChildrenOfAccessed
    let inside := DedupRangeMap.new (Size.ofBytes len) sharedState
    let resultTree := (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag inside .Frozen false).tree
    ∃ result after,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent older frame machine) (Storage.withCurrent older result after) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.trackCallerArg = frame.trackCallerArg ∧ result.locals.size = 25 ∧ result.location = .mir ⟨2,12⟩ ∧
      result.locals[0]? = frame.locals[0]? ∧
      result.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]? = some ⟨.live (.immediate freshValue),some RootSharedStep.sharedLayout⟩ ∧
      result.locals[13]? = frame.locals[13]? ∧ ZeroImmediateFacts.AllImmediate result ∧
      after = {tick options remaining span machine with memory := after.memory, borrowTracker := after.borrowTracker} ∧
      after.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra resultTree} ∧
      OwnedOn (fun row => LocationRights resultTree row tracker.global.protectedTags parent)
        offset (offset+len) resultTree.locations ∧
      MaterializedWithin resultTree parent offset (offset+len) ∧ VacantRows resultTree ∧
      (∃ child, resultTree.indexOfTag tag = some child ∧
        SharedChildFrame initialTree read.tree resultTree parent child tag (Size.ofBytes offset) (Size.ofBytes len) inside) ∧
      ∃ newTracker, after.borrowTracker = some newTracker ∧ newTracker.retagMode = .Default ∧
        newTracker.global.protectedTags = tracker.global.protectedTags ∧
        tracker.global.newPointerTag = .ok (newTracker.global, tag) ∧
        CurrentSharedRetag.ReadGrant after entry id tag root offset len tracker.global.protectedTags := by
  intro cfg tag value initialTree read inside resultTree
  obtain ⟨result, after, trace, bodyR, identityR, calleeR, extra, place, continuation, va, localsId, track, sizeR, loc,
    slot0, slot7, slot8, slot9, slot10, slot11, slot12, slot13, immediate, afterShape, heap, writable, scope,
    vacant, footprint, newTracker, trackedNext, defaultNext, protectedNext, nextTag, grant, _⟩ :=
    reachesLenCallWithSlots options limits remaining sizeFuel span source debugOff fuel fuelEq older frame machine
      body identity callee location size n positive unused dead3 uncached3 dead4 dead5 uncached4 uncached5 live2 cached2
      noClocks all tracker tracked defaultMode ghost shallow unchecked noGc fixed sizing preciseOff implicitOff
      id parentTag parent root base offset len entry fresh cached live allocationMut raceOff positiveLen bounded memoryBounds
      notNull cmp metadata noAlias coherent parentNode parentStored roots parentFound depth rank tagFresh nodeFresh unheld
      room aligned reuse clean bounds owners extent sourceSlot
  exact ⟨result, after, trace, bodyR, identityR, calleeR, extra, place, continuation, va, localsId, track, sizeR, loc,
    slot0, slot7, slot8, slot9, slot10, slot11, slot12, slot13, immediate, afterShape, heap, writable, scope,
    vacant, footprint, newTracker, trackedNext, defaultNext, protectedNext, nextTag, grant⟩

#print axioms reachesLenCallWithSlots
#print axioms reachesLenCall
end DuplicatePrefix.RootNonzeroEntry

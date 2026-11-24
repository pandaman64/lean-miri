import duplicate_prefix.CurrentLenEntry
import duplicate_prefix.LenUncachedFrontend
import duplicate_prefix.PtrMetadataReturn
import duplicate_prefix.CurrentReferenceCore
import duplicate_prefix.LenInstall
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.ScopedFrame

namespace DuplicatePrefix.RootLenCurrentCall

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ArchiveForestProjection SourceDomain GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- The actual root bb2 terminator enters the length body using the
shared receiver read capability and the stock accounted call transition. -/
theorem stepWithFrame
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1) (sizing : options.place.dynamicFuel = sizeFuel+1)
    (debug : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (old : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some old)
    (fresh : old.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none) (localClocks : caller.extra.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any
      (·.value.ty == 2) = false)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag old.global.nextPointerTag = none)
    (freshNode : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ old.global.nextPointerTag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row old.global.protectedTags parent .Read)
      offset (offset+len) entry.allocation.extra.locations)
    (validDest : 11 < caller.locals.size) (oldDest : Immediate Provenance)
    (destLive : caller.locals[11].value = .live (.immediate oldDest))
    (destUncached : caller.locals[11].layout = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (LenUncachedFrontend.cachedCaller caller validDest) machine)
      (LocalPlaces.localRuntimePlace frames.size (LenUncachedFrontend.cachedCaller caller validDest) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (LenUncachedFrontend.cachedCaller caller validDest) machine)
      (LocalPlaces.localRuntimePlace frames.size (LenUncachedFrontend.cachedCaller caller validDest) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (validSource : 12 < caller.locals.size)
    (sourceCached : caller.locals[12].layout = some LenHelper.rawLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let value := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let newValue := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let cached := LenUncachedFrontend.cachedCaller caller validDest
    let destination := (LocalPlaces.localRuntimePlace frames.size cached 11 RootCompilerFacts.usizeLayout).stackView
    caller.locals[12].value = .live (.immediate value) →
    ∃ finalFrame finalMachine,
      ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller beforeMachine) =
        (Storage.withCurrent (frames.push cached) finalFrame finalMachine, .ok true) ∧
      finalFrame.body = LenHelper.body.body ∧ finalFrame.bodyIdentity = LenHelper.body.identity ∧
      finalFrame.functionInstance = LenHelper.resolved.callee ∧ finalFrame.location = .mir ⟨0,0⟩ ∧
      finalFrame.locals[1]? = some ⟨.live (.immediate newValue), some LenHelper.rawLayout⟩ ∧
      finalFrame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩ ∧
      finalFrame.locals[2]? = some ⟨.dead, none⟩ ∧ finalFrame.locals.size = 3 ∧
      finalFrame.extra.borrowTracker = some (({} : FrameState).addProtector id old.global.nextPointerTag) ∧
      finalFrame.returnPlace = destination ∧ finalFrame.returnContinuation = .goto (some 3) .Unreachable ∧
      finalFrame.extra.dataRace = none ∧ finalFrame.vaList = #[] ∧
      ∃ tracker, finalMachine.borrowTracker = some tracker ∧ tracker.retagMode = old.retagMode ∧
        tracker.global.protectedTags = old.global.protectedTags.insert old.global.nextPointerTag .StrongProtector ∧
        CurrentSharedRetag.ReadGrant finalMachine entry id old.global.nextPointerTag root offset len tracker.global.protectedTags ∧
        CurrentLenFnEntry.FrameGrant finalMachine entry id parentTag old.global.nextPointerTag parent offset len tracker.global.protectedTags ∧
        finalMachine = {(LenPush.completed options.userRelevantCrates (Storage.withCurrent frames cached machine)
          destination current).machine with memory := finalMachine.memory, borrowTracker := finalMachine.borrowTracker} := by
  intro cfg inner value newValue cachedCaller destination sourceLive
  have valid : 11 < cachedCaller.locals.size := by
    simpa [cachedCaller,LenUncachedFrontend.cachedCaller,LocalPlaces.cachePlaceLayout] using validDest
  have cachedDestLive : cachedCaller.locals[11].value = .live (.immediate oldDest) := by
    simpa [cachedCaller,LenUncachedFrontend.cachedCaller,LocalPlaces.cachePlaceLayout] using destLive
  have cachedDestLayout : cachedCaller.locals[11].layout = some RootCompilerFacts.usizeLayout := by
    simp [cachedCaller,LenUncachedFrontend.cachedCaller,LocalPlaces.cachePlaceLayout]
  obtain ⟨done, after, initialized, observations⟩ :=
    CurrentLenEntry.initWithFrame options limits remaining fuel sizeFuel span budget sizing debug preciseOff implicitOff
      frames cachedCaller machine id parentTag parent root base offset len entry old tracked fresh cached live
      allocationMut raceOff localClocks positive bounded memoryBounds notNull cmp metadata noAlias ghost shallow
      coherent parentNode parentStored roots parentFound depth rank tagFresh freshNode room aligned reuse clean bounds
      owners valid oldDest cachedDestLive cachedDestLayout thread index current active top present
  have called := LenUncachedFrontend.call_uncached_of_entry options limits (remaining+1) dispatch dispatchFuel
    span debug frames caller machine value sourceBody identity callee located source cmp validSource sourceLive
    sourceCached validDest destUncached localClocks raceOff backend ghost done after initialized
  let before := Storage.withCurrent frames caller beforeMachine
  let next := Storage.withCurrent frames caller machine
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have charged : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (next,.ok ()) := by
    simpa only [next,before,machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted,Storage.withCurrent,cfg] using accounting
  let block := RootBody.reflected.body.body.basicBlocks[2]'(by decide +kernel)
  have blockAt : caller.body.basicBlocks[2]? = some block := by rw [sourceBody]; simp [block]
  have noStatement : block.statements[12]? = none := by with_unfolding_all rfl
  refine ⟨done,after,?_,observations⟩
  apply GenericCallStages.source_step cfg limits () before next _ caller ⟨2,12⟩ block
    LenHelper.resolved.function #[LenEvaluateCall.argument] ⟨11,#[]⟩ (some 3) .Unreachable
    LenCallFrontend.sourceKind LenCallFrontend.fnSpan
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement
    LenCallFrontend.source_call charged called
  simp [Storage.withCurrent,next]

theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1) (sizing : options.place.dynamicFuel = sizeFuel+1)
    (debug : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (old : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some old)
    (fresh : old.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none) (localClocks : caller.extra.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any
      (·.value.ty == 2) = false)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag old.global.nextPointerTag = none)
    (freshNode : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ old.global.nextPointerTag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row old.global.protectedTags parent .Read)
      offset (offset+len) entry.allocation.extra.locations)
    (validDest : 11 < caller.locals.size) (oldDest : Immediate Provenance)
    (destLive : caller.locals[11].value = .live (.immediate oldDest))
    (destUncached : caller.locals[11].layout = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (LenUncachedFrontend.cachedCaller caller validDest) machine)
      (LocalPlaces.localRuntimePlace frames.size (LenUncachedFrontend.cachedCaller caller validDest) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (LenUncachedFrontend.cachedCaller caller validDest) machine)
      (LocalPlaces.localRuntimePlace frames.size (LenUncachedFrontend.cachedCaller caller validDest) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (validSource : 12 < caller.locals.size)
    (sourceCached : caller.locals[12].layout = some LenHelper.rawLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let value := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let newValue := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let cached := LenUncachedFrontend.cachedCaller caller validDest
    let destination := (LocalPlaces.localRuntimePlace frames.size cached 11 RootCompilerFacts.usizeLayout).stackView
    caller.locals[12].value = .live (.immediate value) →
    ∃ finalFrame finalMachine,
      ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller beforeMachine) =
        (Storage.withCurrent (frames.push cached) finalFrame finalMachine, .ok true) ∧
      finalFrame.body = LenHelper.body.body ∧ finalFrame.bodyIdentity = LenHelper.body.identity ∧
      finalFrame.functionInstance = LenHelper.resolved.callee ∧ finalFrame.location = .mir ⟨0,0⟩ ∧
      finalFrame.locals[1]? = some ⟨.live (.immediate newValue), some LenHelper.rawLayout⟩ ∧
      finalFrame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩ ∧
      finalFrame.locals[2]? = some ⟨.dead, none⟩ ∧ finalFrame.locals.size = 3 ∧
      finalFrame.extra.borrowTracker = some (({} : FrameState).addProtector id old.global.nextPointerTag) ∧
      finalFrame.returnPlace = destination ∧ finalFrame.returnContinuation = .goto (some 3) .Unreachable ∧
      ∃ tracker, finalMachine.borrowTracker = some tracker ∧ tracker.retagMode = old.retagMode ∧
        tracker.global.protectedTags = old.global.protectedTags.insert old.global.nextPointerTag .StrongProtector ∧
        CurrentSharedRetag.ReadGrant finalMachine entry id old.global.nextPointerTag root offset len tracker.global.protectedTags := by
  intro cfg inner value newValue cachedCaller destination sourceLive
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n, _, _, tracker, trackedAfter, mode, tags, grant, _, _⟩ := stepWithFrame
    options limits remaining fuel sizeFuel span budget sizing debug preciseOff implicitOff frames
    caller machine id parentTag parent root base offset len entry old tracked fresh cached live
    allocationMut raceOff localClocks positive bounded memoryBounds notNull cmp metadata noAlias
    ghost shallow coherent parentNode parentStored roots parentFound depth rank tagFresh freshNode
    room aligned reuse clean bounds owners validDest oldDest destLive destUncached thread index
    current active top present sourceBody identity callee located source validSource sourceCached
    backend dispatch dispatchFuel beforeMachine machineEq unchecked noGc fixed sourceLive
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n, tracker, trackedAfter, mode, tags, grant⟩

#print axioms stepWithFrame
#print axioms step
end DuplicatePrefix.RootLenCurrentCall

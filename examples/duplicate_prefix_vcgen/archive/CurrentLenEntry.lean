import duplicate_prefix.CurrentLenArgument
import duplicate_prefix.LenEntry
import duplicate_prefix.CurrentReferenceCore
import duplicate_prefix.LenInstall
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.ScopedFrame

namespace DuplicatePrefix.CurrentLenEntry

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ArchiveForestProjection SourceDomain GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- Prepare the real length frame and install its shared receiver and
strong protector, including the selected callee's normal entry location. -/
theorem initWithFrame
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
    (validDest : 11 < caller.locals.size)
    (oldDest : Immediate Provenance) (destLive : caller.locals[11].value = .live (.immediate oldDest))
    (destCached : caller.locals[11].layout = some RootCompilerFacts.usizeLayout)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let value := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let newValue := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let destination := (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView
    ∃ finalFrame finalMachine,
      Call.initStackFrame (ExecutionMachine.callHooks cfg limits) () LenHelper.resolved.callee LenHelper.body LenHelper.abi
        #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩] false destination (.goto (some 3) .Unreachable)
        (Storage.withCurrent frames caller machine) = .ok () (Storage.withCurrent (frames.push caller) finalFrame finalMachine) ∧
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
        finalMachine = {(LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
          destination current).machine with memory := finalMachine.memory, borrowTracker := finalMachine.borrowTracker} := by
  intro cfg inner value newValue destination
  let state := Storage.withCurrent frames caller machine
  let raw := LenEntry.rawFrame options state destination
  let pushed := (LenPush.completed options.userRelevantCrates state destination current).machine
  have rawSize : raw.locals.size = 3 := LenEntry.raw_size options state destination
  have valid : 1 < raw.locals.size := by rw [rawSize]; decide
  have frameBody : raw.body = LenHelper.body.body := rfl
  have identity : raw.bodyIdentity = LenHelper.body.identity := rfl
  have callee : raw.functionInstance = LenHelper.resolved.callee := rfl
  have dead : raw.locals[1].value = .dead := by with_unfolding_all rfl
  have uncached : raw.locals[1].layout = none := by with_unfolding_all rfl
  have rawRace : raw.extra.dataRace = none := by
    simp [raw, LenEntry.rawFrame, LenFrame.rawFrame, LenPush.fresh, CallEntryFacts.freshRoot, state, Storage.withCurrent, raceOff]
  have rawLedger : raw.extra.borrowTracker = some ({} : FrameState) := by
    simp [raw, LenEntry.rawFrame, LenFrame.rawFrame, LenPush.fresh, CallEntryFacts.freshRoot, state, Storage.withCurrent, tracked]
  have pushFrame : pushed = {(LenPush.fresh machine).1 with threads := pushed.threads} := by
    unfold pushed LenPush.completed
    simp only [state, Storage.withCurrent]
    unfold GenericPushRelevance.afterPush
    split <;> rfl
  have postMetadata : (EvalProjectionMachine.arrays.get
      (Storage.withCurrent (frames.push caller) raw pushed)).metadata = PreparedReflection.actual.runtime := by
    rw [pushFrame]
    exact metadata
  have postNoAlias : (EvalProjectionMachine.arrays.get
      (Storage.withCurrent (frames.push caller) raw pushed)).entries.any (·.value.ty == 2) = false := by
    rw [pushFrame]
    exact noAlias
  have trackedPushed : pushed.borrowTracker = some old := by rw [pushFrame]; exact tracked
  have cachedPushed : pushed.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩ := by rw [pushFrame]; exact cached
  have livePushed : pushed.memory.live[id]? = some entry := by rw [pushFrame]; exact live
  have racePushed : pushed.dataRace = none := by rw [pushFrame]; exact raceOff
  have ghostPushed : pushed.user.payload.ghost = false := by rw [pushFrame]; exact ghost
  have shallowPushed : pushed.user.payload.validation = .Shallow := by rw [pushFrame]; exact shallow
  obtain ⟨installed, after, installedArg, ledger, slot, b, i, c, returned, continuation, vaList, localsId,
    count, noRace, other, tracker, afterTracked, mode, protections, read, receiverFrame, machineFrame⟩ :=
    CurrentLenArgument.installWithFrame options limits remaining fuel sizeFuel span budget sizing debug preciseOff implicitOff
      (frames.push caller) raw pushed id parentTag parent root base offset len entry old trackedPushed fresh cachedPushed
      livePushed allocationMut racePushed rawRace positive bounded memoryBounds notNull cmp postMetadata postNoAlias
      ghostPushed shallowPushed coherent parentNode parentStored roots parentFound depth rank tagFresh freshNode room aligned reuse
      clean bounds owners valid frameBody identity callee dead uncached {} rawLedger
  have afterSize : installed.locals.size = 3 := count.trans rawSize
  have valid0 : 0 < installed.locals.size := by rw [afterSize]; decide
  have untouched0 : installed.locals[0]? = some ⟨.dead,none⟩ := (other 0 (by decide)).trans (by with_unfolding_all rfl)
  have untouched2 : installed.locals[2]? = some ⟨.dead,none⟩ := (other 2 (by decide)).trans (by with_unfolding_all rfl)
  have dead0 : installed.locals[0].value = .dead := by
    have slot0 := Option.some.inj ((getElem?_pos installed.locals 0 valid0).symm.trans untouched0)
    exact congrArg LocalState.value slot0
  have init := LenEntry.actual_entry_of_install options limits remaining span debug frames caller machine old tracked
    value 11 validDest oldDest destLive destCached localClocks raceOff ghost shallow thread index current active
    top present installed after installedArg (b.trans frameBody) (i.trans identity) (c.trans callee)
    valid0 dead0 (noRace.trans rawRace)
  let finalFrame := LenDone.doneFrame {installed with location := .unwinding LenEntryFacts.lenPreamble}
  refine ⟨finalFrame, after, init, b.trans frameBody, i.trans identity, c.trans callee, rfl,
    ?_, ?_, ?_, ?_, ledger, returned, continuation, noRace.trans rawRace, vaList, tracker, afterTracked, mode,
    protections, read, receiverFrame, machineFrame⟩
  · simpa [finalFrame, LenDone.doneFrame, CallEntryFacts.liveSlot, Array.getElem?_modify] using slot
  · simp [finalFrame, LenDone.doneFrame, CallEntryFacts.liveSlot, Array.getElem?_modify, untouched0]
  · simpa [finalFrame, LenDone.doneFrame, CallEntryFacts.liveSlot, Array.getElem?_modify] using untouched2
  · simpa [finalFrame, LenDone.doneFrame, CallEntryFacts.liveSlot] using afterSize

theorem init
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
    (validDest : 11 < caller.locals.size)
    (oldDest : Immediate Provenance) (destLive : caller.locals[11].value = .live (.immediate oldDest))
    (destCached : caller.locals[11].layout = some RootCompilerFacts.usizeLayout)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let value := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let newValue := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let destination := (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView
    ∃ finalFrame finalMachine,
      Call.initStackFrame (ExecutionMachine.callHooks cfg limits) () LenHelper.resolved.callee LenHelper.body LenHelper.abi
        #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩] false destination (.goto (some 3) .Unreachable)
        (Storage.withCurrent frames caller machine) = .ok () (Storage.withCurrent (frames.push caller) finalFrame finalMachine) ∧
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
  intro cfg inner value newValue destination
  obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n, _, _, tracker, trackedAfter, mode, tags, grant, _, _⟩ := initWithFrame
    options limits remaining fuel sizeFuel span budget sizing debug preciseOff implicitOff frames
    caller machine id parentTag parent root base offset len entry old tracked fresh cached live
    allocationMut raceOff localClocks positive bounded memoryBounds notNull cmp metadata noAlias
    ghost shallow coherent parentNode parentStored roots parentFound depth rank tagFresh freshNode
    room aligned reuse clean bounds owners validDest oldDest destLive destCached thread index
    current active top present
  exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,m,n, tracker, trackedAfter, mode, tags, grant⟩

#print axioms initWithFrame
#print axioms init
end DuplicatePrefix.CurrentLenEntry

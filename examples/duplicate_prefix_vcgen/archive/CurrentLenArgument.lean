import duplicate_prefix.CurrentLenFnEntry
import duplicate_prefix.CurrentReferenceCore
import duplicate_prefix.LenInstall
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.ScopedFrame

namespace DuplicatePrefix.CurrentLenArgument

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ArchiveForestProjection SourceDomain GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- Actual scoped installation of the shared receiver into the freshly
pushed length helper. Validation installs the protector and the exact
new pointee tag before the argument is visible to the callee. -/
theorem installWithFrame
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1) (sizing : options.place.dynamicFuel = sizeFuel+1)
    (debug : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (old : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some old)
    (fresh : old.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none) (localClocks : frame.extra.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
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
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (dead : frame.locals[1].value = .dead) (uncached : frame.locals[1].layout = none)
    (ledger : FrameState) (frameLedger : frame.extra.borrowTracker = some ledger) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let value := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let newValue := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let h := ExecutionMachine.callHooks cfg limits
    ∃ finalFrame finalMachine,
      h.withRetagMode () .FnEntry (LenInstall.action h value) (Storage.withCurrent frames frame machine) =
        .ok (1,1) (Storage.withCurrent frames finalFrame finalMachine) ∧
      finalFrame.extra.borrowTracker = some (ledger.addProtector id old.global.nextPointerTag) ∧
      finalFrame.locals[1]? = some ⟨.live (.immediate newValue), some LenHelper.rawLayout⟩ ∧
      finalFrame.body = frame.body ∧ finalFrame.bodyIdentity = frame.bodyIdentity ∧
      finalFrame.functionInstance = frame.functionInstance ∧
      finalFrame.returnPlace = frame.returnPlace ∧ finalFrame.returnContinuation = frame.returnContinuation ∧
      finalFrame.vaList = frame.vaList ∧ finalFrame.localsIdentity = frame.localsIdentity ∧
      finalFrame.locals.size = frame.locals.size ∧ finalFrame.extra.dataRace = frame.extra.dataRace ∧
      (∀ index, index ≠ 1 → finalFrame.locals[index]? = frame.locals[index]?) ∧
      ∃ tracker, finalMachine.borrowTracker = some tracker ∧ tracker.retagMode = old.retagMode ∧
        tracker.global.protectedTags = old.global.protectedTags.insert old.global.nextPointerTag .StrongProtector ∧
        CurrentSharedRetag.ReadGrant finalMachine entry id old.global.nextPointerTag root offset len tracker.global.protectedTags ∧
        CurrentLenFnEntry.FrameGrant finalMachine entry id parentTag old.global.nextPointerTag parent offset len tracker.global.protectedTags ∧
        finalMachine = {machine with memory := finalMachine.memory, borrowTracker := finalMachine.borrowTracker} := by
  intro cfg inner value newValue h
  let cachedFrame := LenInstall.cacheFrame frame valid
  have vc : 1 < cachedFrame.locals.size := by
    simpa [cachedFrame, LenInstall.cacheFrame, LenInstall.spanFrame, LocalOperands.cachedLayoutFrame] using valid
  let liveFrame := LenArgument.liveFrame cachedFrame 1 vc
  have vl : 1 < liveFrame.locals.size := by simpa [liveFrame, LenArgument.liveFrame] using vc
  let stored := CurrentReferenceLocalWrite.written liveFrame 1 value vl
  have vs : 1 < stored.locals.size := by simpa [stored, CurrentReferenceLocalWrite.written] using vl
  let scopedMachine := ScopedFrame.entered machine old .FnEntry
  let activeMachine := {scopedMachine with user := {scopedMachine.user with payload := {scopedMachine.user.payload with ghost := true}}}
  let activeBorrow := {old with retagMode := .FnEntry}
  let tagged := {stored with extra := {stored.extra with borrowTracker := some (ledger.addProtector id old.global.nextPointerTag)}}
  let reference := LenHelper.rawLayout
  have ty : reference.ty = 7 := LenHelper.raw_layout_type
  have cachedStored : stored.locals[1].layout = some reference := by
    simp [stored, liveFrame, cachedFrame, LenArgument.liveFrame, LenInstall.cacheFrame,
      LenInstall.spanFrame, LocalOperands.cachedLayoutFrame, CurrentReferenceLocalWrite.written, reference]
  have liveStored : stored.locals[1].value = .live (.immediate value) := by
    simp [stored, CurrentReferenceLocalWrite.written]
  obtain ⟨after, retagged, afterUser, newTracker, trackedAfter, modeAfter, newProtected, grant, machineFrame, receiverFrame⟩ :=
    CurrentLenFnEntry.runWithFrame options remaining span sizeFuel sizing preciseOff implicitOff frames stored activeMachine
      ledger frameLedger callee reference ty id parentTag parent root base offset len entry activeBorrow rfl rfl
      fresh old.global.nextPointerTag rfl cached live allocationMut raceOff positive bounded memoryBounds cmp
      metadata noAlias coherent parentNode parentStored roots parentFound depth rank tagFresh freshNode room aligned
      reuse clean bounds owners
  have sized : reference.layout.isSized = true := by decide +kernel
  obtain ⟨pa,pb,ra,rb,bo,repr⟩ : ∃ (pa pb : Primitive) (ra rb : WrappingRange) (bo : Size),
      reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := bo) := by
    with_unfolding_all exact ⟨_,_,_,_,_,rfl⟩
  have validated := CurrentReferenceCore.validatePositiveAcrossFrame options remaining span fuel sizeFuel sizing
    debug frames stored tagged scopedMachine after 1 vs reference false ty sized pa pb ra rb bo repr
    id parentTag old.global.nextPointerTag base offset len entry cached live notNull positive bounded memoryBounds
    rfl rfl cachedStored ghost (by rw [afterUser]) shallow cmp metadata noAlias liveStored retagged
  let written := CurrentReferenceLocalWrite.written tagged 1 newValue vs
  let restored := {after with user := {after.user with payload := {after.user.payload with ghost := false}}}
  have exactValidation : ValidityMachine.validateRuntime inner.validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size liveFrame 1 reference) true
      (Storage.withCurrent frames stored scopedMachine) = .ok () (Storage.withCurrent frames written restored) := by
    rw [budget]
    exact validated
  have localCached : liveFrame.locals[1].layout = some reference := by
    simp [liveFrame, cachedFrame, LenArgument.liveFrame, LenInstall.cacheFrame, LenInstall.spanFrame,
      LocalOperands.cachedLayoutFrame, reference]
  have localLive : liveFrame.locals[1].value = .live (.immediate .uninit) := by
    simp [liveFrame, LenArgument.liveFrame]
  have noPadding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false reference = .ok false := by
    with_unfolding_all rfl
  have copied := ReferenceArgumentCopy.copy_layout_with_nested_validation options limits remaining span debug
    frames liveFrame scopedMachine 1 .uninit value reference sized noPadding vl localLive localCached localClocks ghost shallow
    (LocalPlaces.localRuntimePlace frames.size liveFrame 1 reference).stackView rfl
    (Storage.withCurrent frames written restored) exactValidation
  have installed := LenInstall.install_of_copy options limits remaining span debug frames frame scopedMachine
    value valid body identity callee uncached dead localClocks ghost (Storage.withCurrent frames written restored) copied
  have effect := ScopedFrame.changed_state (LenInstall.action h value)
    (Storage.withCurrent frames frame machine) (Storage.withCurrent frames written restored)
    old newTracker .FnEntry (1,1) tracked trackedAfter installed
  let finalTracker := {newTracker with retagMode := old.retagMode}
  let finalMachine := {restored with borrowTracker := some finalTracker}
  have clearUser (value : Machine.RootUser) (off : value.payload.ghost = false) :
      {value with payload := {value.payload with ghost := false}} = value := by
    rw [← off]
  have restoredUser : restored.user = machine.user := by
    change {after.user with payload := {after.user.payload with ghost := false}} = machine.user
    rw [afterUser]
    exact clearUser machine.user ghost
  have stable : finalMachine = {machine with memory := finalMachine.memory, borrowTracker := finalMachine.borrowTracker} := by
    have clear : {after with user := restored.user} = restored := rfl
    dsimp only [finalMachine]
    rw [← clear, restoredUser, machineFrame]
    rfl
  refine ⟨written, finalMachine, effect, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_,
    finalTracker, rfl, rfl, newProtected, grant, receiverFrame, stable⟩
  · simp [written, tagged, stored, liveFrame, cachedFrame, CurrentReferenceLocalWrite.written,
      LenArgument.liveFrame, LenInstall.cacheFrame, LenInstall.spanFrame, LocalOperands.cachedLayoutFrame, reference]
  · simp [written, tagged, stored, liveFrame, cachedFrame, CurrentReferenceLocalWrite.written,
      LenArgument.liveFrame, LenInstall.cacheFrame, LenInstall.spanFrame, LocalOperands.cachedLayoutFrame]
  · intro index distinct
    simp [written, tagged, stored, liveFrame, cachedFrame, CurrentReferenceLocalWrite.written,
      LenArgument.liveFrame, LenInstall.cacheFrame, LenInstall.spanFrame, LocalOperands.cachedLayoutFrame,
      Ne.symm distinct]

theorem install
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1) (sizing : options.place.dynamicFuel = sizeFuel+1)
    (debug : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (old : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some old)
    (fresh : old.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none) (localClocks : frame.extra.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
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
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (dead : frame.locals[1].value = .dead) (uncached : frame.locals[1].layout = none)
    (ledger : FrameState) (frameLedger : frame.extra.borrowTracker = some ledger) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let value := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let newValue := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    let h := ExecutionMachine.callHooks cfg limits
    ∃ finalFrame finalMachine,
      h.withRetagMode () .FnEntry (LenInstall.action h value) (Storage.withCurrent frames frame machine) =
        .ok (1,1) (Storage.withCurrent frames finalFrame finalMachine) ∧
      finalFrame.extra.borrowTracker = some (ledger.addProtector id old.global.nextPointerTag) ∧
      finalFrame.locals[1]? = some ⟨.live (.immediate newValue), some LenHelper.rawLayout⟩ ∧
      finalFrame.body = frame.body ∧ finalFrame.bodyIdentity = frame.bodyIdentity ∧
      finalFrame.functionInstance = frame.functionInstance ∧
      finalFrame.returnPlace = frame.returnPlace ∧ finalFrame.returnContinuation = frame.returnContinuation ∧
      finalFrame.vaList = frame.vaList ∧ finalFrame.localsIdentity = frame.localsIdentity ∧
      finalFrame.locals.size = frame.locals.size ∧ finalFrame.extra.dataRace = frame.extra.dataRace ∧
      (∀ index, index ≠ 1 → finalFrame.locals[index]? = frame.locals[index]?) ∧
      ∃ tracker, finalMachine.borrowTracker = some tracker ∧ tracker.retagMode = old.retagMode ∧
        tracker.global.protectedTags = old.global.protectedTags.insert old.global.nextPointerTag .StrongProtector ∧
        CurrentSharedRetag.ReadGrant finalMachine entry id old.global.nextPointerTag root offset len tracker.global.protectedTags := by
  intro cfg inner value newValue h
  obtain ⟨a,b,c,d,e,f,g,h1,i,j,k,l,m,n,rest,tracker,trackedAfter,mode,tagState,grant, _, _⟩ := installWithFrame
    options limits remaining fuel sizeFuel span budget sizing debug preciseOff implicitOff frames
    frame machine id parentTag parent root base offset len entry old tracked fresh cached live
    allocationMut raceOff localClocks positive bounded memoryBounds notNull cmp metadata noAlias
    ghost shallow coherent parentNode parentStored roots parentFound depth rank tagFresh freshNode
    room aligned reuse clean bounds owners valid body identity callee dead uncached ledger
    frameLedger
  exact ⟨a,b,c,d,e,f,g,h1,i,j,k,l,m,n,rest,tracker,trackedAfter,mode,tagState,grant⟩

#print axioms installWithFrame
#print axioms install
end DuplicatePrefix.CurrentLenArgument

import duplicate_prefix.CurrentSharedRetag
import duplicate_prefix.CurrentReferenceCore
import duplicate_prefix.RootSharedStep

namespace DuplicatePrefix.RootSharedComplete

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ArchiveForestProjection SourceDomain GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

/-- On a prepared nonempty concrete slice, the emitted shared reference
assignment really reborrows the allocation and installs its fresh tag in
local 12 before the call to slice length. -/
theorem stepWithRights
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (budget : options.limits.validation = fuel+1) (sizing : options.place.dynamicFuel = sizeFuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (old : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some old)
    (mode : old.retagMode = .Default)
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
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row old.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : 12 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨2,11⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (destLive : frame.locals[12].value = .live (.immediate .uninit))
    (destUncached : frame.locals[12].layout = none) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let initialPtr := Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
    let initialRef : Immediate Provenance :=
      .scalarPair (.fromPointer config.access.runtime.base initialPtr) (.fromScalarInt (.ofUInt64 len))
    let freshPtr := Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))
    let freshRef : Immediate Provenance :=
      .scalarPair (.fromPointer config.access.runtime.base freshPtr) (.fromScalarInt (.ofUInt64 len))
    (frame.locals[1]'(by omega)).value = .live (.immediate initialRef) →
    ∃ resultFrame resultMachine,
      ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames resultFrame resultMachine, .ok true) ∧
      resultFrame.location = .mir ⟨2,12⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate freshRef),some RootSharedStep.sharedLayout⟩ ∧
      CurrentSharedRetag.ReadGrant resultMachine entry id old.global.nextPointerTag root offset len old.global.protectedTags ∧
      ∃ tracker, resultMachine.borrowTracker = some tracker ∧ tracker.retagMode = .Default ∧
        tracker.global.protectedTags = old.global.protectedTags := by
  intro config initialPtr initialRef freshPtr freshRef sourceLive
  let reference := RootSharedStep.sharedLayout
  let cachedFrame := RootSharedStep.cacheDestination frame capacity
  have cachedSize : cachedFrame.locals.size = frame.locals.size := by
    simp [cachedFrame, RootSharedStep.cacheDestination, LocalPlaces.cachePlaceLayout]
  have index : 12 < cachedFrame.locals.size := by rwa [cachedSize]
  let stored := CurrentReferenceLocalWrite.written cachedFrame 12 initialRef index
  have storedSize : stored.locals.size = frame.locals.size := by
    simpa [stored, CurrentReferenceLocalWrite.written] using cachedSize
  have valid : 12 < stored.locals.size := by rwa [storedSize]
  have storedLayout : stored.locals[12].layout = some reference := by
    simp [stored, cachedFrame, RootSharedStep.cacheDestination, CurrentReferenceLocalWrite.written,
      LocalPlaces.cachePlaceLayout, reference]
  have storedLoc : stored.location = .mir ⟨2,11⟩ := located
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  have typed : reference.ty = 7 := by with_unfolding_all rfl
  obtain ⟨after, adjusted, activeUser, tracker, trackedAfter, modeAfter, protec, grant⟩ :=
    CurrentSharedRetag.runWithRights options remaining span sizeFuel sizing preciseOff implicitOff frames stored activeMachine
      reference typed id parentTag parent root base offset len entry old tracked mode fresh old.global.nextPointerTag
      rfl cached live allocationMut raceOff positive bounded memoryBounds cmp metadata noAlias coherent parentNode
      parentStored roots parentFound depth rank tagFresh room aligned reuse clean bounds owners
  have sized : reference.layout.isSized = true := by with_unfolding_all rfl
  have pair : ∃ (pa pb : Primitive) (ra rb : WrappingRange) (bo : Size),
      reference.layout.backendRepr = .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := bo) := by
    with_unfolding_all exact ⟨_, _, _, _, _, rfl⟩
  obtain ⟨pa, pb, ra, rb, bo, repr⟩ := pair
  have activeAfter : after.user.payload.ghost = true := by rw [activeUser]
  have runtimeSame : (PreparedContracts.actualConfig options () remaining span).access.runtime =
      config.access.runtime := (actual_access_runtime options () remaining span).trans
        (actual_access_runtime options () (remaining+1) span).symm
  have inputValue :
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len reference).imm = initialRef := by
    rw [runtimeSame]
    rfl
  have outputValue :
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
        (Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))) len reference).imm = freshRef := by
    rw [runtimeSame]
    rfl
  have inputLive : stored.locals[12].value = .live (.immediate initialRef) := by
    simp [stored, CurrentReferenceLocalWrite.written]
  have validated := CurrentReferenceCore.validatePositive options remaining span fuel sizeFuel sizing debug
    frames stored machine after 12 valid reference false typed sized pa pb ra rb bo repr id parentTag
    old.global.nextPointerTag base offset len entry cached live notNull positive bounded memoryBounds storedLayout
    ghost activeAfter shallow cmp metadata noAlias (by rw [inputValue]; exact inputLive) adjusted
  let finalMachine := {after with user := {after.user with payload := {after.user.payload with ghost := false}}}
  let finalFrame := CurrentReferenceLocalWrite.written stored 12 freshRef valid
  have canonical := RootSharedStep.stepOfValidation options limits remaining fuel span budget debug frames
    frame finalFrame machine finalMachine initialPtr len capacity body identity callee located storedLoc
    sourceCached destLive destUncached localClocks old tracker tracked trackedAfter mode modeAfter ghost shallow
    sourceLive (by simpa only [outputValue] using validated)
  refine ⟨{finalFrame with location := .mir ⟨2,12⟩}, finalMachine, canonical, rfl, ?_, grant,
    tracker, trackedAfter, modeAfter, protec⟩
  simp [finalFrame, CurrentReferenceLocalWrite.written, storedLayout, valid, reference]

theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (budget : options.limits.validation = fuel+1) (sizing : options.place.dynamicFuel = sizeFuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (old : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some old)
    (mode : old.retagMode = .Default)
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
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row old.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : 12 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨2,11⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (destLive : frame.locals[12].value = .live (.immediate .uninit))
    (destUncached : frame.locals[12].layout = none) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let initialPtr := Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
    let initialRef : Immediate Provenance :=
      .scalarPair (.fromPointer config.access.runtime.base initialPtr) (.fromScalarInt (.ofUInt64 len))
    let freshPtr := Pointer.new (.concrete id old.global.nextPointerTag) (Size.ofBytes (base+offset))
    let freshRef : Immediate Provenance :=
      .scalarPair (.fromPointer config.access.runtime.base freshPtr) (.fromScalarInt (.ofUInt64 len))
    (frame.locals[1]'(by omega)).value = .live (.immediate initialRef) →
    ∃ resultFrame resultMachine,
      ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames resultFrame resultMachine, .ok true) ∧
      resultFrame.location = .mir ⟨2,12⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate freshRef),some RootSharedStep.sharedLayout⟩ := by
  intro config initialPtr initialRef freshPtr freshRef sourceLive
  obtain ⟨resultFrame,resultMachine,execution,location,localValue,_,_⟩ :=
    stepWithRights options limits remaining fuel sizeFuel span debug budget sizing preciseOff implicitOff frames
      frame machine id parentTag parent root base offset len entry old tracked mode fresh cached live allocationMut
      raceOff localClocks positive bounded memoryBounds notNull cmp metadata noAlias ghost shallow coherent parentNode
      parentStored roots parentFound depth rank tagFresh room aligned reuse clean bounds owners capacity body identity
      callee located sourceCached destLive destUncached sourceLive
  exact ⟨resultFrame,resultMachine,execution,location,localValue⟩

#print axioms stepWithRights
#print axioms step
end DuplicatePrefix.RootSharedComplete

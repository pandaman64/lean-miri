import duplicate_prefix.LenInstall
import duplicate_prefix.EmptyBackedLenArgument

namespace DuplicatePrefix.EmptyBackedLenInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts EmptyReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem live_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : EmptyReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset : UInt64) (parentTag : BorTag)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO frozenRead) (sharedPolicy true).outsidePermission true =
        ⟨finalTree, .ok ()⟩)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false)
 :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let resultMachine := {EmptyBackedPointer.registeredMachine (EmptyReferenceAllocation.allocatedMachine machine tracker fresh)
      (EmptyReferenceAllocation.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (EmptyBackedPointer.registeredFrame (LenInstall.resultFrame frame valid output) borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  have validInstance : frame.functionInstance < PreparedReflection.actual.program.input.instances.size := by
    rw [callee]
    decide +kernel
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
  let cache := LenInstall.cacheFrame frame valid
  have cacheValid : 1 < cache.locals.size := by simpa [cache,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame] using valid
  let live := LenArgument.liveFrame cache 1 cacheValid
  have liveValid : 1 < live.locals.size := by simpa [live,LenArgument.liveFrame] using cacheValid
  have cached : live.locals[1].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [live,LenArgument.liveFrame,cache,LenInstall.cacheFrame,LocalOperands.cachedLayoutFrame,LenHelper.rawLayout]
  have checked := EmptyBackedLenArgument.live_zero options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset parentTag nonzero frames live machine
    tracker enabled mode borrowFrame frameBorrow fresh 1 liveValid .uninit
    (by simp [live,LenArgument.liveFrame]) cached noClocks ghost shallow cachedAddress present finalTree child metadata notConstructed
    (LocalPlaces.localRuntimePlace frames.size live 1 SharedReferenceMetadata.sharedLayout).stackView rfl
  apply LenInstall.install_of_copy options limits remaining span debugOff frames frame machine value valid body identity callee
    uncached dead noClocks ghost _
  simpa only [live,cache,EmptyBackedLenArgument.copiedFrame,LenInstall.resultFrame,LenInstall.cacheFrame,
    LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,LenArgument.liveFrame,
    EmptyBackedPointer.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem_set_self,Array.set_set] using checked

theorem live_zero_scoped
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : EmptyReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset : UInt64) (parentTag : BorTag)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new Size.ZERO frozenRead) (sharedPolicy true).outsidePermission true =
        ⟨finalTree, .ok ()⟩)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let resultMachine := {EmptyBackedPointer.registeredMachine (EmptyReferenceAllocation.allocatedMachine machine tracker fresh)
      (EmptyReferenceAllocation.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (EmptyBackedPointer.registeredFrame (LenInstall.resultFrame frame valid output) borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  have validInstance : frame.functionInstance < PreparedReflection.actual.program.input.instances.size := by
    rw [callee]
    decide +kernel
  let activeTracker := {tracker with retagMode := .FnEntry}
  let activeMachine := {machine with borrowTracker := some activeTracker}
  have made := live_zero options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset parentTag nonzero frames frame activeMachine
    activeTracker rfl rfl borrowFrame frameBorrow fresh valid body identity callee uncached dead noClocks ghost shallow
    cachedAddress present finalTree child metadata notConstructed
  change MachineHooks.withRetagMode .FnEntry _ _ = _
  unfold MachineHooks.withRetagMode
  simp only [Storage.withCurrent]
  rw [enabled]
  dsimp only
  simp only [Storage.withCurrent,activeMachine,activeTracker] at made
  rw [made]
  simp only [Storage.withCurrent,EmptyBackedPointer.registeredMachine,EmptyReferenceAllocation.allocatedMachine,
    EmptyReferenceAllocation.allocatedTracker,EmptyBackedPointer.registeredGlobal,activeMachine,activeTracker]
  rfl

#print axioms live_zero
end
end DuplicatePrefix.EmptyBackedLenInstall

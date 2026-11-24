import duplicate_prefix.EmptyWildcardLocalWrite
import duplicate_prefix.EmptyReferenceFacts
import duplicate_prefix.CopyHelperSteps
import duplicate_prefix.EmptyLocalReferenceWrite
namespace DuplicatePrefix.EmptyWildcardReference
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts EmptyReferenceContext EmptyReferenceInfo
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem zero_rvalue_of_local_write
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : EmptyReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (address : UInt64)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base 0)))
    (sourceCached : frame.locals[1].layout = some EmptyReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout true) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false)
    (validInstance : frame.functionInstance < PreparedReflection.actual.program.input.instances.size := by
      first | assumption | (rw [callee]; with_unfolding_all decide +kernel) | (rw [function]; with_unfolding_all decide +kernel) | (rw [fnInstance]; with_unfolding_all decide +kernel) | with_unfolding_all decide +kernel)
    (localWrite :
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout true) validDest
      let value := PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) cfg.access.runtime.base 0
      let entered := EmptyReferenceRvalue.enter machine tracker true
      let afterFrame := EmptyReferenceWrite.written cachedFrame localId value
        (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
      (ExecutionMachine.rvalueHooks cfg limits).writeImmediate () value
        (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true))
        (Storage.withCurrent frames cachedFrame entered) = .ok ()
        (Storage.withCurrent frames afterFrame
          (EmptyReferenceAllocation.allocatedMachine entered {tracker with retagMode := mode true} fresh))) :
    let inner := config options remaining span
    let value := (⟨PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base 0, layout true⟩ : RvalueImmTy Provenance)
    let resultMachine := EmptyReferenceAllocation.allocatedMachine machine tracker fresh
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (EmptyReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout true) validDest value.imm) resultMachine) := by
  let inner := config options remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks outer limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout true) validDest
  let activeTracker := {tracker with retagMode := mode true}
  let enteredMachine := EmptyReferenceRvalue.enter machine tracker true
  let updatedMachine := EmptyReferenceAllocation.allocatedMachine enteredMachine activeTracker fresh
  let value := (⟨PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base 0, layout true⟩ : RvalueImmTy Provenance)
  let afterFrame := EmptyReferenceWrite.written cachedFrame localId value.imm
    (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
  have info := EmptyReferenceInfo.facts options remaining span ctx true
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    localId (layout true) validDest destUncached info.sized query
  have cachedSourceValid : (1 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validSource
  have cachedDestValid : localId < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have sourceLive' : cachedFrame.locals[1].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) outer.access.runtime.base 0)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different,PtrMetadataComplete.rawImmediate,RetagReferencePlace.integerSliceValue,outer] using sourceLive
  have sourceCached' : cachedFrame.locals[1].layout = some EmptyReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using sourceCached
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span debugOff frames cachedFrame machine
    1 (.inl (Pointer.new .wildcard (Size.ofBytes address))) 0 cachedSourceValid sourceLive' sourceCached' noClocks ghost
  have writer' : hooks.writeImmediate () value.imm
      (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true))
      (Storage.withCurrent frames cachedFrame enteredMachine) =
      .ok () (Storage.withCurrent frames afterFrame updatedMachine) := localWrite
  have result := EmptyReferenceRvalue.of_write options limits (remaining+1) span true region
    (.inl (Pointer.new .wildcard (Size.ofBytes address))) 0 ⟨1,#[.Deref]⟩ ⟨localId,#[]⟩
    (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true)) (Storage.withCurrent frames frame machine)
    frames cachedFrame machine tracker (EmptyReferenceAllocation.allocatedTracker activeTracker fresh) enabled shallow rfl
    destination sourcePlace afterFrame updatedMachine rfl writer'
  simpa only [afterFrame,updatedMachine,enteredMachine,EmptyReferenceRvalue.enter,EmptyReferenceAllocation.allocatedMachine,
    EmptyReferenceAllocation.allocatedTracker,activeTracker,EmptyReferenceWrite.written,ActualLocalCopy.written,cachedFrame,value,
    inner] using result

theorem zero_statement
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (unresolved : EmptyWildcardLocalValidator.Unresolved machine.user.addresses machine.memory address)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (EmptyReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (EmptyReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base 0)))
    (sourceCached : frame.locals[1].layout = some EmptyReferenceMetadata.reference)
    (destLive : frame.locals[EmptyReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[EmptyReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false) :
    let inner := config options remaining span
    let value := (⟨PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base 0, layout true⟩ : RvalueImmTy Provenance)
    let resultMachine := EmptyReferenceAllocation.allocatedMachine machine tracker fresh
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (EmptyReferenceFacts.destination true) (layout true) validDest value.imm)
        (EmptyReferenceFacts.location true)) resultMachine,.ok true) := by
  obtain ⟨ctx⟩ := EmptyReferenceContext.exists_context options remaining span preciseOff implicitOff
  have query := EmptyReferenceFacts.compute_destination frames frame machine sourceBody identity callee true
  have different : EmptyReferenceFacts.destination true ≠ 1 := by cases true <;> decide
  have validInstance : frame.functionInstance < PreparedReflection.actual.program.input.instances.size := by
    rw [callee]
    decide +kernel
  have rvalue := zero_rvalue_of_local_write options limits remaining span ctx debugOff cmp .Erased dynamicFuel validityFuel fuelEq validationFuel
    address frames frame machine tracker enabled
    defaultMode fresh (EmptyReferenceFacts.destination true) different validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks ghost shallow metadata notConstructed validInstance
  let cachedFrame := LocalPlaces.cachePlaceLayout frame (EmptyReferenceFacts.destination true) (layout true) validDest
  have cachedBound : EmptyReferenceFacts.destination true < cachedFrame.locals.size := by
    simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using validDest
  have writer := EmptyWildcardLocalWrite.zero_cached options limits remaining span ctx debugOff cmp true dynamicFuel validityFuel
    fuelEq validationFuel address nonzero frames cachedFrame (EmptyReferenceRvalue.enter machine tracker true)
    {tracker with retagMode := mode true} rfl rfl fresh (EmptyReferenceFacts.destination true) .uninit cachedBound
    (by simpa [cachedFrame, LocalPlaces.cachePlaceLayout] using destLive)
    (by simp [cachedFrame, LocalPlaces.cachePlaceLayout]) unresolved noClocks ghost shallow metadata notConstructed validInstance
  have baseEq : (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base = (config options remaining span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span, CanonicalConfigFacts.actual_access_runtime options () remaining span]
  specialize rvalue (by simpa [cachedFrame, baseEq, PtrMetadataComplete.rawImmediate, RetagReferencePlace.sliceValue] using writer)
  let inner := config options remaining span
  let value := (⟨PtrMetadataComplete.rawImmediate (.inl (Pointer.new .wildcard (Size.ofBytes address))) (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base 0, layout true⟩ : RvalueImmTy Provenance)
  let resultMachine := EmptyReferenceAllocation.allocatedMachine machine tracker fresh
  let resultFrame := ActualLocalCopy.written frame (EmptyReferenceFacts.destination true) (layout true) validDest value.imm
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    frames frame resultFrame machine resultMachine (EmptyReferenceFacts.location true)
    ⟨EmptyReferenceFacts.destination true,#[]⟩ (.Ref .Erased (EmptyReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) located
  · simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using located
  · rw [sourceBody]
    exact EmptyReferenceFacts.statement true
  · exact rvalue

#print axioms zero_statement
end
end DuplicatePrefix.EmptyWildcardReference

import duplicate_prefix.EmptyPointerShallow
import duplicate_prefix.EmptyUnresolvedPointerBorrow
import duplicate_prefix.EmptyReferenceAllocation
import duplicate_prefix.EmptyReferenceMetadata
namespace DuplicatePrefix.EmptyWildcardLocalValidator
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts EmptyReferenceContext Miri.Memory.AllocAddresses
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The zero-width stock address lookup selects no live, exposed allocation.
This uses the address table and heap alone, and is independent of frame,
retag scope, or ghost validation. -/
def Unresolved (addresses : GlobalAddressState)
    (memory : MemoryState Provenance BorrowTree K) (address : UInt64) : Prop :=
  addresses.allocIdFromAddr address (Int64.ofInt 0)
    {sizeOf := fun id => (memory.getAllocInfo id).toOption.map (·.size),
     isLive := fun id => some (memory.isAllocLive id)} = .ok none

theorem zero_unresolved
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : EmptyReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (reference : LocalLayout) (mutability : MIR.Mutability) (mode : RetagPolicy.RetagMode)
    (dereference : CompilerFacts.builtinDeref ReferenceMetadataFacts.prepared.context reference.ty true =
      .ok (some ProjectionMetadataFacts.sliceLayout.ty))
    (sized : reference.layout.isSized = true)
    (readable : ∃ pa pb ra rb offset, reference.layout.backendRepr = .ScalarPair
      (a := .Initialized (value := pa) (validRange := ra)) (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset))
    (name : String)
    (named : (config options remaining span).validity.typeName () reference.ty = pure name)
    (classified : (config options remaining span).validity.classify () reference.ty = pure (.reference (mutability == .Mut)))
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (currentMode : tracker.retagMode = mode)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 2) = false)
    (policy : RetagPolicy.NewPermission)
    (shape : (adapted options remaining span ctx.pointers).typeShape reference.ty = pure .reference)
    (pointeeQuery : (adapted options remaining span ctx.pointers).referencePointee reference.ty =
      pure (ProjectionMetadataFacts.sliceLayout.ty,mutability))
    (unpin : (adapted options remaining span ctx.pointers).isUnpin ProjectionMetadataFacts.sliceLayout.ty = pure true)
    (unsafeUnpin : (adapted options remaining span ctx.pointers).isUnsafeUnpin ProjectionMetadataFacts.sliceLayout.ty = pure true)
    (frozen : (adapted options remaining span ctx.pointers).typeIsFreeze ProjectionMetadataFacts.sliceLayout.ty = pure true)
    (created : RetagPolicy.create ⟨true,true,true⟩ (if mutability == .Mut then .Mutable else .Shared)
      mode ⟨false,false⟩ = some policy)
    (validInstance : frame.functionInstance < PreparedReflection.actual.program.input.instances.size)
    (unresolved : Unresolved machine.user.addresses machine.memory address) :
    let cfg := config options remaining span
    let resultMachine := EmptyReferenceAllocation.allocatedMachine machine tracker fresh
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm),
         layout := frame.locals[localId].layout} valid)} resultMachine) := by
  let cfg := config options remaining span
  let retag := adapted options remaining span ctx.pointers
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent frames frame activeMachine
  let place := RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 ProjectionMetadataFacts.sliceLayout
  let afterMachine := EmptyReferenceAllocation.allocatedMachine activeMachine tracker fresh
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have sizing : retag.sizeAndAlign place active = .ok (some (Size.ofBytes 0,Align.ONE)) active := by
    rw [← ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp active dynamicFuel fuelEq 0
      metadata notConstructed (by decide) place rfl rfl
  have resolution : retag.resolveAllocation (Pointer.new (some .wildcard) (Size.ofBytes address))
      (TypedRetagEmpty.afterTag active tracker fresh) =
      .ok none (TypedRetagEmpty.afterTag active tracker fresh) := by
    rw [ctx.source.resolve]
    apply EmptyWildcardRetag.ofSelection
    unfold GlobalAddressState.ptrGetAlloc
    have lookup : (TypedRetagEmpty.afterTag active tracker fresh).machine.user.addresses.allocIdFromAddr address (Int64.ofInt 0)
        {sizeOf := fun id => ((TypedRetagEmpty.afterTag active tracker fresh).machine.memory.getAllocInfo id).toOption.map (·.size),
         isLive := fun id => some ((TypedRetagEmpty.afterTag active tracker fresh).machine.memory.isAllocLive id)} = .ok none :=
      unresolved
    simp only [Pointer.new, Size.ofBytes]
    rw [lookup]
    rfl
  have definitionReady := EmptyReferenceContext.instance_definition_ready options remaining span ctx.pointers frame validInstance
  have retagged := EmptyUnresolvedPointerBorrow.unresolved_zero_pointer retag ReferenceMetadataFacts.prepared cfg.access
    cfg.validity.projection cfg.validity.vtable ctx.pointers () ctx.source options.limits.retag reference ProjectionMetadataFacts.sliceLayout
    (Pointer.new .wildcard (Size.ofBytes address)) mutability mode policy shape pointeeQuery unpin unsafeUnpin frozen created dereference
    EmptyReferenceMetadata.pointee_layout ProjectionMetadataFacts.slice_layout_shape.2.2
    (CanonicalConfigFacts.actual_target_width options () remaining span)
    active frames frame rfl tracker enabled currentMode fresh sizing resolution
  have retagAt : cfg.validity.retagPointer () (RetagReferencePlace.sliceValue cfg.access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference) reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue cfg.access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference))
        (Storage.withCurrent frames frame afterMachine) := by
    rw [ctx.visitor.retagAction]
    simpa only [retag,active,Storage.withCurrent,afterMachine,TypedRetagEmpty.afterTag,EmptyReferenceAllocation.allocatedMachine,EmptyReferenceAllocation.allocatedTracker] using retagged
  have debug : ctx.inner.debugAssertions = false := ctx.innerDebug.trans (fields.debug.trans debugOff)
  have noDebug : ctx.inner.debugAbiCheck (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm reference = pure () := by
    rw [ctx.innerAbi,fields.debugAbiNoChecks debugOff]
  obtain ⟨target,tail,inhabited,name3,kind3⟩ := EmptyReferenceMetadata.visitor_metadata options remaining span
  obtain ⟨pa,pb,ra,rb,pairOffset,repr⟩ := readable
  have validator := EmptyPointerShallow.validate_of_retag cfg.validity cfg.access cfg.allocation ctx.inner retag
    ReferenceMetadataFacts.prepared ctx.pointers () options.limits.retag validityFuel ctx.visitor ctx.source reference
    ProjectionMetadataFacts.sliceLayout (Pointer.new .wildcard (Size.ofBytes address)) (Pointer.new .wildcard (Size.ofBytes address)) nonzero dereference EmptyReferenceMetadata.pointee_layout ProjectionMetadataFacts.slice_layout_shape.2.2
    ctx.pointer (CanonicalConfigFacts.actual_target_width options () remaining span)
    (EmptyReferenceMetadata.visitor_target options remaining span).1 (EmptyReferenceMetadata.visitor_target options remaining span).2
    ProjectionMetadataFacts.slice_layout_shape.2.1 tail inhabited name (mutability == .Mut) frames frame machine localId valid live cached sized
    pa pb ra rb pairOffset repr debug noDebug ghost (CanonicalConfigFacts.actual_retain_touched options () remaining span)
    frame afterMachine rfl rfl rfl sizing retagAt named classified
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent frames frame machine) =
      .ok false (Storage.withCurrent frames frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively,Storage.withCurrent,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  unfold ValidityMachine.validateRuntime
  simp only [bind,EStateM.bind,recursive]
  have restore : {machine.user.payload with ghost := false} = machine.user.payload := by rw [← ghost]
  simpa only [afterMachine,activeMachine,EmptyReferenceAllocation.allocatedMachine,restore] using validator

#print axioms zero_unresolved
end
end DuplicatePrefix.EmptyWildcardLocalValidator

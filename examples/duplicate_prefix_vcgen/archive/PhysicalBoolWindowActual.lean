import duplicate_prefix.PhysicalBoolWindowWrite
import duplicate_prefix.PhysicalBoolWindowValidateActual
import duplicate_prefix.S04ReturnAllocationClear
import duplicate_prefix.DuplicatePrefixPhysicalContexts
import duplicate_prefix.CopyHolderRights
import duplicate_prefix.RootActualPhysicalReturn

namespace DuplicatePrefix.PhysicalBoolWindowActual

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The canonical write and nonrecursive Boolean validation for a concrete
one-byte destination inside an arbitrary ordinary allocation. -/
theorem write_actual (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (state : CanonicalConfigFacts.RootState) (place : MPlaceTy Provenance)
    (window : PhysicalBoolWindowWrite.Window state.machine place)
    (value : Bool)
    (tracker : MachineHooks.BorrowState) (tracked : state.machine.borrowTracker = some tracker)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (source root : UniIndex) (node : TreeNode) (found : window.entry.allocation.extra.nodeAt source = some node)
    (key : window.entry.allocation.extra.indexOfTag window.tag = some source)
    (roots : window.entry.allocation.extra.roots = #[root])
    (coherent : CoherentForest window.entry.allocation.extra)
    (treeBounds : window.offset.toNat + 1 ≤ window.entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights window.entry.allocation.extra row tracker.global.protectedTags source)
      window.offset (window.offset+1) window.entry.allocation.extra.locations)
    (extras : let context := (DuplicatePrefixPhysicalContexts.canonical options remaining span).writeContext
      (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == window.id) =
        some (window.id,{weakMemory := none, backtrace := (AllocationBacktrace.get
          ((context.extras.get state.machine.user).allocations) window.id)}))
    (addressBound : place.mplace.ptr.offset.bytes.toNat + 1 < 2^64) :
    ∃ updated, (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () (.scalar (Scalar.fromBool value)) ⟨.memory place.mplace,place.layout⟩ state =
      .ok () (CanonicalCopy.replaceAllocation state window.id window.entry.kind updated) ∧
      updated.byteSize = window.entry.allocation.byteSize ∧ updated.len = window.entry.allocation.len ∧
      updated.mutability = .Mut := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.writeContext
  let validationContext := contexts.validationContext
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let tree := window.entry.allocation.extra
  let range := allocRange (Size.ofBytes window.offset) (Size.ofBytes 1)
  let access := tree.performBorrowAccessRange (.concrete window.tag) range.start range.size .Write
    tracker.global.protectedTags .VisitChildrenOfAccessed
  have complete : access.status = .Completed :=
    bounded_range tree tracker.global.protectedTags window.tag source root .Write range.start range.size
      coherent node found roots key treeBounds owners
  have hook : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ tree window.id
      (.concrete window.tag) range = ⟨⟨state.machine,none⟩,access.tree,.ok ()⟩ := by
    have exactRun := MemoryCopyBridge.source_memory_access_exact context.prepared context.image context.maximum context.fuel
      context.globalHooks context.pointers context.extras state.machine tracker tree window.id (.concrete window.tag) range
      true noClocks noBackend tracked extras
    have completed := complete
    dsimp only [access] at completed
    simpa only [context, CanonicalCopy.Context.access, ite_true, completed] using exactRun
  have resolve : context.access.resolvePointer state.machine.memory place.mplace.ptr (Int.ofNat (1 : UInt64).toNat)
      state.machine = .ok (.ok ⟨window.id,range.start,.concrete window.tag⟩) state.machine := by
    rw [window.pointer]
    exact MemoryCopyBridge.typed_resolve_cached context.pointers state.machine.memory state.machine window.id
      window.tag window.base window.offset (Int.ofNat (1 : UInt64).toNat) contexts.width (by decide) (by decide)
      window.cachedBase
  obtain ⟨stored, writeEq, _, storedSize, storedLen, storedMut, read, pointerBounds⟩ :=
    PhysicalBoolWindowWrite.on_context_of_access context state place window access.tree value contexts.width
      contexts.runtimeWidth contexts.runtimeSize hook resolve config.compiler.willValidateMemory
  let intermediate := CanonicalCopy.replaceAllocation state window.id window.entry.kind stored
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨window.entry.kind,stored⟩
  have present : intermediate.machine.memory.live[window.id]? = some entry :=
    CanonicalCopy.replace_lookup state window.id window.entry.kind stored
  have size := storedSize.trans window.size
  have length := storedLen.trans window.bytes
  obtain ⟨updated, cleared, len, bytes, mutability, _, _, _⟩ :=
    S04ReturnAllocationClear.clear_exists stored window.capacity window.offset length size window.bounds pointerBounds
  have read' : Allocation.readScalar stored validationContext.access.runtime.base range false =
      .ok (Scalar.fromBool value) := by
    rw [contexts.sameRuntime]
    exact read
  obtain ⟨finish, endpoint⟩ : ∃ finish, (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish :=
    ⟨_, DuplicatePrefix.source_end place.mplace.ptr.offset 1 (by simpa using addressBound)⟩
  have validation := PhysicalBoolWindowValidateActual.validate_actual validationContext options remaining span
    contexts.accessEq intermediate place.mplace window.id window.tag window.base window.offset window.capacity entry updated
    value fuel contexts.validationWidth window.cachedBase present size window.bounds storedMut read' cleared
    window.pointer window.aligned contexts.validationRuntimeSize ghost shallow finish endpoint
  have memoryEq : CanonicalCopy.replaceAllocation intermediate window.id entry.kind updated =
      CanonicalCopy.replaceAllocation state window.id window.entry.kind updated := by
    unfold intermediate CanonicalCopy.replaceAllocation
    exact (congrArg (fun m => {state with machine := {state.machine with memory := m}})
      (MemoryCopyBridge.live_update_twice state.machine.memory window.id entry ⟨window.entry.kind,updated⟩))
  rw [memoryEq] at validation
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have write : writePlaceImmediateNoValidate hooks () (.scalar (Scalar.fromBool value))
      ⟨.memory place.mplace,place.layout⟩ state = .ok () intermediate := by
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    have sized : place.layout.layout.isSized = true := by rw [window.layout]; decide +kernel
    simp only [sized, Bool.true_eq_false, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure]
    change config.projection.place.writeMemoryNoValidate () (.scalar (Scalar.fromBool value)) place state = _
    rw [fields.projectionWriteMemory]
    have scopedResult : ValidityMachine.scopedAccess config.access state = .ok context.access state := by
      unfold ValidityMachine.scopedAccess ValidityMachine.validationInProgress
      simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure, ghost]
      rw [contexts.outerAccessEq]
      rfl
    have enforce : ValidityMachine.enforceValidity state = .ok true state := by
      simp [ValidityMachine.enforceValidity, shallow, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, pure, EStateM.pure]
    dsimp only [config] at scopedResult
    simp only [bind, EStateM.bind, scopedResult, enforce]
    exact writeEq
  have enforced : hooks.enforceValidity () place.layout intermediate = .ok true intermediate := by
    change config.projection.place.enforceValidity () place.layout intermediate = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, intermediate, CanonicalCopy.replaceAllocation, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have checked : hooks.validate () ⟨.memory place.mplace,place.layout⟩ intermediate =
      .ok () (CanonicalCopy.replaceAllocation state window.id window.entry.kind updated) := by
    change config.projection.place.validate () _ intermediate = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor, validationFuel, window.layout]
    exact validation
  refine ⟨updated, ?_, bytes.trans storedSize, len.trans storedLen, mutability.trans storedMut⟩
  change writePlaceImmediate hooks () (.scalar (Scalar.fromBool value)) ⟨.memory place.mplace,place.layout⟩ state = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [write]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact checked

theorem copy_return (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (state : CanonicalConfigFacts.RootState) (place : MPlaceTy Provenance)
    (window : PhysicalBoolWindowWrite.Window state.machine place)
    (value : Bool)
    (tracker : MachineHooks.BorrowState) (tracked : state.machine.borrowTracker = some tracker)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (source root : UniIndex) (node : TreeNode) (found : window.entry.allocation.extra.nodeAt source = some node)
    (key : window.entry.allocation.extra.indexOfTag window.tag = some source)
    (roots : window.entry.allocation.extra.roots = #[root])
    (coherent : CoherentForest window.entry.allocation.extra)
    (treeBounds : window.offset.toNat + 1 ≤ window.entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights window.entry.allocation.extra row tracker.global.protectedTags source)
      window.offset (window.offset+1) window.entry.allocation.extra.locations)
    (extras : let context := (DuplicatePrefixPhysicalContexts.canonical options remaining span).writeContext
      (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == window.id) =
        some (window.id,{weakMemory := none, backtrace := (AllocationBacktrace.get
          ((context.extras.get state.machine.user).allocations) window.id)}))
    (addressBound : place.mplace.ptr.offset.bytes.toNat + 1 < 2^64)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩) :
    ∃ updated, (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (Scalar.fromBool value)),RootCompilerFacts.boolLayout⟩ view state =
        (CanonicalCopy.replaceAllocation state window.id window.entry.kind updated,.ok ()) ∧
      updated.byteSize = window.entry.allocation.byteSize ∧ updated.len = window.entry.allocation.len ∧
      updated.mutability = .Mut := by
  obtain ⟨updated, write, size, length, mutable⟩ :=
    write_actual options remaining span limits fuel validationFuel state place window value tracker tracked
      noClocks noBackend ghost shallow source root node found key roots coherent treeBounds owners extras addressBound
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let bound := ExecutionMachine.withValidation config limits
  let placeHooks := (ExecutionMachine.projectionHooks bound).place
  let dest : RuntimePlace Provenance := ⟨.memory place.mplace,place.layout⟩
  let scalar : Immediate Provenance := .scalar (Scalar.fromBool value)
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have destLayout : dest.layout = RootCompilerFacts.boolLayout := window.layout
  have flag := GenericCallReturn.same_layout_transmute_flag placeHooks bound.copy PreparedReflection.actual.compiler ()
    RootCompilerFacts.boolLayout scalar dest destLayout compatible
  have exactCopy : copyRuntimePlace placeHooks bound.copy () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest := by
    rw [flag]; rfl
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.boolLayout
    RootGenericBoolWrite.bool_initialized
  have copy := ActualScalarCopy.actual_copy_scalar options limits (remaining+1) span debugOff
    RootCompilerFacts.boolLayout scalar dest destLayout _ repr RootGenericBoolWrite.bool_sized
  refine ⟨updated, ?_, size, length, mutable⟩
  change MachineHooks.run (copyRuntimePlace placeHooks bound.copy ()
    ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ view.toRuntimePlace true) state = _
  rw [destination, exactCopy, copy]
  unfold MachineHooks.run Call.run
  rw [write]

end DuplicatePrefix.PhysicalBoolWindowActual

#print axioms DuplicatePrefix.PhysicalBoolWindowActual.write_actual
#print axioms DuplicatePrefix.PhysicalBoolWindowActual.copy_return

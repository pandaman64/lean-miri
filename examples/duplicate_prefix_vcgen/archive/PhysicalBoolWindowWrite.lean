import duplicate_prefix.S04ReturnWindowScalar
import duplicate_prefix.S04ReturnPostStorage
import duplicate_prefix.PhysicalMachineWrite

namespace DuplicatePrefix.PhysicalBoolWindowWrite

open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Window (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (place : MPlaceTy Provenance) where
  layout : place.layout = RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned = none
  id : AllocId
  tag : BorTag
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  capacity : UInt64
  live : before.memory.live[id]? = some entry
  cachedBase : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  pointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))
  bounds : offset.toNat+1 ≤ capacity.toNat
  size : entry.allocation.byteSize = Size.ofBytes capacity
  bytes : entry.allocation.len = capacity.toNat
  mutable : entry.allocation.mutability = .Mut
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = Size.ofBytes capacity
  provenance : ∀ pointer ∈ entry.allocation.provenanceMap.ptrs,
    pointer.1.bytes.toNat+8 ≤ entry.allocation.len

theorem on_context_of_access (context : PhysicalMachineWrite.Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : Window state.machine place)
    (tree : BorrowTree) (value : Bool)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (.concrete input.tag) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
        ⟨⟨state.machine,none⟩,tree,.ok ()⟩)
    (resolved : context.access.resolvePointer state.machine.memory
      place.mplace.ptr (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,(.concrete input.tag)⟩) state.machine)
    (willValidate : MemoryOperandLayout → Bool) :
    ∃ updated, PlaceMachine.writeMemory context.access willValidate (.scalar (Scalar.fromBool value)) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := (state.machine.memory.live.insert input.id {input.entry with allocation := updated})}}} ∧
      updated.extra = tree ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Allocation.readScalar updated context.access.runtime.base
        (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value) ∧
      (∀ entry ∈ updated.provenanceMap.ptrs, entry.1.bytes.toNat + 8 ≤ updated.len) := by
  let before := state.machine
  have unsized : place.layout.layout.backendRepr.isUnsized = false := by rw [input.layout]; decide +kernel
  have placeSize : place.layout.layout.size = Size.ofBytes 1 := by rw [input.layout]; decide +kernel
  have abi : immediate_abi (.scalar (Scalar.fromBool value : Scalar Provenance))
      (localMemoryLayout place.layout) context.access.runtime = .ok () := by
    rw [input.layout]; exact PhysicalMachineWrite.bool_abi _ _
  let id := input.id
  let entry := input.entry
  let config := context.access
  let afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {entry with allocation := entry.allocation.setExtra tree}
  let current := RetagEntry.updatedMemory before.memory id entry tree
  have synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
    funext memory view
    exact MemoryCopyBridge.source_globals_synchronize context.prepared context.image context.extras context.globals memory view
  have placeAccess := S04ReturnResolvedWindowMemory.get_place_write_of_access config context.pointers rfl before
    ⟨place.mplace,localMemoryLayout place.layout⟩ input.id (.concrete input.id input.tag) (.concrete input.tag) input.base input.offset 1 input.capacity input.entry tree width (by decide) (by decide) input.cachedBase input.live input.size input.bounds
    input.mutable synchronize rfl access unsized placeSize input.pointer input.aligned runtimeSize (by simpa only [input.pointer] using resolved)
  have currentPresent : current.live[id]? = some afterEntry :=
    MemoryCopyBridge.live_lookup_replaced before.memory id afterEntry
  obtain ⟨updated, mutation, length, bytes, mutability, extra, _, _, _, read, provenanceBounds⟩ :=
    S04ReturnPostStorage.store_and_read afterEntry.allocation config.runtime.base input.capacity input.offset value
      (by rw [runtimeWidth]; rfl) input.bytes input.size input.mutable input.maskValid input.maskLength
      input.provenance input.bounds
  have placeAccess' : getPlaceAllocMut before.memory ⟨before,none⟩
      ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
      (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨current,⟨before,none⟩,some ⟨id,allocRange (Size.ofBytes input.offset) (Size.ofBytes 1),afterEntry.allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes input.offset) (Size.ofBytes 1),afterEntry.allocation⟩)⟩ := by
    simpa only [current, afterEntry] using placeAccess
  have operand := S04ReturnWindowScalar.scalar_write_of_allocation before.memory current
    (PlaceMachine.AccessState.mk before none) (PlaceMachine.AccessState.mk before none)
    ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
    (PlaceMachine.accessHooks config) config.dynamicLayout willValidate input.offset 1 (by have := input.capacity.toNat_lt; have := input.bounds; simpa only [UInt64.toNat_one] using (show input.offset.toNat + 1 < 2^64 by omega)) input.id afterEntry updated (Scalar.fromBool value) unsized abi placeAccess'
    currentPresent (by cases value <;> rfl) mutation
  have memoryEq :
      {current with live := current.live.insert id {afterEntry with allocation := updated}} =
      {before.memory with live := before.memory.live.insert id {entry with allocation := updated}} :=
    MemoryCopyBridge.live_update_twice before.memory id afterEntry {entry with allocation := updated}
  rw [memoryEq] at operand
  refine ⟨updated, ?_, extra, bytes, length, mutability,read,provenanceBounds⟩
  change PlaceMachine.writeMemory config willValidate (.scalar (Scalar.fromBool value)) place state = _
  unfold PlaceMachine.writeMemory
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  have ghostMode : config.ghostMode = false := rfl
  rw [ghostMode]
  rw [operand]
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  have retain : config.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, retain,
    bind, EStateM.bind, pure, EStateM.pure]
  rfl

end DuplicatePrefix.PhysicalBoolWindowWrite

#print axioms DuplicatePrefix.PhysicalBoolWindowWrite.on_context_of_access

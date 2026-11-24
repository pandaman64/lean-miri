import Miri.Verification.ScalarMemoryWP

/-! The execution access hooks supply the selected snapshot. Starting with the
ordinary typed operations, the generated conditions then reduce to mask, byte,
and commit facts for that snapshot. -/
namespace MiriTests.Verification.ScalarMemoryWP

open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Verification.MemoryWP Std.WP

set_option experimental.vcgen true

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "Access" => MemoryOperandResult Provenance BorrowTree K (PlaceMachine.AccessState K U)
  (Option (AllocationAccessRef Provenance BorrowTree))
local notation "Reference" => AllocationAccessRef Provenance BorrowTree

example [DecidableEq K] (config : Config) (before : State)
    (operand : OpTy Provenance) (mplace : MemPlace Provenance)
    (access : Access) (reference : Reference)
    (range : AllocRange) (value : Bool) (validRange : WrappingRange)
    (indirect : operand.op = .indirect mplace)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := .Int .I8 false) (validRange := validRange)))
    (primitiveWidth : (Miri.ABI.Primitive.Int .I8 false).size config.runtime =
      .ok (localMemoryLayout operand.layout).size)
    (accessed : getPlaceAlloc before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = access)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO (localMemoryLayout operand.layout).size) =
      .ok range)
    (width : range.size = Size.ofBytes 1)
    (initialized : reference.allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (bytes : reference.allocation.getBytesUnchecked range = .ok #[if value then 1 else 0]) :
    Triple (PlaceMachine.readImmediate config operand) (· = before)
      (fun loaded after => loaded = ⟨.scalar (Scalar.fromBool value), operand.layout⟩ ∧
        after = {before with machine := (config.retainTouched
          {access.hooks.machine with memory := access.memory} access.touched)})
      (fun _ _ => False) := by
  vcgen
  rename_i state entry
  subst state
  rw [immediateReadPre_iff, readImmediate_iff, indirect]
  rw [scalarRead_eq_afterAccess _ _ ⟨mplace, localMemoryLayout operand.layout⟩
    _ _ _ _ _ _ (.Int .I8 false) validRange backend primitiveWidth, accessed]
  have load := readBool_of_bytes reference.allocation config.runtime.base range value width initialized bytes (.inl rfl)
  simp only [scalarReadAfterAccess_of_read _ (.Int .I8 false) config.runtime _ reference range _ selected component load,
    Except.mapError, Except.map, resultPre, and_self]

example [DecidableEq K] (config : Config) (before : State)
    (later : MemoryOperandLayout → Bool) (place : MPlaceTy Provenance)
    (access : Access) (reference : Reference) (range : AllocRange) (value : Bool)
    (entry : LocalAllocation Provenance BorrowTree K) (cleared : ProvenanceMap Provenance)
    (sized : (localMemoryLayout place.layout).backendRepr.isUnsized = false)
    (abi : immediateMatchesAbi (.scalar (Scalar.fromBool (Prov := Provenance) value)) (localMemoryLayout place.layout)
      config.runtime = .ok ())
    (accessed : getPlaceAllocMut before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = access)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO (Scalar.fromBool (Prov := Provenance) value).size) =
      .ok range)
    (present : access.memory.live[reference.allocId]? = some entry)
    (width : range.size = Size.ofBytes 1)
    (storage : reference.allocation.len = reference.allocation.byteSize.bytes.toNat)
    (mutable : reference.allocation.mutability = .Mut)
    (maskLength : reference.allocation.initializationMask.len = reference.allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed reference.allocation.initializationMask)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ reference.allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      reference.allocation.getBytesUnchecked (allocRange Size.ZERO reference.allocation.byteSize) = .ok fullBytes →
      reference.allocation.provenanceMap.clear range fullBytes
        (Size.fromBits config.runtime.base.pointerWidth.bits) = .ok () cleared) :
    Triple (PlaceMachine.writeMemory config later (.scalar (Scalar.fromBool value)) place) (· = before)
      (fun () after => ∃ updated,
        updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
        updated.getBytesUnchecked range = .ok #[if value then 1 else 0] ∧
        after = {before with machine := (config.retainTouched
          {access.hooks.machine with memory :=
            {access.memory with live := (access.memory.live.insert reference.allocId
              {entry with allocation := updated})}}
          (some {reference with allocation := updated}))})
      (fun _ _ => False) := by
  vcgen
  rename_i state initial
  subst state
  rw [immediateWritePre_iff, writeMemory_iff]
  rw [immediateWrite_eq_afterAccess _ _ _ _ _ _ _ _ _ _ _ sized abi, accessed]
  obtain ⟨updated, store, _, _, _, _, initialized, bytes⟩ :=
    writeBool_of_bytes reference.allocation config.runtime.base range value cleared width storage
      mutable maskLength maskValid bound clear
  have committed := access.memory.setLiveAllocation_of_find reference.allocId entry updated present
  rw [scalarWriteAfterAccess_of_mutation _ _ _ _ reference range _ updated _ (.ok ())
    selected component store committed]
  exact ⟨updated, initialized, bytes, rfl⟩

/-- A four-byte store initializes the selected cells, clears the actual
provenance overlap, and commits the target-endian bytes to live memory. -/
example [DecidableEq K] (config : Config) (before : State)
    (later : MemoryOperandLayout → Bool) (place : MPlaceTy Provenance)
    (access : Access) (reference : Reference) (range : AllocRange)
    (value : Scalar Provenance) (bits : U128)
    (entry : LocalAllocation Provenance BorrowTree K) (cleared : ProvenanceMap Provenance)
    (sized : (localMemoryLayout place.layout).backendRepr.isUnsized = false)
    (abi : immediateMatchesAbi (.scalar value) (localMemoryLayout place.layout) config.runtime = .ok ())
    (accessed : getPlaceAllocMut before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = access)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO value.size) = .ok range)
    (present : access.memory.live[reference.allocId]? = some entry)
    (width : range.size = Size.ofBytes 4)
    (storage : reference.allocation.len = reference.allocation.byteSize.bytes.toNat)
    (mutable : reference.allocation.mutability = .Mut)
    (maskLength : reference.allocation.initializationMask.len = reference.allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed reference.allocation.initializationMask)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ reference.allocation.byteSize.bytes.toNat)
    (converted : value.toBitsOrPtrInternal range.size = .ok (.bits bits))
    (clear : ∀ fullBytes : Array UInt8,
      reference.allocation.getBytesUnchecked (allocRange Size.ZERO reference.allocation.byteSize) = .ok fullBytes →
      reference.allocation.provenanceMap.clear range fullBytes
        (Size.fromBits config.runtime.base.pointerWidth.bits) = .ok () cleared)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    wp (PlaceMachine.writeMemory config later (.scalar value) place) post onError before ↔
      ∃ updated,
        Allocation.writeScalar config.runtime.base range value reference.allocation = .ok () updated ∧
        updated.provenanceMap = cleared ∧
        updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
        updated.getBytesUnchecked range = .ok (scalarBytes config.runtime.base range.size bits.toNat) ∧
        post () {before with machine := (config.retainTouched
          {access.hooks.machine with memory :=
            {access.memory with live := (access.memory.live.insert reference.allocId
              {entry with allocation := updated})}}
          (some {reference with allocation := updated}))} := by
  rw [scalarWrite_access_iff config before later place value access sized abi accessed]
  obtain ⟨updated, store, _, _, _, provenance, initialized, bytes⟩ :=
    writeInt_of_bytes reference.allocation config.runtime.base range value bits cleared storage
      mutable maskLength maskValid (by rw [width]; decide) (by rw [width]; decide) bound converted clear
  rw [scalarStore_resultPre_iff config before _ later access reference range value updated _ (.ok ())
    selected component store (access.memory.setLiveAllocation_of_find reference.allocId entry updated present)]
  constructor
  · exact fun success => ⟨updated, store, provenance, initialized, bytes, success⟩
  · rintro ⟨actual, actualStore, _, _, _, success⟩
    have same : updated = actual := by
      rw [store] at actualStore
      cases actualStore
      rfl
    simpa only [same] using success

/-- An integer load reconstructs the same four-byte scalar for either
target byte order. -/
example [DecidableEq K] (config : Config) (before : State) (layout : MemoryOperandLayout)
    (access : Access) (reference : Reference) (range : AllocRange)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO layout.size) = .ok range)
    (initialized : reference.allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (width : range.size = Size.ofBytes 4)
    (bytes : reference.allocation.getBytesUnchecked range =
      .ok (if config.runtime.base.endian == .little then #[0x78, 0x56, 0x34, 0x12]
        else #[0x12, 0x34, 0x56, 0x78]))
    (value : Scalar Provenance)
    (converted : Scalar.fromUInt 0x12345678 (Size.ofBytes 4) = .ok value)
    (post : ImmediateValue Provenance → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (scalarReadAfterAccess layout (.Int .I32 false) config.runtime access)
        post onError ↔
      post ⟨.scalar value, layout⟩ {before with machine := (config.retainTouched
        {access.hooks.machine with memory := access.memory} access.touched)} := by
  have serialized : scalarBytes config.runtime.base range.size (0x12345678 : U128).toNat =
      if config.runtime.base.endian == .little then #[0x78, 0x56, 0x34, 0x12]
        else #[0x12, 0x34, 0x56, 0x78] := by
    rw [width]
    unfold scalarBytes
    cases config.runtime.base.endian <;> decide
  exact scalarLoad_int_resultPre_iff config before layout .I32 false access reference range 0x12345678
    selected component initialized (by rw [width]; decide) (by rw [width]; decide)
    (by rw [serialized]; exact bytes) value (by rw [width]; exact converted) post onError

/-- Pointer loads use both bytes and the provenance found by the access. -/
example [DecidableEq K] (config : Config) (before : State)
    (operand : OpTy Provenance) (mplace : MemPlace Provenance)
    (addressSpace : AddressSpace) (validRange : WrappingRange)
    (access : Access) (reference : Reference) (range : AllocRange) (pointer : Pointer Provenance)
    (indirect : operand.op = .indirect mplace)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := .Pointer addressSpace) (validRange := validRange)))
    (primitiveWidth : (Miri.ABI.Primitive.Pointer addressSpace).size config.runtime =
      .ok (localMemoryLayout operand.layout).size)
    (accessed : getPlaceAlloc before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = access)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO (localMemoryLayout operand.layout).size) =
      .ok range)
    (initialized : reference.allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (pointerWidth : range.size = Size.fromBits config.runtime.base.pointerWidth.bits)
    (width : range.size.bytes.toNat ≤ 16)
    (fits : pointer.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (provenance : reference.allocation.provenanceMap.readPtr range.start
      (Size.fromBits config.runtime.base.pointerWidth.bits) = .ok (some pointer.provenance))
    (bytes : reference.allocation.getBytesUnchecked range =
      .ok (scalarBytes config.runtime.base range.size pointer.offset.bytes.toNat))
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    wp (PlaceMachine.readImmediate config operand) post onError before ↔
      post ⟨.scalar (Scalar.fromPointer config.runtime.base pointer), operand.layout⟩
        {before with machine := (config.retainTouched
          {access.hooks.machine with memory := access.memory} access.touched)} := by
  rw [scalarRead_access_iff config before operand mplace (.Pointer addressSpace) validRange access
    indirect backend primitiveWidth accessed]
  exact scalarLoad_pointer_resultPre_iff config before _ addressSpace access reference range pointer
    selected component initialized pointerWidth width fits provenance bytes _ onError

/-- A successful pointer store commits the offset bytes and the provenance
insertion in the same live allocation. -/
example [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (later : MemoryOperandLayout → Bool)
    (access : Access) (reference : Reference) (range : AllocRange) (pointer : Pointer Provenance)
    (entry : LocalAllocation Provenance BorrowTree K) (cleared inserted : ProvenanceMap Provenance)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO
      (Scalar.fromPointer config.runtime.base pointer).size) = .ok range)
    (present : access.memory.live[reference.allocId]? = some entry)
    (pointerWidth : range.size = Size.fromBits config.runtime.base.pointerWidth.bits)
    (storage : reference.allocation.len = reference.allocation.byteSize.bytes.toNat)
    (mutable : reference.allocation.mutability = .Mut)
    (maskLength : reference.allocation.initializationMask.len = reference.allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed reference.allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ reference.allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      reference.allocation.getBytesUnchecked (allocRange Size.ZERO reference.allocation.byteSize) = .ok fullBytes →
      reference.allocation.provenanceMap.clear range fullBytes
        (Size.fromBits config.runtime.base.pointerWidth.bits) = .ok () cleared)
    (insert : cleared.insertPtr range.start pointer.provenance
      (Size.fromBits config.runtime.base.pointerWidth.bits) = .ok () inserted)
    (onError : StepError → State → Prop) :
    resultPre config before
      (writeImmediateAfterAccess (.scalar (Scalar.fromPointer config.runtime.base pointer))
        layout config.runtime later access)
      (fun () after => ∃ updated,
        updated.provenanceMap = inserted ∧
        updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
        updated.getBytesUnchecked range =
          .ok (scalarBytes config.runtime.base range.size pointer.offset.bytes.toNat) ∧
        after = {before with machine := (config.retainTouched
          {access.hooks.machine with memory :=
            {access.memory with live := (access.memory.live.insert reference.allocId
              {entry with allocation := updated})}}
          (some {reference with allocation := updated}))}) onError := by
  obtain ⟨updated, store, provenance, initialized, bytes⟩ :=
    writePointer_of_bytes reference.allocation config.runtime.base range pointer cleared inserted
      pointerWidth storage mutable maskLength maskValid nonzero width bound clear insert
  rw [scalarStore_resultPre_iff config before layout later access reference range _ updated _ (.ok ())
    selected component store (access.memory.setLiveAllocation_of_find reference.allocId entry updated present)]
  exact ⟨updated, provenance, initialized, bytes, rfl⟩

/-- An uninitialized part of a multi-byte scalar yields the exact error and
touched snapshot, with a pending hook error taking precedence. -/
example [DecidableEq K] (config : Config) (before : State)
    (operand : OpTy Provenance) (mplace : MemPlace Provenance) (validRange : WrappingRange)
    (access : Access) (reference : Reference) (range bad : AllocRange)
    (indirect : operand.op = .indirect mplace)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := .Int .I32 false) (validRange := validRange)))
    (primitiveWidth : (Miri.ABI.Primitive.Int .I32 false).size config.runtime =
      .ok (localMemoryLayout operand.layout).size)
    (accessed : getPlaceAlloc before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = access)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO (localMemoryLayout operand.layout).size) =
      .ok range)
    (uninitialized : reference.allocation.initializationMask.isRangeInitialized range = .ok (.error bad))
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    wp (PlaceMachine.readImmediate config operand) post onError before ↔
    onError (access.hooks.pendingError.getD
      (config.memoryError (.allocation (.invalidUninitBytes (some ⟨range, bad⟩)))))
      {before with machine := (config.retainTouched
        {access.hooks.machine with memory := access.memory} access.touched)} := by
  rw [scalarRead_access_iff config before operand mplace (.Int .I32 false) validRange access
    indirect backend primitiveWidth accessed]
  exact scalarLoad_uninit_resultPre_iff config before _ (.Int .I32 false) access reference range bad
    selected component uninitialized _ onError

/-- A scalar mutation can fail after an allocation change. The error
continuation receives the committed partial allocation. -/
example [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (later : MemoryOperandLayout → Bool)
    (access : Access) (reference : Reference) (range : AllocRange)
    (value : Scalar Provenance) (error : AllocError) (partialAllocation : Allocation Provenance BorrowTree)
    (memory : MemoryState Provenance BorrowTree K)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO value.size) = .ok range)
    (store : Allocation.writeScalar config.runtime.base range value reference.allocation =
      .error error partialAllocation)
    (committed : access.memory.setLiveAllocation reference.allocId partialAllocation = .ok memory)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (writeImmediateAfterAccess (.scalar value) layout config.runtime later access)
      post onError ↔
    onError (access.hooks.pendingError.getD (config.memoryError (.allocation error)))
      {before with machine := (config.retainTouched {access.hooks.machine with memory}
        (some {reference with allocation := partialAllocation}))} :=
  scalarStore_resultPre_iff config before layout later access reference range value
    partialAllocation memory (.error error) selected component store committed post onError

#print axioms scalarRead_access_iff
#print axioms scalarWrite_access_iff
#print axioms scalarLoad_int_resultPre_iff
#print axioms scalarLoad_pointer_resultPre_iff
#print axioms scalarLoad_uninit_resultPre_iff
#print axioms scalarStore_resultPre_iff
#print axioms writeInt_of_bytes
#print axioms writePointer_of_bytes

#print axioms readBool_of_bytes
#print axioms writeBool_of_bytes
#print axioms scalarReadAfterAccess_of_read
#print axioms scalarWriteAfterAccess_of_mutation

end MiriTests.Verification.ScalarMemoryWP

import Miri.Memory.AllocationVerification
import Miri.Verification.MemoryWP

/-! Byte-level refinements for scalar memory operands. -/
namespace Miri.Verification.MemoryWP

open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Std.WP

/-- The target-endian byte representation of the low bits at the given width. -/
def scalarBytes (layout : TargetDataLayout) (width : Size) (bits : Nat) : Array UInt8 :=
  Array.ofFn (fun i : Fin width.bytes.toNat =>
    UInt8.ofNat ((bits / 2 ^ (8 *
      (if layout.endian == .little then i.1 else width.bytes.toNat - i.1 - 1))) % 256))

variable {K U : Type}
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "State" => MachineHooks.State K U
local notation "Access" => MemoryOperandResult Provenance BorrowTree K (PlaceMachine.AccessState K U)
  (Option (AllocationAccessRef Provenance BorrowTree))
local notation "Reference" => AllocationAccessRef Provenance BorrowTree

/-- Refine a typed indirect load to its scalar continuation after the
specified access from the initial machine state. -/
theorem scalarRead_access_iff [DecidableEq K] (config : Config) (before : State)
    (operand : OpTy Provenance) (mplace : MemPlace Provenance) (primitive : BackendPrimitive)
    (validRange : WrappingRange) (access : Access)
    (indirect : operand.op = .indirect mplace)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.runtime = .ok (localMemoryLayout operand.layout).size)
    (accessed : getPlaceAlloc before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = access)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    wp (PlaceMachine.readImmediate config operand) post onError before ↔
      resultPre config before
        (scalarReadAfterAccess (localMemoryLayout operand.layout) primitive config.runtime access)
        (fun value => post ⟨value.value, operand.layout⟩) onError := by
  rw [readImmediate_iff, indirect, scalarRead_eq_afterAccess _ _
    ⟨mplace, localMemoryLayout operand.layout⟩ _ _ _ _ _ _ primitive validRange backend width, accessed]

/-- Refine a typed scalar store to its mutation and commit continuation after
the specified access from the initial machine state. -/
theorem scalarWrite_access_iff [DecidableEq K] (config : Config) (before : State)
    (later : MemoryOperandLayout → Bool) (place : MPlaceTy Provenance)
    (value : Scalar Provenance) (access : Access)
    (sized : (localMemoryLayout place.layout).backendRepr.isUnsized = false)
    (abi : immediateMatchesAbi (.scalar value) (localMemoryLayout place.layout) config.runtime = .ok ())
    (accessed : getPlaceAllocMut before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = access)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    wp (PlaceMachine.writeMemory config later (.scalar value) place) post onError before ↔
      resultPre config before
        (writeImmediateAfterAccess (.scalar value) (localMemoryLayout place.layout) config.runtime later access)
        post onError := by
  rw [writeMemory_iff, immediateWrite_eq_afterAccess _ _ _ _ _ _ _ _ _ _ _ sized abi, accessed]

/-- Pull either result of the selected scalar load back to the exact retained
machine state. The error continuation observes the hook's pending error first. -/
theorem scalarLoad_resultPre_iff [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (primitive : BackendPrimitive)
    (access : Access) (reference : Reference) (range : AllocRange)
    (result : Except AllocError (Scalar Provenance))
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO layout.size) = .ok range)
    (load : reference.allocation.readScalar config.runtime.base range
      (match primitive with | .Pointer _ => true | _ => false) = result)
    (post : ImmediateValue Provenance → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (scalarReadAfterAccess layout primitive config.runtime access) post onError ↔
      let after := {before with machine := (config.retainTouched
        {access.hooks.machine with memory := access.memory} access.touched)}
      match result with
      | .ok value => post ⟨.scalar value, layout⟩ after
      | .error error =>
        onError (access.hooks.pendingError.getD (config.memoryError (.allocation error))) after := by
  rw [scalarReadAfterAccess_of_read _ _ _ _ _ _ _ selected component load]
  cases result <;> rfl

/-- A successful or partially failed scalar mutation leaves the committed
allocation in both the live map and the touched snapshot. -/
theorem scalarStore_resultPre_iff [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (later : MemoryOperandLayout → Bool)
    (access : Access) (reference : Reference) (range : AllocRange) (value : Scalar Provenance)
    (updated : Allocation Provenance BorrowTree) (memory : MemoryState Provenance BorrowTree K)
    (result : Except AllocError Unit)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO value.size) = .ok range)
    (store : Allocation.writeScalar config.runtime.base range value reference.allocation =
      match result with | .ok () => .ok () updated | .error error => .error error updated)
    (committed : access.memory.setLiveAllocation reference.allocId updated = .ok memory)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (writeImmediateAfterAccess (.scalar value) layout config.runtime later access)
        post onError ↔
      let after := {before with machine := (config.retainTouched {access.hooks.machine with memory}
        (some {reference with allocation := updated}))}
      match result with
      | .ok () => post () after
      | .error error =>
        onError (access.hooks.pendingError.getD (config.memoryError (.allocation error))) after := by
  rw [scalarWriteAfterAccess_of_mutation _ _ _ _ _ _ _ _ _ _ selected component store committed]
  cases result with
  | ok value => cases value; rfl
  | error => rfl

/-- An initialized integer operand specified by its target-endian bytes. -/
theorem scalarLoad_int_resultPre_iff [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (intWidth : Integer) (signed : Bool)
    (access : Access) (reference : Reference) (range : AllocRange) (bits : U128)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO layout.size) = .ok range)
    (initialized : reference.allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (width : range.size.bytes.toNat ≤ 16)
    (fits : bits.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (bytes : reference.allocation.getBytesUnchecked range =
      .ok (scalarBytes config.runtime.base range.size bits.toNat))
    (value : Scalar Provenance)
    (converted : Scalar.fromUInt bits range.size = .ok value)
    (post : ImmediateValue Provenance → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (scalarReadAfterAccess layout (.Int intWidth signed) config.runtime access)
        post onError ↔
      post ⟨.scalar value, layout⟩ {before with machine := (config.retainTouched
        {access.hooks.machine with memory := access.memory} access.touched)} := by
  have load := reference.allocation.readScalar_int_roundtrip config.runtime.base range bits
    initialized width fits (.inl rfl) bytes
  rw [converted] at load
  exact scalarLoad_resultPre_iff config before layout (.Int intWidth signed) access reference range
    (.ok value) selected component load post onError

/-- A pointer operand combines the serialized offset with the provenance
returned by the allocation's pointer-width lookup. -/
theorem scalarLoad_pointer_resultPre_iff [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (addressSpace : AddressSpace)
    (access : Access) (reference : Reference) (range : AllocRange) (pointer : Pointer Provenance)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO layout.size) = .ok range)
    (initialized : reference.allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (pointerWidth : range.size = Size.fromBits config.runtime.base.pointerWidth.bits)
    (width : range.size.bytes.toNat ≤ 16)
    (fits : pointer.offset.bytes.toNat < 2 ^ (8 * range.size.bytes.toNat))
    (provenance : reference.allocation.provenanceMap.readPtr range.start
      (Size.fromBits config.runtime.base.pointerWidth.bits) = .ok (some pointer.provenance))
    (bytes : reference.allocation.getBytesUnchecked range =
      .ok (scalarBytes config.runtime.base range.size pointer.offset.bytes.toNat))
    (post : ImmediateValue Provenance → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (scalarReadAfterAccess layout (.Pointer addressSpace) config.runtime access)
        post onError ↔
      post ⟨.scalar (Scalar.fromPointer config.runtime.base pointer), layout⟩
        {before with machine := (config.retainTouched
          {access.hooks.machine with memory := access.memory} access.touched)} :=
  scalarLoad_resultPre_iff config before layout (.Pointer addressSpace) access reference range _
    selected component (reference.allocation.readScalar_ptr_roundtrip config.runtime.base range pointer
      initialized pointerWidth width fits provenance bytes) post onError

/-- The first failing initialization subrange determines the allocation error
on any scalar load, including pointer loads. -/
theorem scalarLoad_uninit_resultPre_iff [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (primitive : BackendPrimitive)
    (access : Access) (reference : Reference) (range bad : AllocRange)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO layout.size) = .ok range)
    (uninitialized : reference.allocation.initializationMask.isRangeInitialized range = .ok (.error bad))
    (post : ImmediateValue Provenance → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (scalarReadAfterAccess layout primitive config.runtime access) post onError ↔
      onError (access.hooks.pendingError.getD
        (config.memoryError (.allocation (.invalidUninitBytes (some ⟨range, bad⟩)))))
        {before with machine := (config.retainTouched
          {access.hooks.machine with memory := access.memory} access.touched)} :=
  scalarLoad_resultPre_iff config before layout primitive access reference range _
    selected component (reference.allocation.readScalar_uninit_err config.runtime.base range bad
      _ uninitialized) post onError

/-- A successful integer store serializes all bytes in the selected range,
marks the range initialized, and uses the provenance map produced by clearing
overlaps. See `Allocation.writeScalar_spec` for the disjoint-byte frame. -/
theorem writeInt_of_bytes {P E : Type} (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (value : Scalar P) (bits : U128) (cleared : ProvenanceMap P)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal range.size = .ok (.bits bits))
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared) :
    ∃ updated, Allocation.writeScalar layout range value allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.extra = allocation.extra ∧ updated.provenanceMap = cleared ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.getBytesUnchecked range = .ok (scalarBytes layout range.size bits.toNat) := by
  obtain ⟨updated, store, size, len, _, _, extra, _, _, _, _, initialized, provenance, bytes, _, _⟩ :=
    Allocation.writeScalar_spec layout allocation range value (.bits bits) cleared cleared
      storage mutable maskLength maskValid nonzero width bound conversion clear rfl
  exact ⟨updated, store, size, len, extra, provenance, initialized, bytes bits rfl⟩

/-- A pointer store writes the target-endian offset and inserts its
provenance after clearing the overwritten range. -/
theorem writePointer_of_bytes {P E : Type} (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (pointer : Pointer P) (cleared inserted : ProvenanceMap P)
    (pointerWidth : range.size = Size.fromBits layout.pointerWidth.bits)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (nonzero : range.size.bytes ≠ 0)
    (width : range.size.bytes.toNat ≤ 16)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (insert : cleared.insertPtr range.start pointer.provenance
      (Size.fromBits layout.pointerWidth.bits) = .ok () inserted) :
    ∃ updated, Allocation.writeScalar layout range (Scalar.fromPointer layout pointer) allocation =
        .ok () updated ∧
      updated.provenanceMap = inserted ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.getBytesUnchecked range = .ok (scalarBytes layout range.size pointer.offset.bytes.toNat) := by
  have conversion : (Scalar.fromPointer layout pointer).toBitsOrPtrInternal range.size =
      .ok (.pointer pointer) := by
    rw [pointerWidth]
    unfold Scalar.toBitsOrPtrInternal
    change (if (Size.fromBits layout.pointerWidth.bits != Size.fromBits layout.pointerWidth.bits) = true
      then _ else _) = _
    rw [bne_self_eq_false]
    rfl
  obtain ⟨updated, store, _, _, _, _, _, _, _, _, _, initialized, provenance, _, bytes, _⟩ :=
    Allocation.writeScalar_spec layout allocation range (Scalar.fromPointer layout pointer)
      (.pointer pointer) cleared inserted storage mutable maskLength maskValid nonzero width bound
      conversion clear ⟨pointerWidth, insert⟩
  have offsetFits : pointer.offset.bytes.toNat < 2 ^ 128 :=
    Nat.lt_trans pointer.offset.bytes.toNat_lt (by decide)
  have storedBytes := bytes pointer rfl
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetFits] at storedBytes
  exact ⟨updated, store, provenance, initialized, storedBytes⟩

private theorem boolByteEncoding (layout : TargetDataLayout) (value : Bool) :
    scalarBytes layout (Size.ofBytes 1) (if value then (1 : U128) else 0).toNat =
      #[if value then 1 else 0] := by
  unfold scalarBytes
  cases value <;> cases layout.endian <;> decide

/-- A scalar load from an initialized Boolean byte produces the Boolean
immediate for either byte order. A non-address provenance mode requires
the same empty-overlap check as the interpreter. -/
theorem readBool_of_bytes {P E : Type} [DecidableEq P] [PointerProvenance P]
    (allocation : Allocation P E) (layout : TargetDataLayout) (range : AllocRange) (value : Bool)
    (width : range.size = Size.ofBytes 1)
    (initialized : allocation.initializationMask.isRangeInitialized range = .ok (.ok ()))
    (bytes : allocation.getBytesUnchecked range = .ok #[if value then 1 else 0])
    (provenance : PointerProvenance.offsetIsAddr (Prov := P) = true ∨
      allocation.provenanceMap.rangeEmpty range (Size.fromBits layout.pointerWidth.bits) = .ok true) :
    allocation.readScalar layout range false = .ok (Scalar.fromBool value) := by
  rw [allocation.readScalar_int_of_bytes layout range _ initialized bytes (by simp) provenance, width]
  cases value <;> cases layout.endian <;> rfl

/-- The scalar write specification specialized to a Boolean byte. The
selected range becomes initialized and contains the serialized value.
Provenance is the actual result of clearing that range. -/
theorem writeBool_of_bytes {P E : Type} (allocation : Allocation P E) (layout : TargetDataLayout)
    (range : AllocRange) (value : Bool) (cleared : ProvenanceMap P)
    (width : range.size = Size.ofBytes 1)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (bound : range.start.bytes.toNat + range.size.bytes.toNat ≤ allocation.byteSize.bytes.toNat)
    (clear : ∀ fullBytes : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok fullBytes →
      allocation.provenanceMap.clear range fullBytes
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared) :
    ∃ updated, Allocation.writeScalar layout range (Scalar.fromBool value) allocation = .ok () updated ∧
      updated.byteSize = allocation.byteSize ∧ updated.len = allocation.len ∧
      updated.extra = allocation.extra ∧ updated.provenanceMap = cleared ∧
      updated.initializationMask.isRangeInitialized range = .ok (.ok ()) ∧
      updated.getBytesUnchecked range = .ok #[if value then 1 else 0] := by
  have conversion : (Scalar.fromBool value : Scalar P).toBitsOrPtrInternal range.size =
      .ok (.bits (if value then 1 else 0)) := by
    rw [width]
    cases value <;> rfl
  obtain ⟨updated, store, size, len, extra, provenance, initialized, bytes⟩ :=
    writeInt_of_bytes allocation layout range (Scalar.fromBool value) (if value then 1 else 0)
      cleared storage mutable maskLength maskValid (by rw [width]; decide)
      (by rw [width]; decide) bound conversion clear
  rw [width, boolByteEncoding] at bytes
  exact ⟨updated, store, size, len, extra, provenance, initialized, bytes⟩

end Miri.Verification.MemoryWP

import Miri.Verification.ExactWP

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

/-- The memory error uses the same touched snapshot, with an already pending
hook error taking precedence. -/
example [DecidableEq K] (config : Config) (before : State)
    (layout : MemoryOperandLayout) (access : Access) (reference : Reference)
    (range : AllocRange) (error : AllocError)
    (selected : access.outcome = .ok (some reference))
    (component : reference.range.subrange (allocRange Size.ZERO layout.size) = .ok range)
    (load : reference.allocation.readScalar config.runtime.base range false = .error error)
    (post : ImmediateValue Provenance → State → Prop) (onError : StepError → State → Prop) :
    resultPre config before (scalarReadAfterAccess layout (.Int .I8 false) config.runtime access)
      post onError ↔
    onError (access.hooks.pendingError.getD (config.memoryError (.allocation error)))
      {before with machine := (config.retainTouched
        {access.hooks.machine with memory := access.memory} access.touched)} := by
  simp only [scalarReadAfterAccess_of_read _ (.Int .I8 false) config.runtime _ reference range _ selected component load,
    Except.mapError, Except.map, resultPre]

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
        (some {reference with allocation := partialAllocation}))} := by
  simp only [scalarWriteAfterAccess_of_mutation _ _ _ _ reference range value partialAllocation memory
    (.error error) selected component store committed, Except.mapError, resultPre]

#print axioms readBool_of_bytes
#print axioms writeBool_of_bytes
#print axioms scalarReadAfterAccess_of_read
#print axioms scalarWriteAfterAccess_of_mutation

end MiriTests.Verification.ScalarMemoryWP

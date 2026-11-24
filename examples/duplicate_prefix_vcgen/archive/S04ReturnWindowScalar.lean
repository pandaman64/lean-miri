import duplicate_prefix.S04ReturnResolvedWindowMemory

namespace DuplicatePrefix.S04ReturnWindowScalar
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem subrange_window (offset count : UInt64) (fits : offset.toNat + count.toNat < 2^64) :
    (allocRange (Size.ofBytes offset) (Size.ofBytes count)).subrange
      (allocRange Size.ZERO (Size.ofBytes count)) =
      .ok (allocRange (Size.ofBytes offset) (Size.ofBytes count)) := by
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes offset) count (by simpa [Size.ofBytes] using fits)
  simp [AllocRange.subrange, allocRange, Size.add, Size.ZERO, Size.ofBytes,
    Except.mapError, bind, Except.bind, pure, Except.pure] at endpoint ⊢
  simp [endpoint]

theorem scalar_write_of_allocation {Prov Extra K S PX : Type} [DecidableEq K] [DecidableEq Prov] [PointerProvenance Prov]
    (memory current : MemoryState Prov Extra K) (hooks afterHooks : S)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghost : Bool) (globalKind : Option K)
    (globals : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX)
    (dynamic : DynamicLayoutResolver Prov Extra K S) (validate : MemoryOperandLayout → Bool)
    (offset count : UInt64) (fits : offset.toNat + count.toNat < 2^64)
    (id : AllocId) (entry : LocalAllocation Prov Extra K) (updated : Allocation Prov Extra)
    (value : Scalar Prov)
    (sized : place.layout.backendRepr.isUnsized = false)
    (abi : immediate_abi (.scalar value) place.layout runtime = .ok ())
    (access : getPlaceAllocMut memory hooks place runtime ghost globalKind globals accessHooks dynamic =
      ⟨current,afterHooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩)⟩)
    (present : current.live[id]? = some entry)
    (valueSize : value.size = Size.ofBytes count)
    (mutation : Allocation.writeScalar runtime.base (allocRange (Size.ofBytes offset) (Size.ofBytes count)) value entry.allocation =
      .ok () updated) :
    writeImmediateToMplaceNoValidate memory hooks (.scalar value) place runtime ghost globalKind globals accessHooks dynamic validate =
      ⟨{current with live := current.live.insert id {entry with allocation := updated}},
        afterHooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),updated⟩,.ok ()⟩ := by
  have stored := MemoryCopyBridge.set_live_exact current id entry updated present
  unfold writeImmediateToMplaceNoValidate
  simp only [sized, abi, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [access]
  unfold writeImmediateAfterAccess
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Miri.Interpreter.writeScalarAt"
  unfold_internal ".Miri.Interpreter.writeRange"
  simp only [valueSize, subrange_window offset count fits, Except.mapError, Bind.bind, Pure.pure, Except.bind, Except.pure, Id.instMonad]
  erw [mutation]
  unfold_internal ".Miri.Interpreter.commitAllocationMutation"
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  erw [stored]
  rfl

end DuplicatePrefix.S04ReturnWindowScalar

#print axioms DuplicatePrefix.S04ReturnWindowScalar.scalar_write_of_allocation

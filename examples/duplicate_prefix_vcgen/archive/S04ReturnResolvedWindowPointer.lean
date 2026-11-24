import duplicate_prefix.PhysicalScalarReturn
import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.RetagEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnResolvedWindowPointer
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows

theorem get_ptr_write_of_access {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (provenance : Provenance) (extra : ProvenanceExtra) (base offset count capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat + count.toNat ≤ capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (before : config.beforeAllocationAccess = fun _ => pure ())
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id extra
      (allocRange (Size.ofBytes offset) (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩)
    (resolved : config.resolvePointer machine.memory
      (Pointer.new (some provenance) (Size.ofBytes (base + offset))) (Int.ofNat count.toNat) machine =
      .ok (.ok ⟨id,Size.ofBytes offset,extra⟩) machine) :
    AllocationAccess.getPtrAllocMut machine.memory ⟨machine,none⟩ ⟨Size.ofBytes 8⟩
      (Pointer.new (some provenance) (Size.ofBytes (base + offset))) (Size.ofBytes count) false
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config) =
      ⟨RetagEntry.updatedMemory machine.memory id entry tree, ⟨machine,none⟩,
        some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩)⟩ := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes count) signedFits
  change sizeAsI64 (Size.ofBytes count) = .ok (Int.ofNat count.toNat) at signed
  have nonzero : (Int.ofNat count.toNat != 0) = true := by
    have positiveNat : 0 < count.toNat := by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
    simp only [bne_iff_ne]
    change (count.toNat : Int) ≠ 0
    omega
  have raw := MemoryCopyBridge.get_raw_mut_live machine.memory (PlaceMachine.AccessState.mk machine none) id entry
    config.globalKind config.globalHooks present mutable
  simp only [synchronize] at raw
  have checked := DuplicatePrefix.checkedBounds_ok ⟨Size.ofBytes 8⟩ id entry.allocation.byteSize (Size.ofBytes offset)
    count.toNat .memoryAccess signedFits (by simpa [size, Size.ofBytes] using bounds)
  have stored := MemoryCopyBridge.set_live_exact machine.memory id entry (entry.allocation.setExtra tree) present
  have contains := MemoryCopyBridge.live_any_of_present machine.memory id entry present
  let ptr : Pointer (Option Provenance) := Pointer.new (some provenance) (Size.ofBytes (base + offset))
  let hooks : PlaceMachine.AccessState K (ValidityMachine.UserState U) := ⟨machine, none⟩
  let resolvedPointer : ResolvedPointer ProvenanceExtra := ⟨id, Size.ofBytes offset, extra⟩
  have resolveHook :
      (PlaceMachine.accessHooks config).resolvePointer machine.memory hooks ptr (Int.ofNat count.toNat) =
        ⟨hooks, .ok (.ok resolvedPointer)⟩ := by
    simp only [PlaceMachine.accessHooks, PlaceMachine.bridge, hooks, ptr, resolvedPointer, resolved]
  have beforeHook : (PlaceMachine.accessHooks config).beforeAllocationAccess hooks id =
      ⟨hooks, .ok ()⟩ := by
    simp only [PlaceMachine.accessHooks, PlaceMachine.bridge, hooks, before, pure, EStateM.pure]
  have performed := AllocationAccess.getPtrAlloc_checked true machine.memory machine.memory
    hooks hooks hooks hooks ⟨Size.ofBytes 8⟩ ptr (Size.ofBytes count) config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) resolvedPointer resolvedPointer entry.allocation
    (Int.ofNat count.toNat) hooks signed (bne_iff_ne.mp nonzero) resolveHook raw checked
    (by intro contradictory; cases contradictory) beforeHook
  simp only [↓reduceIte] at performed
  change AllocationAccess.getPtrAllocMut machine.memory hooks ⟨Size.ofBytes 8⟩ ptr
    (Size.ofBytes count) false config.globalKind config.globalHooks (PlaceMachine.accessHooks config) = _
  rw [performed]
  dsimp only [AllocationAccess.finishCheckedAccess, PlaceMachine.accessHooks, hooks, resolvedPointer]
  rw [access]
  dsimp only
  rw [ite_eq_left contains, stored]
  rfl

#print axioms get_ptr_write_of_access

end DuplicatePrefix.S04ReturnResolvedWindowPointer

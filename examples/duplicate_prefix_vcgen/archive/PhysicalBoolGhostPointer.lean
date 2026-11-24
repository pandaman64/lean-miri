import duplicate_prefix.PhysicalPointerAccess

namespace DuplicatePrefix.PhysicalBoolGhostPointer
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem ghost_access_of_edges {P E K H X : Type} [DecidableEq K]
    (write : Bool) (memory rawMemory : MemoryState P E K) (hooks resolvedHooks rawHooks : H)
    (target : PointerArithmetic) (ptr : Pointer (Option P)) (size : Size) (kind : Option K)
    (global : GlobalAllocationHooks P E K H) (access : AllocationAccessHooks P E K H X)
    (resolved : ResolvedPointer X) (allocation : Allocation P E) (amount : Int)
    (signed : sizeAsI64 size = .ok amount) (nonzero : amount ≠ 0)
    (resolve : access.resolvePointer memory hooks ptr amount = ⟨resolvedHooks, .ok (.ok resolved)⟩)
    (raw : (if write then MemoryLifecycle.getAllocRawMut memory resolvedHooks resolved.allocId kind global
      else MemoryLifecycle.getAllocRaw memory resolvedHooks resolved.allocId kind global) =
        ⟨rawMemory, rawHooks, .ok allocation⟩)
    (bounds : checkedBounds target resolved.allocId allocation.byteSize resolved.offset amount .memoryAccess = .ok ()) :
    (if write then AllocationAccess.getPtrAllocMut memory hooks target ptr size true kind global access
      else AllocationAccess.getPtrAlloc memory hooks target ptr size true kind global access) =
      let reference := AllocationAccessRef.mk resolved.allocId (allocRange resolved.offset size) allocation
      ⟨rawMemory, rawHooks, some reference, .ok (some reference)⟩ := by
  have same :
      (if write then AllocationAccess.getPtrAllocMut memory hooks target ptr size true kind global access
        else AllocationAccess.getPtrAlloc memory hooks target ptr size true kind global access) =
        AllocationAccess.getPtrAllocation memory hooks target ptr size true kind global access write := by
    cases write <;> rfl
  rw [same]
  unfold AllocationAccess.getPtrAllocation AllocationAccess.preparePtrAllocation
  rw [signed]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  simp only [bne_iff_ne, ite_eq_left nonzero]
  rw [resolve]
  dsimp only
  rw [raw]
  dsimp only
  rw [bounds]
  rfl

theorem get_ptr_window_ghost {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset count capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (write : Bool)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat + count.toNat ≤ capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    (if write then AllocationAccess.getPtrAllocMut machine.memory ⟨machine,none⟩ ⟨Size.ofBytes 8⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) (Size.ofBytes count) true
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config)
    else AllocationAccess.getPtrAlloc machine.memory ⟨machine,none⟩ ⟨Size.ofBytes 8⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) (Size.ofBytes count) true
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config)) =
      ⟨machine.memory,⟨machine,none⟩,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩)⟩ := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes count) signedFits
  change sizeAsI64 (Size.ofBytes count) = .ok (Int.ofNat count.toNat) at signed
  have nonzero : (Int.ofNat count.toNat != 0) = true := by
    have positiveNat : 0 < count.toNat := by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
    simp only [bne_iff_ne]
    change (count.toNat : Int) ≠ 0
    omega
  have resolve := MemoryCopyBridge.typed_resolve_cached pointers machine.memory machine id tag base offset
    (Int.ofNat count.toNat) width
    (by change -(2^63 : Int) ≤ (count.toNat : Int); omega)
    (by change (count.toNat : Int) < (2^63 : Int); omega) cached
  have resolveHook : (PlaceMachine.accessHooks config).resolvePointer machine.memory ⟨machine,none⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) (Int.ofNat count.toNat) =
      ⟨⟨machine,none⟩,.ok (.ok ⟨id,Size.ofBytes offset,.concrete tag⟩)⟩ := by
    unfold PlaceMachine.accessHooks
    simp only
    unfold_internal ".PlaceMachine.bridge"
    simp only [canonical]
    erw [resolve]
  have rawRead := MemoryCopyBridge.get_raw_live machine.memory (PlaceMachine.AccessState.mk machine none) id entry
    config.globalKind config.globalHooks present
  have rawWrite := MemoryCopyBridge.get_raw_mut_live machine.memory (PlaceMachine.AccessState.mk machine none) id entry
    config.globalKind config.globalHooks present mutable
  simp only [synchronize] at rawRead rawWrite
  have rawEq :
      (if write then MemoryLifecycle.getAllocRawMut machine.memory (PlaceMachine.AccessState.mk machine none)
        id config.globalKind config.globalHooks else MemoryLifecycle.getAllocRaw machine.memory
          (PlaceMachine.AccessState.mk machine none) id config.globalKind config.globalHooks) =
      ⟨machine.memory,⟨machine,none⟩,.ok entry.allocation⟩ := by
    cases write
    · exact rawRead
    · exact rawWrite
  have checked := DuplicatePrefix.checkedBounds_ok ⟨Size.ofBytes 8⟩ id entry.allocation.byteSize (Size.ofBytes offset)
    count.toNat .memoryAccess signedFits (by simpa only [size, Size.ofBytes] using bounds)
  exact ghost_access_of_edges write machine.memory machine.memory
    ⟨machine,none⟩ ⟨machine,none⟩ ⟨machine,none⟩ ⟨Size.ofBytes 8⟩
    (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset))) (Size.ofBytes count)
    config.globalKind config.globalHooks (PlaceMachine.accessHooks config)
    ⟨id,Size.ofBytes offset,.concrete tag⟩ entry.allocation (Int.ofNat count.toNat)
    signed (bne_iff_ne.mp nonzero) resolveHook rawEq checked


end DuplicatePrefix.PhysicalBoolGhostPointer

#print axioms DuplicatePrefix.PhysicalBoolGhostPointer.get_ptr_window_ghost

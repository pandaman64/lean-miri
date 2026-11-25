import Miri.Verification.CopyTreeWP
import Miri.Verification.MemoryObservationWP

/-! Pull a post-copy scalar load through the checked live allocation and Tree Borrows. -/
namespace Miri.Verification.CopyLoadObservationWP

open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Std.WP

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "Alloc" => Allocation Provenance BorrowTree
local notation "HookState" => PlaceMachine.AccessState K U

/-- Decode the selected scalar after permission checks, retaining the exact
cache update and hook state at either exit. -/
def selectedScalarImagePre [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (before : State) (primitive : BackendPrimitive)
    (accessHooks : HookState) (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (provenance : ProvenanceExtra) (offset : Size)
    (entry : LocalAllocation Provenance BorrowTree K) (allocation : Alloc) (range : AllocRange)
    (bytes : Except AllocError (Array UInt8))
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) : Prop :=
    let layout := localMemoryLayout operand.layout
    let accessed := allocRange offset layout.size
    let readPointer := match primitive with | .Pointer _ => true | _ => false
    let finish := fun (hooks : HookState) (tree : BorrowTree) outcome =>
      let updated := allocation.setExtra tree
      let memory := {memory with live := (memory.live.insert id
        {entry with allocation := updated})}
      MemoryWP.resultPre config before ⟨memory, hooks, some ⟨id, accessed, updated⟩, outcome⟩
        (fun (value : ImmediateValue Provenance) => post ⟨value.value, operand.layout⟩) onError
    MemoryWP.memoryAccessPre config false accessHooks allocation.extra id provenance
      accessed
      (fun hooks tree => finish hooks tree
        (((MemoryObservationWP.scalarFromImage config.runtime.base range readPointer
          bytes (allocation.initializationMask.isRangeInitialized range)
          allocation.provenanceMap).mapError MemoryOperandError.allocation).map
            fun scalar => ⟨.scalar scalar, layout⟩))
      (fun message hooks tree => finish hooks tree (.error (.pointerAccess
        (.hookFailure "beforeMemoryRead" message))))

/-- Use the selected allocation's own bytes during an ordinary indirect load. -/
def selectedScalarLoadPre [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (before : State) (primitive : BackendPrimitive)
    (accessHooks : HookState) (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (provenance : ProvenanceExtra) (offset : Size)
    (entry : LocalAllocation Provenance BorrowTree K) (allocation : Alloc) (range : AllocRange)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) : Prop :=
    selectedScalarImagePre config operand before primitive accessHooks memory id provenance offset
      entry allocation range (allocation.getBytesUnchecked range) post onError

/-- The typed load observes the selected live allocation's physical image.
A successful permission access changes the tree used for the live commit,
while the scalar is decoded from the already selected bytes and metadata.
A failing permission access retains the changed tree and skips decoding. -/
theorem liveScalarLoadPre [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (before : State) (place : MemPlace Provenance)
    (primitive : BackendPrimitive) (validRange : WrappingRange)
    (checked : MemoryWP.CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨place, localMemoryLayout operand.layout⟩)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : checked.rawMemory.live[checked.resolved.allocId]? = some entry)
    (indirect : operand.op = .indirect place)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.runtime = .ok (localMemoryLayout operand.layout).size)
    (aligned : place.misaligned = none)
    (range : AllocRange)
    (component : (allocRange checked.resolved.offset (localMemoryLayout operand.layout).size).subrange
      (allocRange Size.ZERO (localMemoryLayout operand.layout).size) = .ok range)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    MemoryWP.immediateReadPre config operand before post onError =
    selectedScalarLoadPre config operand before primitive checked.accessHooks checked.rawMemory
      checked.resolved.allocId checked.resolved.extra checked.resolved.offset entry checked.allocation
      range post onError := by
  apply propext
  rw [MemoryWP.immediateReadPre_iff, MemoryWP.readImmediate_iff,
    MemoryWP.scalarRead_resultPre_iff config operand place primitive validRange
    post onError before checked indirect backend width]
  unfold MemoryWP.CheckedPlaceAccess.pre selectedScalarLoadPre selectedScalarImagePre
  dsimp only
  apply Iff.of_eq
  congr 1
  · funext hooks tree
    rw [AllocationAccess.finishCheckedAccess, Std.ExtTreeMap.contains_eq_isSome_getElem?, live]
    simp only [Option.isSome_some, ↓reduceIte, MemoryState.setLiveAllocation_of_find _ _ _ _ live,
      finishPlaceAccess, aligned]
    rw [scalarReadAfterAccess_of_read _ _ _ _
      ⟨checked.resolved.allocId, allocRange checked.resolved.offset (localMemoryLayout operand.layout).size,
        checked.allocation.setExtra tree⟩ range _ rfl component]
    rw [Allocation.setExtra, Allocation.readScalar_mapExtra, MemoryObservationWP.readScalar_eq_image]
    cases primitive <;> rfl
  · funext message hooks tree
    rw [AllocationAccess.finishCheckedAccess, Std.ExtTreeMap.contains_eq_isSome_getElem?, live]
    simp only [Option.isSome_some, ↓reduceIte, MemoryState.setLiveAllocation_of_find _ _ _ _ live,
      Bool.false_eq_true, finishPlaceAccess, scalarReadAfterAccess]

/-- The live-map query after inserting a committed allocation splits on
the resolved ID, including when the resolved ID is still symbolic. -/
@[miri_initial_wp] theorem liveLookup_insert
    (memory : MemoryState Provenance BorrowTree K) (written observed : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) :
    (memory.live.insert written entry)[observed]? =
      if observed = written then some entry else memory.live[observed]? := by
  rw [Std.ExtTreeMap.getElem?_insert]
  simp only [Std.compare_eq_iff_eq, eq_comm (a := written) (b := observed)]

/-- Resolve a raw read lookup on the actual post-commit memory. The live branch
keeps the post-commit memory and the configured synchronization; on a live
miss the same global lookup and materialization rules run on that memory. -/
@[miri_initial_wp] theorem getAllocRaw_insert [DecidableEq K] (config : Config)
    (memory : MemoryState Provenance BorrowTree K) (written observed : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (hooks : HookState) :
    let committed := {memory with live := memory.live.insert written entry}
    MemoryLifecycle.getAllocRaw committed hooks observed config.globalKind config.globalHooks =
      MemoryLifecycle.getAllocRawFromLookup committed hooks observed config.globalKind config.globalHooks
        (if observed = written then some entry else memory.live[observed]?) := by
  simp only [MemoryLifecycle.getAllocRaw_eq_lookup, liveLookup_insert]

attribute [miri_initial_wp] MemoryLifecycle.getAllocRawFromLookup

/-- The physical copy publishes its allocation on either result. A missing
live key still reports the cache-update error at the pre-commit state. -/
@[miri_initial_wp] def copyCommitPre [DecidableEq K] (config : Config) (id : AllocId) (updated : Alloc)
    (outcome : Except AllocError Unit) (post : Unit → State → Prop)
    (onError : StepError → State → Prop) (before : State) : Prop :=
  match before.machine.memory.live[id]? with
  | none => onError (config.memoryError (.memoryUpdate (.unavailable id))) before
  | some entry =>
    let memory := {before.machine.memory with live :=
      (before.machine.memory.live.insert id {entry with allocation := updated})}
    let after := {before with machine := {before.machine with memory}}
    match outcome with
    | .ok () => post () after
    | .error error => onError (config.memoryError (.allocation error)) after

@[miri_initial_wp] theorem copyCommit_eq [DecidableEq K] (config : Config) (id : AllocId)
    (result : EStateM.Result AllocError Alloc Unit) (post : Unit → State → Prop)
    (onError : StepError → State → Prop) (before : State) :
    CopyMemoryWP.commitPre config id result post onError before =
      match result with
      | .ok () updated => copyCommitPre config id updated (.ok ()) post onError before
      | .error error updated => copyCommitPre config id updated (.error error) post onError before := by
  cases result with
  | ok value updated =>
    cases value
    simp only [CopyMemoryWP.commitPre, copyCommitPre, MemoryState.setLiveAllocation_eq_lookup]
    generalize before.machine.memory.live[id]? = entry
    cases entry <;> rfl
  | error error updated =>
    simp only [CopyMemoryWP.commitPre, copyCommitPre, MemoryState.setLiveAllocation_eq_lookup]
    generalize before.machine.memory.live[id]? = entry
    cases entry <;> rfl

/-- A same-ID indirect load after a copy commit takes its tree and byte image
from the replacement allocation. This follows from the actual raw-memory
lookup, regardless of what the pointer policies do to their hook state. -/
theorem copiedAllocation_selected [DecidableEq K] (config : Config)
    (before : State) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (updated : Alloc) (place : MemoryOperandPlace Provenance)
    (copied : State)
    (commit : before.machine.memory.setLiveAllocation id updated = .ok copied.machine.memory)
    (live : before.machine.memory.live[id]? = some entry)
    (checked : MemoryWP.CheckedPlaceAccess config false copied.machine.memory
      ⟨copied.machine, none⟩ place)
    (same : checked.resolved.allocId = id) :
    checked.rawMemory = copied.machine.memory ∧
    checked.rawMemory.live[checked.resolved.allocId]? = some {entry with allocation := updated} ∧
    checked.allocation = updated := by
  have found := MemoryObservationWP.lookup_after_commit before.machine.memory id id updated entry live
  rw [commit] at found
  have selected : copied.machine.memory.live[id]? = some {entry with allocation := updated} := by
    simpa only [Except.map, ↓reduceIte, Except.ok.injEq] using found
  have raw := checked.raw
  simp only [Bool.false_eq_true, ↓reduceIte, same, MemoryLifecycle.getAllocRaw, selected,
    Id.run, pure, Pure.pure, MemoryAccessResult.mk.injEq, Except.ok.injEq] at raw
  exact ⟨raw.1.symm, by rw [raw.1.symm, same, selected], raw.2.2.symm⟩

/-- Specialize the successful physical-copy continuation to a same-ID
scalar observer. The pointer-resolution and lookup evidence belongs to the
state after the commit. The returned precondition still checks diagnostics,
races, permission transitions, and synchronization. -/
theorem commitThenReadSame [DecidableEq K] (config : Config) (before copied : State)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (updated : Alloc)
    (live : before.machine.memory.live[id]? = some entry)
    (commit : before.machine.memory.setLiveAllocation id updated = .ok copied.machine.memory)
    (copiedState : {before with machine := {before.machine with memory := copied.machine.memory}} = copied)
    (operand : OpTy Provenance) (place : MemPlace Provenance)
    (primitive : BackendPrimitive) (validRange : WrappingRange)
    (checked : MemoryWP.CheckedPlaceAccess config false copied.machine.memory ⟨copied.machine, none⟩
      ⟨place, localMemoryLayout operand.layout⟩)
    (same : checked.resolved.allocId = id)
    (indirect : operand.op = .indirect place)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.runtime = .ok (localMemoryLayout operand.layout).size)
    (aligned : place.misaligned = none)
    (range : AllocRange)
    (component : (allocRange checked.resolved.offset (localMemoryLayout operand.layout).size).subrange
      (allocRange Size.ZERO (localMemoryLayout operand.layout).size) = .ok range)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    CopyMemoryWP.commitPre config id (.ok () updated)
      (fun _ after => MemoryWP.immediateReadPre config operand after post onError) onError before =
    selectedScalarLoadPre config operand copied primitive checked.accessHooks copied.machine.memory
      id checked.resolved.extra checked.resolved.offset {entry with allocation := updated} updated
      range post onError := by
  obtain ⟨raw, present, allocation⟩ :=
    copiedAllocation_selected config before id entry updated _ copied commit live checked same
  simp only [CopyMemoryWP.commitPre, commit, copiedState]
  rw [liveScalarLoadPre config operand copied place primitive validRange checked
    {entry with allocation := updated} present indirect backend width aligned range component,
    raw, same, allocation]

/-- An actual canonical byte copy can use the typed load as its next
continuation. The pointer, bounds, diagnostic, race and synchronization
actions are the same ones used by the canonical machine. -/
theorem wp_copyThenLoad [DecidableEq K] (config : Config)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (source dest : Pointer (Option Provenance)) (size : Size) (repeatCount : UInt64)
    (nonoverlapping : Bool) (operand : OpTy Provenance)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop)
    (before : State) :
    wp (do
      GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest size repeatCount nonoverlapping
      PlaceMachine.readImmediate config operand) post onError before ↔
    CopyTreeWP.copyPre config addresses arithmetic source dest size repeatCount nonoverlapping
      (fun _ copied => MemoryWP.immediateReadPre config operand copied post onError) onError before := by
  rw [← RvalueWP.actionPre_eq_wp, RvalueWP.actionPre_bind, CopyTreeWP.copyPre_eq]
  have nextEq : RvalueWP.actionPre (PlaceMachine.readImmediate config operand) post onError =
      fun copied => MemoryWP.immediateReadPre config operand copied post onError := by
    rw [RvalueWP.actionPre_eq_wp]
    funext copied
    exact propext (MemoryWP.immediateReadPre_iff ..).symm
  rw [nextEq]

end Miri.Verification.CopyLoadObservationWP

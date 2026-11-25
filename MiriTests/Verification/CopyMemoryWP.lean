import Miri.Verification.CopyMemoryWP

/-! Real overlapping copies exercise snapshot bytes, metadata, and hook order. -/
namespace MiriTests.Verification.CopyMemoryWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification Std.WP

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

private abbrev User := Array String
private abbrev State := MachineHooks.State Unit User
private abbrev Alloc := Allocation Provenance BorrowTree

private def id : AllocId := ⟨1, by decide⟩
private def size (bytes : UInt64) : Size := Size.ofBytes bytes
private def arithmetic : PointerArithmetic := ⟨size 8⟩
private def pointer (offset : UInt64) : Pointer (Option Provenance) :=
  Pointer.new (some (.concrete id BorTag.one)) (size offset)

private def record (event : String) : PlaceMachine.MachineM Unit User Unit :=
  modify fun machine => {machine with user := machine.user.push event}

private def config : PlaceMachine.AccessConfig Unit User where
  runtime := {RuntimeTargetDataLayout.default with base := ⟨.little, .w64⟩}
  ghostMode := false
  globalKind := none
  globalHooks := {
    synchronizeMemory := fun _ state => state
    evaluateStaticInitializer := fun memory state _ => ⟨memory, state, .error "unexpected global"⟩
    beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state, .error "unexpected global"⟩
    adjustGlobalAllocation := fun memory state _ _ => ⟨memory, state, .error "unexpected global"⟩ }
  dynamicLayout := fun memory state _ => ⟨memory, state, .ok none⟩
  resolvePointer := fun _ ptr _ => do
    record (if ptr.offset == Size.ZERO then "source pointer" else "destination pointer")
    match ptr.provenance with
    | some (.concrete id tag) => pure (.ok ⟨id, ptr.offset, .concrete tag⟩)
    | _ => pure (.error ptr.offset.bytes)
  beforeAllocationAccess := fun _ => record "allocation"
  diagnostic := fun write _ _ => record (if write then "write" else "read")
  weakMemoryWrite := fun _ _ => record "weak write"
  syncAccess := fun write _ _ => record (if write then "sync write" else "sync read")
  retainTouched := fun machine _ => machine
  memoryError := MemoryErrors.operand

private def addresses (_ : User) : AllocAddresses.GlobalAddressState :=
  {provenanceMode := .strict, addressMode := .managed, generation := none, baseAddr := #[⟨id, 0⟩]}

private def initial (allocation : Alloc) : State :=
  let empty : MemoryState Provenance BorrowTree Unit := MemoryState.empty
  let entry : LocalAllocation Provenance BorrowTree Unit := ⟨.machine (), allocation⟩
  { stack := Stack.empty
    machine := {
      memory := {empty with live := empty.live.insert id entry}
      borrowTracker := none
      dataRace := none
      threads := Miri.Concurrency.ThreadManager.initial true
      raceAllocations := {}
      allocationSpans := #[]
      user := #[] } }

private def events : User :=
  #["source pointer", "destination pointer", "allocation", "read", "sync read",
    "allocation", "write", "weak write", "sync write"]

private def image : Except AllocError Alloc :=
  (Allocation.fromBytes #[11, 22, 33, 44] Align.ONE .Mut).map
    (·.mapExtra fun _ => BorrowTree.new BorTag.one (size 4))

private def observed (state : State) (expected : Array UInt8) : Bool :=
  state.machine.user == events &&
    match state.machine.memory.live[id]? with
    | none => false
    | some entry =>
      (entry.allocation.getBytesUnchecked (allocRange Size.ZERO (size 4))).toOption == some expected &&
      ((entry.allocation.initializationMask.isRangeInitialized (allocRange Size.ZERO (size 4))).toOption.map
        Except.isOk) == some true &&
      entry.allocation.provenanceMap.ptrs.isEmpty &&
      entry.allocation.provenanceMap.byteFragments.isNone

private def checkCopy (source dest : Pointer (Option Provenance)) (nonoverlap : Bool)
    (post : State → Bool) (onError : StepError → State → Bool) (before : State) : Bool :=
  match GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest (size 2) 1 nonoverlap before with
  | .ok () after => post after
  | .error error after => onError error after

private theorem copyPre_checkCopy (source dest : Pointer (Option Provenance)) (nonoverlap : Bool)
    (post : State → Bool) (onError : StepError → State → Bool) (before : State) :
    CopyMemoryWP.copyPre config addresses arithmetic source dest (size 2) 1 nonoverlap
      (fun _ after => post after = true) (fun error after => onError error after = true) before =
      (checkCopy source dest nonoverlap post onError before = true) := by
  rw [← CopyMemoryWP.copyPre_eq]
  unfold RvalueWP.actionPre checkCopy
  cases GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest (size 2) 1 nonoverlap before with
  | ok value => cases value; rfl
  | error => rfl

private def checkImage (action : Alloc → Bool) : Bool :=
  match image with | .ok allocation => action allocation | .error _ => false

private theorem image_check (action : Alloc → Bool) :
    (match image with | .ok allocation => action allocation = true | .error _ => False) =
      (checkImage action = true) := by
  unfold checkImage
  cases image <;> simp

/-- Ordinary copy within the same allocation keeps the original source image
when the first destination byte also lies in the source range. -/
theorem overlapping_copy :
    match image with
    | .error _ => False
    | .ok allocation =>
      wp (GlobalMemoryCopyMachine.genericCopy config addresses arithmetic
          (pointer 0) (pointer 1) (size 2) 1 false)
        (fun _ after => observed after #[11, 11, 22, 44] = true)
        (fun _ _ => false = true) (initial allocation) := by
  simp only [CopyMemoryWP.wp_copy, copyPre_checkCopy]
  refine Eq.mpr (image_check (fun allocation =>
    checkCopy (pointer 0) (pointer 1) false (fun after => observed after #[11, 11, 22, 44])
      (fun _ _ => false) (initial allocation))) ?_
  decide +kernel

/-- The same ranges fail under copy_nonoverlapping after the write hooks.
Destination bytes are still the original bytes. -/
theorem overlap_nonoverlapping :
    match image with
    | .error _ => False
    | .ok allocation =>
      wp (GlobalMemoryCopyMachine.genericCopy config addresses arithmetic
          (pointer 0) (pointer 1) (size 2) 1 true)
        (fun _ _ => false = true)
        (fun error after =>
          (RunLoop.reportsUB error && observed after #[11, 22, 33, 44]) = true)
        (initial allocation) := by
  simp only [CopyMemoryWP.wp_copy, copyPre_checkCopy]
  refine Eq.mpr (image_check (fun allocation =>
    checkCopy (pointer 0) (pointer 1) true (fun _ => false)
      (fun error after => RunLoop.reportsUB error &&
        observed after #[11, 22, 33, 44]) (initial allocation))) ?_
  decide +kernel

private def destinationUninitialized (state : State) : Bool :=
  state.machine.user == events &&
    match state.machine.memory.live[id]? with
    | none => false
    | some entry =>
      (entry.allocation.getBytesUnchecked (allocRange Size.ZERO (size 4))).toOption ==
        some #[11, 22, 33, 44] &&
      match entry.allocation.initializationMask.isRangeInitialized (allocRange (size 2) (size 2)) with
      | .ok (.error range) => range == allocRange (size 2) (size 2)
      | _ => false

private theorem uninitImage_check (allocation : Alloc) (action : Alloc → Bool) :
    (match Allocation.writeUninit (allocRange Size.ZERO (size 2)) (size 8) allocation with
      | .error _ _ => False
      | .ok () uninitialized => action uninitialized = true) =
    ((match Allocation.writeUninit (allocRange Size.ZERO (size 2)) (size 8) allocation with
      | .error _ _ => false
      | .ok () uninitialized => action uninitialized) = true) := by
  cases Allocation.writeUninit (allocRange Size.ZERO (size 2)) (size 8) allocation with
  | ok value => cases value; rfl
  | error => simp

/-- A fully uninitialized source propagates uninitialization and preserves the
destination byte representation through the all-uninitialized fast path. -/
theorem uninitialized_copy :
    match image with
    | .error _ => False
    | .ok allocation =>
      match Allocation.writeUninit (allocRange Size.ZERO (size 2)) (size 8) allocation with
      | .error _ _ => False
      | .ok () uninitialized =>
        wp (GlobalMemoryCopyMachine.genericCopy config addresses arithmetic
            (pointer 0) (pointer 2) (size 2) 1 true)
          (fun _ after => destinationUninitialized after = true)
          (fun _ _ => false = true) (initial uninitialized) := by
  simp only [CopyMemoryWP.wp_copy, copyPre_checkCopy, uninitImage_check]
  refine Eq.mpr (image_check (fun allocation =>
    match Allocation.writeUninit (allocRange Size.ZERO (size 2)) (size 8) allocation with
    | .error _ _ => false
    | .ok () uninitialized =>
      checkCopy (pointer 0) (pointer 2) true destinationUninitialized
        (fun _ _ => false) (initial uninitialized))) ?_
  decide +kernel

/-- The byte rule can stop at a failing source slice before it touches the
destination image. The machine still publishes the returned allocation. -/
example (source dest : Alloc) (before : State) (range : AllocRange) (allocError : AllocError)
    (readError : source.getBytesUnchecked range = .error allocError)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    CopyMemoryWP.commitPre config id
      (source.copyRepeatedly range (size 1) 1 (size 8) true false dest) post onError before =
    CopyMemoryWP.commitPre config id (.error allocError dest) post onError before := by
  miri_copy_bytes_wp
  rw [readError]

#print axioms overlapping_copy
#print axioms overlap_nonoverlapping
#print axioms uninitialized_copy

end MiriTests.Verification.CopyMemoryWP

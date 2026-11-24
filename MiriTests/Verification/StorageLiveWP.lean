import Init.Internal.Order.While
import Miri.Verification.StorageLiveWP

namespace MiriTests.Verification.StorageLiveWP

open Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification RvalueWP Std.WP

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra
local notation "Errors" => StepError → State → Prop

/-- The selected statement reaches the driver continuation with the replaced local. -/
theorem sizedStatement {C O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (id : LocalId) (post : Bool → State → Prop) (onError : Errors)
    (before : State) (frame updated : Frame) (slot : LocalState Provenance LocalLayout) (ty : TyId)
    (current : before.stack.currentFrame? = some frame) (nonempty : before.stack.frames.isEmpty = false)
    (selected : frame.getLocal id = .ok slot) (dead : slot.value = .dead)
    (localType : frame.body.locals[id]? = some ty)
    (trivial : (ExecutionMachine.withValidation config limits).lifecycle.storage.veryTriviallySized ty = .ok true)
    (noRace : frame.extra.dataRace = none)
    (installed : frame.replaceLocalValue id (.live (.immediate .uninit)) = .ok updated) :
    CanonicalStepWP.statementPre config limits choice (.StorageLive id) post onError before ↔
      InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError
        {before with stack := ⟨before.stack.frames.pop.push updated⟩} := by
  miri_storage_live
  simp [current, nonempty, selected, dead, localType, trivial, noRace, installed,
    Miri.Verification.StorageLiveWP.currentFramePre, Except.mapError]

/-- With no cached layout, a successful layout query updates the current frame
before a missing-metadata error is reported. -/
theorem missingMetadataAfterCaching (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (before ready : State) (frame currentFrame updated : Frame) (layout : LocalLayout)
    (slot : LocalState Provenance LocalLayout) (ty : TyId) (post : Unit → State → Prop) (onError : Errors)
    (current : before.stack.currentFrame? = some frame)
    (selected : frame.getLocal id = .ok slot) (localType : frame.body.locals[id]? = some ty)
    (trivial : hooks.veryTriviallySized ty = .ok false)
    (uncached : frame.getLocalLayout id = .ok none) (computed : hooks.layout id before = .ok layout ready)
    (readyFrame : ready.stack.currentFrame? = some currentFrame) (nonempty : ready.stack.frames.isEmpty = false)
    (cached : currentFrame.getOrCacheLocalLayout id layout = .ok (updated, layout))
    (unsized : layout.layout.isSized = false) :
    wp (MachineHooks.storageLiveDyn hooks id .none) post onError before ↔
      onError (.stack (.unsizedLocalMissingMetadata id))
        {ready with stack := ⟨ready.stack.frames.pop.push updated⟩} := by
  simp [Miri.Verification.StorageLiveWP.wp_storageLiveDyn, Miri.Verification.StorageLiveWP.storageLiveDynPre,
    Miri.Verification.StorageLiveWP.valuePre, Miri.Verification.StorageLiveWP.localLayoutPre,
    Miri.Verification.StorageLiveWP.currentFramePre, Miri.Verification.StorageLiveWP.stackCheck,
    Miri.Verification.StorageLiveWP.setCurrentFramePre, scalarCheckPre, Except.mapError, MemPlaceMeta.hasMeta,
    current, selected, localType, trivial, uncached, actionPre_ok computed, readyFrame, nonempty, cached, unsized]

/-- When deallocation fails, the error continuation sees the installed operand
and all state updates made by the deallocator. -/
theorem deallocationFailureAfterInstall (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (before allocated failed : State) (frame currentFrame updated : Frame)
    (layout : LocalLayout) (newPlace oldPlace : MemPlace Provenance) (metadata : Scalar Provenance)
    (slot old : LocalState Provenance LocalLayout) (ty : TyId)
    (post : Unit → State → Prop) (onError : Errors) (error : StepError)
    (current : before.stack.currentFrame? = some frame)
    (selected : frame.getLocal id = .ok slot) (localType : frame.body.locals[id]? = some ty)
    (trivial : hooks.veryTriviallySized ty = .ok false)
    (cached : frame.getLocalLayout id = .ok (some layout)) (unsized : layout.layout.isSized = false)
    (allocation : hooks.allocateDyn layout (.metadata metadata) before = .ok newPlace allocated)
    (allocatedFrame : allocated.stack.currentFrame? = some currentFrame)
    (nonempty : allocated.stack.frames.isEmpty = false)
    (oldSlot : currentFrame.getLocal id = .ok old) (indirect : old.value = .live (.indirect oldPlace))
    (installed : currentFrame.replaceLocalValue id (.live (.indirect newPlace)) = .ok updated)
    (deallocation : hooks.deallocateStack oldPlace.ptr
      {allocated with stack := ⟨allocated.stack.frames.pop.push updated⟩} = .error error failed) :
    wp (MachineHooks.storageLiveDyn hooks id (.metadata metadata)) post onError before ↔
      onError error failed := by
  simp [Miri.Verification.StorageLiveWP.wp_storageLiveDyn, Miri.Verification.StorageLiveWP.storageLiveDynPre,
    Miri.Verification.StorageLiveWP.valuePre, Miri.Verification.StorageLiveWP.localLayoutPre,
    Miri.Verification.StorageLiveWP.installPre, Miri.Verification.StorageLiveWP.currentFramePre,
    Miri.Verification.StorageLiveWP.stackCheck, Miri.Verification.StorageLiveWP.setCurrentFramePre,
    scalarCheckPre, Except.mapError, MemPlaceMeta.hasMeta, current, selected, localType, trivial, cached,
    unsized, actionPre_ok allocation, allocatedFrame, nonempty, oldSlot, indirect, installed]
  simp [actionPre, deallocation]

set_option experimental.vcgen true in
/-- The registered effect rule exposes the empty-stack error to VC generation. -/
theorem generatedEmptyStack (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (before : State) (post : Unit → State → Prop) (onError : Errors)
    (empty : before.stack.currentFrame? = none)
    (handled : onError (.stack .emptyStack) before) :
    Triple (MachineHooks.storageLiveDyn hooks id .none) (· = before) post onError := by
  vcgen
  rename_i state same
  subst state
  simpa [Miri.Verification.StorageLiveWP.storageLiveDynPre,
    Miri.Verification.StorageLiveWP.currentFramePre, empty] using handled

open Miri.ABI Miri.Input Miri.Memory.AllocAddresses StackAllocationWP

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private abbrev TestState := EvalConfiguration.State Unit Unit Unit Unit Unit Unit Unit Unit Unit
private abbrev TestUser := EvalConfiguration.User Unit Unit Unit Unit Unit Unit Unit Unit Unit

private def testedId : AllocId := ⟨1, by decide⟩

private def configuredExtras : MemoryExtras.Hooks MiriMemoryKind TestUser Unit :=
  EvalCoreMachine.extras (fun _ _ => throw (.invalidProgram "unexpected synchronization access"))
    (fun _ => .invalidProgram "unexpected weak-memory error")

private def configuredAllocation : PlaceMachine.AllocationConfig MiriMemoryKind TestUser :=
  EvalConfiguration.allocation (Size.ofBytes 64)
    (fun size _ => some (Array.replicate size.bytes.toNat 0)) (fun _ _ _ => pure ())
    { arithmetic := ⟨Size.ofBytes 8⟩
      externalAddress := fun _ _ => throw (.invalidProgram "unexpected external allocation")
      ensureTreeExtra := fun _ => throw (.invalidProgram "unexpected global materialization")
      diagnosticIntToPtr := throw (.invalidProgram "unexpected integer cast")
      strictIntToPtr := .invalidProgram "strict integer cast"
      classifyAddressError := fun _ => .resourceExhaustion "managed stack address failure" }
    configuredExtras

private def allocationInput (ambient : TestState) (tape : ExecutionChoices.Tape) : TestState :=
  let addresses : GlobalAddressState :=
    {provenanceMode := .default, addressMode := .managed,
      generation := some ⟨AddressGenerator.new 1024 2048, ⟨0.0, 0.0, #[]⟩⟩}
  let tracker : MachineHooks.BorrowState := ⟨Miri.TreeBorrows.GlobalState.new, .Default⟩
  let user := ambient.machine.user
  let world := user.payload.payload.user
  let world := {world with backend := .none, runtime := {world.runtime with extras := {}}}
  let user := {user with addresses, payload := {user.payload with payload :=
    {user.payload.payload with user := world}}}
  EvalCoreMachine.tape.put
    {ambient with machine := {ambient.machine with
      memory := .empty, borrowTracker := some tracker, dataRace := none,
      threads := .initial false, raceAllocations := {}, allocationSpans := #[], user}} tape

private def stackEntryFacts (state : TestState) : Prop :=
  let memory := state.machine.memory
  memory.nextAllocId = 2 ∧
  (state.machine.borrowTracker.bind fun tracker => tracker.global.rootTag? testedId) = some BorTag.one ∧
  (MemoryExtras.lookup configuredExtras state.machine testedId).isOk = true ∧
  match memory.live[testedId]? with
  | none => False
  | some entry =>
    entry.kind = .stack ∧ entry.allocation.byteSize = Size.ofBytes 4 ∧
      entry.allocation.initializationMask = InitMask.new (Size.ofBytes 4) false

set_option maxRecDepth 8192 in
set_option cbv.maxSteps 1000000 in
/-- The production allocator reserves an ID, initializes uninitialized storage,
installs the root tag and extras, and caches the address from the supplied draw. -/
theorem configuredAllocationSuccess (ambient : TestState) :
    actionPre (PlaceMachine.allocateStackRaw configuredAllocation (Size.ofBytes 4) Align.ONE)
      (fun pointer state =>
        pointer = Pointer.new (some (.concrete testedId BorTag.one)) (Size.ofBytes 1027) ∧
        stackEntryFacts state ∧
        (EvalCoreMachine.tape.get state).cursor = 1 ∧
        (state.machine.user.addresses.baseAddr.find? (·.allocId == testedId)).map (·.address) =
          some 1027)
      (fun _ _ => False) (allocationInput ambient {inputs := #[.index .addressSlack 3]}) := by
  unfold configuredAllocation
  miri_storage_live
  cbv
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
set_option cbv.maxSteps 1000000 in
/-- When the configured allocator exhausts its tape at address assignment,
the issued ID, live bytes, root tag and extras reach the error continuation. -/
theorem configuredAllocationAddressFailure (ambient : TestState) :
    actionPre (PlaceMachine.allocateStackRaw configuredAllocation (Size.ofBytes 4) Align.ONE)
      (fun _ _ => False)
      (fun error state =>
        error = .callback "choice input unknown: tape exhausted" ∧
        stackEntryFacts state ∧
        (EvalCoreMachine.tape.get state).cursor = 0 ∧
        state.machine.user.addresses.baseAddr = #[])
      (allocationInput ambient {inputs := #[]}) := by
  unfold configuredAllocation
  miri_storage_live
  cbv

end MiriTests.Verification.StorageLiveWP

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

end MiriTests.Verification.StorageLiveWP

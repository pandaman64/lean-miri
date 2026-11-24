import Miri.Verification.CanonicalStepWP
import Miri.Verification.StackAllocationWP
import Miri.Input.CompilerStorage
import Lean.Elab.Tactic.Conv

/-! Exact continuation rules for the canonical MIR storage-live operation. -/

namespace Miri.Verification.StorageLiveWP

open Miri.Interpreter Miri.MIR Miri.Memory RvalueWP Std.WP

variable {K U A : Type}
local notation "State" => MachineHooks.State K U
local notation "Errors" => StepError → State → Prop
local notation "ActualFrame" => Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- Read the current frame at the state left by the preceding effect. -/
def currentFramePre (post : ActualFrame → State → Prop)
    (onError : Errors) (state : State) : Prop :=
  match state.stack.currentFrame? with
  | none => onError (.stack .emptyStack) state
  | some frame => post frame state

theorem actionPre_currentFrame
    (post : ActualFrame → State → Prop) (onError : Errors) :
    actionPre MachineHooks.currentFrame post onError = currentFramePre post onError := by
  funext state
  unfold currentFramePre MachineHooks.currentFrame actionPre
  simp only [bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  cases state.stack.currentFrame? <;> rfl

/-- Publish an updated current frame while retaining the machine state. -/
def setCurrentFramePre (frame : ActualFrame) (post : Unit → State → Prop)
    (onError : Errors) (state : State) : Prop :=
  if state.stack.frames.isEmpty then onError (.stack .emptyStack) state
  else post () {state with stack := ⟨state.stack.frames.pop.push frame⟩}

theorem actionPre_setCurrentFrame (frame : ActualFrame)
    (post : Unit → State → Prop) (onError : Errors) :
    actionPre (MachineHooks.setCurrentFrame frame) post onError =
      setCurrentFramePre frame post onError := by
  funext state
  unfold setCurrentFramePre MachineHooks.setCurrentFrame actionPre
  simp only [bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  cases state.stack.frames.isEmpty <;> rfl

def stackCheck (result : Except StackError A) (post : A → State → Prop)
    (onError : Errors) (state : State) : Prop :=
  scalarCheckPre (result.mapError StepError.stack) post onError state

private theorem actionPre_stackCheck (result : Except StackError A)
    (post : A → State → Prop) (onError : Errors) :
    actionPre (MachineHooks.storageResult result) post onError =
      stackCheck result post onError := by
  cases result <;> rfl

private theorem actionPre_pure_fun (value : A) (post : A → State → Prop) (onError : Errors) :
    actionPre (pure value) post onError = post value := rfl

private theorem actionPre_throw_fun (error : StepError) (post : A → State → Prop) (onError : Errors) :
    actionPre (throw error) post onError = onError error := rfl

private theorem actionPre_deallocate (hooks : MachineHooks.StorageHooks K U)
    (old : LocalValue Provenance) (post : Unit → State → Prop) (onError : Errors) :
    actionPre (MachineHooks.deallocateStorage hooks old) post onError =
      (match old with
      | .live (.indirect place) => actionPre (hooks.deallocateStack place.ptr) post onError
      | _ => post ()) := by
  cases old with
  | dead => rfl
  | live operand => cases operand <;> rfl

/-- Use the cached layout when present. On a miss, cache the computed layout
in the frame current after the compiler hook. -/
def localLayoutPre (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (post : LocalLayout → State → Prop) (onError : Errors) : State → Prop :=
  currentFramePre (fun frame =>
    stackCheck (frame.getLocalLayout id) (fun
      | some cached => post cached
      | none => actionPre (hooks.layout id) (fun computed =>
          currentFramePre (fun updated =>
            stackCheck (updated.getOrCacheLocalLayout id computed) (fun (frame, cached) =>
              setCurrentFramePre frame (fun _ => post cached) onError) onError) onError)
        onError) onError) onError

/-- Replacing a live indirect operand publishes the new operand before
deallocating the old storage. -/
def installPre (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (value : Operand Provenance) (post : Unit → State → Prop) (onError : Errors) : State → Prop :=
  currentFramePre (fun frame =>
    stackCheck (frame.getLocal id) (fun old =>
      stackCheck (frame.replaceLocalValue id (.live value)) (fun updated =>
        setCurrentFramePre updated (fun _ =>
          match old.value with
          | .live (.indirect place) => actionPre (hooks.deallocateStack place.ptr) post onError
          | _ => post ()) onError) onError) onError) onError

/-- Select the sized or unsized value and account for its effect before
publishing the replacement local. -/
def valuePre (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (metadata : MemPlaceMeta Provenance) (post : Operand Provenance → State → Prop)
    (onError : Errors) : Option LocalLayout → State → Prop
  | none =>
    if metadata.hasMeta then onError (.stack (.metadataForSizedLocal id))
    else actionPre (MachineHooks.afterLocalWrite id true)
      (fun _ => post (.immediate .uninit)) onError
  | some layout =>
    if metadata.hasMeta then actionPre (hooks.allocateDyn layout metadata)
      (fun place => post (.indirect place)) onError
    else onError (.stack (.unsizedLocalMissingMetadata id))

/-- Account for each local, type, layout, metadata, race, allocation and
replacement check before running the corresponding continuation. -/
def storageLiveDynPre (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (metadata : MemPlaceMeta Provenance) (post : Unit → State → Prop)
    (onError : Errors) : State → Prop :=
  let finish := valuePre hooks id metadata (fun value => installPre hooks id value post onError) onError
  currentFramePre (fun frame =>
    stackCheck (frame.getLocal id) (fun _ state =>
      match frame.body.locals[id]? with
      | none => onError (.stack (.missingLocalType id)) state
      | some ty =>
        scalarCheckPre (hooks.veryTriviallySized ty) (fun trivial =>
          if trivial then finish none else
            localLayoutPre hooks id (fun layout => finish (if layout.layout.isSized then none else some layout))
              onError) onError state) onError) onError

theorem actionPre_storageLiveDyn (hooks : MachineHooks.StorageHooks K U)
    (id : LocalId) (metadata : MemPlaceMeta Provenance) (post : Unit → State → Prop)
    (onError : Errors) :
    actionPre (MachineHooks.storageLiveDyn hooks id metadata) post onError =
      storageLiveDynPre hooks id metadata post onError := by
  funext before
  simp only [MachineHooks.storageLiveDyn, storageLiveDynPre, actionPre_bind_fun,
    actionPre_currentFrame, currentFramePre]
  cases current : before.stack.currentFrame? with
  | none => rfl
  | some frame =>
    dsimp only
    rw [MachineHooks.storageResult_eq, actionPre_stackCheck]
    unfold stackCheck scalarCheckPre
    cases frame.getLocal id with
    | error => rfl
    | ok slot =>
      cases localType : frame.body.locals[id]? with
      | none => rfl
      | some ty =>
        simp only [actionPre_bind_fun, actionPre_pure]
        cases sized : hooks.veryTriviallySized ty with
        | error => rfl
        | ok trivial =>
          simp only [actionPre_bind_fun, actionPre_pure]
          cases trivial <;>
            simp only [Bool.false_eq_true, ↓reduceIte, actionPre_ite,
              localLayoutPre, installPre, valuePre, stackCheck, scalarCheckPre, Except.mapError,
              actionPre_bind_fun, actionPre_pure_fun, actionPre_throw_fun, actionPre_currentFrame,
              actionPre_setCurrentFrame, currentFramePre, MachineHooks.storageResult_eq,
              MachineHooks.deallocateLocal_eq, actionPre_stackCheck, actionPre_deallocate, current]
          case false =>
            cases frame.getLocalLayout id with
            | error => rfl
            | ok cached =>
              cases cached with
              | some layout =>
                cases layoutSized : layout.layout.isSized <;> cases metadata.hasMeta <;>
                  simp only [layoutSized, Bool.false_eq_true, ↓reduceIte,
                    actionPre_bind_fun, actionPre_pure_fun, actionPre_throw_fun,
                    actionPre_currentFrame, actionPre_setCurrentFrame, actionPre_stackCheck,
                    actionPre_deallocate]
              | none =>
                simp only [actionPre_bind_fun, actionPre_currentFrame, actionPre_stackCheck,
                  actionPre_setCurrentFrame, actionPre_pure_fun]
                congr 1
                funext computed state
                unfold currentFramePre
                cases state.stack.currentFrame? with
                | none => rfl
                | some updated =>
                  dsimp only
                  unfold stackCheck scalarCheckPre
                  cases updated.getOrCacheLocalLayout id computed with
                  | error => rfl
                  | ok result =>
                    simp only [Except.mapError]
                    rcases result with ⟨frame, layout⟩
                    cases layoutSized : layout.layout.isSized <;> cases metadata.hasMeta <;>
                      simp only [Bool.false_eq_true, ↓reduceIte,
                        actionPre_bind_fun, actionPre_pure_fun, actionPre_throw_fun,
                        actionPre_currentFrame, actionPre_setCurrentFrame, actionPre_stackCheck,
                        actionPre_deallocate]
                    all_goals rfl

theorem wp_storageLiveDyn (hooks : MachineHooks.StorageHooks K U)
    (id : LocalId) (metadata : MemPlaceMeta Provenance) (post : Unit → State → Prop)
    (onError : Errors) :
    wp (MachineHooks.storageLiveDyn hooks id metadata) post onError =
      storageLiveDynPre hooks id metadata post onError := by
  rw [← actionPre_eq_wp, actionPre_storageLiveDyn]

@[spec high] theorem spec_storageLiveDyn (hooks : MachineHooks.StorageHooks K U)
    (id : LocalId) (metadata : MemPlaceMeta Provenance) (post : Unit → State → Prop)
    (onError : Errors) :
    Triple (MachineHooks.storageLiveDyn hooks id metadata)
      (storageLiveDynPre hooks id metadata post onError) post onError := by
  apply Triple.iff.mpr
  intro state checked
  rw [wp_storageLiveDyn]
  exact checked

/-- Preserve the original frame-index guard and statement advance after storage succeeds. -/
theorem statement_storageLive {C O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (id : LocalId) (post : Bool → State → Prop) (onError : Errors)
    (before : State) :
    CanonicalStepWP.statementPre config limits choice (.StorageLive id) post onError before =
      storageLiveDynPre (ExecutionMachine.withValidation config limits).lifecycle.storage id .none
        (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError)
        onError before := by
  rw [CanonicalStepWP.statementPre, wp_storageLiveDyn]

/-- Model the frame-local race write and its error-state ordering. The machine
clock update precedes the frame update, which precedes the race verdict. -/
def afterLocalWritePre (id : LocalId) (storageLive : Bool) (post : Unit → State → Prop)
    (onError : Errors) : State → Prop :=
  currentFramePre (fun frame before =>
    match frame.extra.dataRace with
    | none => post () before
    | some clocks =>
      match before.machine.dataRace with
      | none => onError (.invalidProgram "frame has vector clocks but machine does not") before
      | some global =>
        let result := Miri.Concurrency.LocalRace.localWrite clocks global before.machine.threads id storageLive
        let next := {before with machine := {before.machine with dataRace := some result.global}}
        let frame := {frame with extra := {frame.extra with dataRace := some result.frame}}
        setCurrentFramePre frame (fun _ state =>
          match result.outcome with
          | .ok _ => post () state
          | .error error => onError (.callback s!"after_local_write: {reprStr error}") state)
          onError next) onError

private theorem actionPre_get (post : State → State → Prop) (onError : Errors) :
    actionPre get post onError = fun state => post state state := rfl

private theorem actionPre_set (next : State) (post : PUnit → State → Prop) (onError : Errors) :
    actionPre (set next) post onError = fun _ => post () next := rfl

theorem actionPre_afterLocalWrite (id : LocalId) (storageLive : Bool) (post : Unit → State → Prop)
    (onError : Errors) :
    actionPre (MachineHooks.afterLocalWrite id storageLive) post onError =
      afterLocalWritePre id storageLive post onError := by
  funext before
  simp only [MachineHooks.afterLocalWrite, afterLocalWritePre, actionPre_bind_fun,
    actionPre_currentFrame, currentFramePre]
  cases before.stack.currentFrame? with
  | none => rfl
  | some frame =>
    dsimp only
    cases tracked : frame.extra.dataRace with
    | none => rfl
    | some clocks =>
      simp only [actionPre_bind_fun, actionPre_get]
      obtain ⟨stack, machine⟩ := before
      obtain ⟨memory, tracker, dataRace, threads, raceAllocations, spans, user⟩ := machine
      cases dataRace with
      | none => rfl
      | some global =>
        dsimp only
        conv =>
          lhs
          arg 1
          change (pure global : MachineHooks.M K U Miri.Concurrency.GlobalState)
        simp only [actionPre_pure_fun, actionPre_set, actionPre_setCurrentFrame]
        congr 1
        funext value state
        cases (Miri.Concurrency.LocalRace.localWrite clocks global threads id storageLive).outcome with
        | error => rfl
        | ok value => cases value; rfl

open Miri.Input in
/-- The compiler layout leaf reads the current frame before querying its
concrete type and layout. A failed query leaves that state intact. -/
theorem actionPre_computeLocalLayout (prepared : CompilerProviders.Prepared) (id : Miri.MIR.LocalId)
    (post : LocalLayout → State → Prop) (onError : Errors) :
    actionPre (CompilerFrameContext.computeLocalLayout prepared id) post onError =
      currentFramePre (fun frame before =>
        match CompilerFrameContext.localType prepared frame id with
        | .error error => onError (.unsupported s!"compiler frame query: {error}") before
        | .ok ty =>
          match prepared.runtime.lookup ty with
          | .error error => onError (.unsupported s!"compiler frame query: {error}") before
          | .ok layout => post layout before) onError := by
  funext before
  simp only [CompilerFrameContext.computeLocalLayout, actionPre_bind_fun,
    actionPre_currentFrame, currentFramePre]
  cases before.stack.currentFrame? with
  | none => rfl
  | some frame =>
    dsimp only
    cases CompilerFrameContext.localType prepared frame id with
    | error => rfl
    | ok ty =>
      conv =>
        lhs
        arg 1
        change (pure ty : MachineHooks.M K U TyId)
      simp only [actionPre_pure_fun]
      cases prepared.runtime.lookup ty <;> rfl

open Miri.ABI Miri.Input in
/-- Dynamic allocation pulls back through size and alignment first. Only a
known size reaches the stack allocator, whose errors retain its output state. -/
theorem actionPre_compilerAllocateDyn {C : Type} [DecidableEq K]
    (prepared : CompilerProviders.Prepared) (allocation : PlaceMachine.AllocationConfig K U)
    (dynamic : DynamicLayoutHooks Provenance State C) (budget : Nat) (choice : C)
    (deallocate : Pointer (Option Provenance) → MachineHooks.M K U Unit)
    (layout : LocalLayout) (metadata : MemPlaceMeta Provenance)
    (post : MemPlace Provenance → State → Prop) (onError : Errors) :
    actionPre ((CompilerStorage.hooks prepared allocation dynamic budget choice deallocate).allocateDyn
      layout metadata) post onError =
      actionPre (DynamicLayout.sizeAndAlignFromMeta dynamic choice budget metadata layout) (fun
        | none => onError (.invalidProgram "cannot allocate space for extern type with unknown size")
        | some (size, align) =>
          actionPre (PlaceMachine.allocateStackRaw allocation size align)
            (fun pointer => post ⟨pointer, metadata, none⟩) onError) onError := by
  simp only [CompilerStorage.hooks, actionPre_bind_fun]
  congr 1
  funext result
  cases result with
  | none => rfl
  | some dimensions =>
    rcases dimensions with ⟨size, align⟩
    simp only [actionPre_bind_fun, actionPre_pure_fun]

end Miri.Verification.StorageLiveWP

/-- Reduce an exact storage-live WP at the selected MIR statement or effect.
Further assumptions about the state and the storage effects can be supplied to simp. -/
macro "miri_storage_live" : tactic =>
  `(tactic| simp only [Miri.Verification.StorageLiveWP.statement_storageLive, Miri.Verification.StorageLiveWP.wp_storageLiveDyn,
    Miri.Verification.StorageLiveWP.actionPre_storageLiveDyn, Miri.Verification.StorageLiveWP.storageLiveDynPre, Miri.Verification.StorageLiveWP.valuePre,
    Miri.Verification.StorageLiveWP.localLayoutPre, Miri.Verification.StorageLiveWP.installPre, Miri.Verification.StorageLiveWP.stackCheck,
    Miri.Verification.StorageLiveWP.actionPre_afterLocalWrite, Miri.Verification.StorageLiveWP.afterLocalWritePre,
    Miri.Verification.StorageLiveWP.currentFramePre, Miri.Verification.StorageLiveWP.setCurrentFramePre, Miri.Verification.RvalueWP.scalarCheckPre,
    Miri.Interpreter.MemPlaceMeta.hasMeta,
    Miri.Verification.StorageLiveWP.actionPre_computeLocalLayout,
    Miri.Verification.StorageLiveWP.actionPre_compilerAllocateDyn,
    Miri.Verification.StackAllocationWP.actionPre_allocateStackRaw,
    Miri.Verification.StackAllocationWP.allocateStackRawPre,
    Miri.Verification.StackAllocationWP.actionPre_initializeAllocation,
    Miri.Verification.StackAllocationWP.initializeAllocationPre,
    Miri.Verification.StackAllocationWP.initStackExtraPre,
    Miri.Verification.StackAllocationWP.machinePre_evalConfigurationTail,
    Miri.Verification.StackAllocationWP.actionPre_evalConfigurationRootAddress])

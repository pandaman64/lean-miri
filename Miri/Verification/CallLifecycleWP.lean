import Miri.Interpreter.ExecutionMachine
import Miri.Verification.RvalueWP

/-! Exact weakest preconditions for the canonical frame insertion and publication hooks. -/

namespace Miri.Verification.CallLifecycleWP

open Miri.Interpreter Miri.MIR Miri.Memory RvalueWP Std.WP

variable {K U C O X Host : Type}
local notation "State" => MachineHooks.State K U
local notation "Errors" => StepError → State → Prop

/-- Update the active thread's relevance cache after insertion. The stack and
cache on either error branch are the ones left by required-constant evaluation. -/
def afterPushPre (debugAssertions : Bool) (post : Unit → State → Prop)
    (onError : Errors) (state : State) : Prop :=
  match FrameRelevance.afterPushResult debugAssertions state with
  | .ok value after => post value after
  | .error error failed => onError error failed

theorem afterPushPre_eq_actionPre (debugAssertions : Bool) (post : Unit → State → Prop)
    (onError : Errors) :
    afterPushPre debugAssertions post onError =
      actionPre (FrameRelevance.afterStackPush debugAssertions) post onError := by
  funext state
  unfold afterPushPre actionPre
  rw [FrameRelevance.afterPushResult_eq]
  cases FrameRelevance.afterStackPush debugAssertions state <;> rfl

private theorem preGet (post : State → State → Prop) (onError : Errors) (state : State) :
    actionPre (get : MachineHooks.M K U State) post onError state = post state state := rfl

private theorem preSet (state : State) (post : PUnit → State → Prop) (onError : Errors) :
    actionPre (set state : MachineHooks.M K U PUnit) post onError = fun _ => post () state := rfl

private theorem preModify (f : State → State) (post : PUnit → State → Prop) (onError : Errors) :
    actionPre (modify f : MachineHooks.M K U PUnit) post onError = fun state => post () (f state) := rfl

/-- Frame initialization samples borrow tracking before compiler relevance
queries and local race tracking after them. -/
def initFramePre (compiler : FrameMetadata.CompilerHooks K U)
    (frame : Frame Provenance LocalLayout Unit)
    (post : Frame Provenance LocalLayout MachineHooks.FrameExtra → State → Prop)
    (onError : Errors) (before : State) : Prop :=
  actionPre (compiler.requiresCallerLocation frame.functionInstance) (fun tracked =>
    if tracked then finish 0 else
      actionPre (compiler.isLocalDefinition frame.functionInstance) (fun localDef =>
        if localDef then finish 255 else
          actionPre (compiler.definitionCrate frame.functionInstance) (fun crate =>
            actionPre (compiler.userRelevantCrate crate) (fun relevant =>
              finish (if relevant then 255 else 1)) onError) onError) onError) onError before
where
  finish relevance ready := post {
    body := frame.body, bodyIdentity := frame.bodyIdentity
    functionInstance := frame.functionInstance
    extra := {
      borrowTracker := before.machine.borrowTracker.map fun _ => {}
      catchUnwind := none
      userRelevance := relevance
      dataRace := ready.machine.dataRace.map fun _ => {} }
    returnContinuation := frame.returnContinuation, returnPlace := frame.returnPlace
    localsIdentity := frame.localsIdentity
    locals := frame.locals, vaList := frame.vaList, trackCallerArg := frame.trackCallerArg
    location := frame.location } ready

theorem initFramePre_eq_actionPre (compiler : FrameMetadata.CompilerHooks K U)
    (frame : Frame Provenance LocalLayout Unit)
    (post : Frame Provenance LocalLayout MachineHooks.FrameExtra → State → Prop)
    (onError : Errors) :
    initFramePre compiler frame post onError =
      actionPre (MachineHooks.initFrame (FrameMetadata.userRelevance compiler) frame)
        post onError := by
  funext before
  simp only [initFramePre, MachineHooks.initFrame, actionPre_bind, preGet]
  simp only [FrameMetadata.userRelevance, actionPre_bind, actionPre_bind_fun, actionPre_ite]
  congr 1
  funext tracked
  cases tracked
  · simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    funext localDef
    cases localDef
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      funext crate
      congr 1
      funext relevant
      cases relevant <;> rfl
    · rfl
  · rfl

/-- Check the root-frame condition before issuing a locals identity. Span and
frame initialization errors precede insertion. Required-constant errors retain
the inserted frame and bypass the relevance-cache update. -/
def pushRawPre (h : CallMachine.Lifecycle K U C) (debugAssertions : Bool)
    (fn : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (post : Unit → State → Prop)
    (onError : Errors) (before : State) : Prop :=
  let isStop := match continuation with | .stop _ => true | .goto .. => false
  if debugAssertions && before.stack.frames.isEmpty != isStop then
    onError (.stack (.rootFrameCondition before.stack.frames.isEmpty isStop)) before
  else
    let (machine, identity) := h.freshLocalsIdentity before.machine
    actionPre (h.preambleSpan body) (fun span =>
      let frame := Frame.create body fn () continuation destination span identity
      initFramePre h.compiler frame (fun initialized state =>
          actionPre (h.requiredConstants body) (fun _ => afterPushPre debugAssertions post onError)
            onError {state with stack := ⟨state.stack.frames.push initialized⟩}) onError)
      onError {before with machine}

theorem pushRawPre_eq_actionPre (h : CallMachine.Lifecycle K U C) (debugAssertions : Bool)
    (fn : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (post : Unit → State → Prop) (onError : Errors) :
    pushRawPre h debugAssertions fn body destination continuation post onError =
      actionPre (CallMachine.pushRaw h debugAssertions fn body destination continuation) post onError := by
  funext before
  simp only [pushRawPre, CallMachine.pushRaw, actionPre_bind, preGet, actionPre_ite]
  rcases supply : h.freshLocalsIdentity before.machine with ⟨machine, identity⟩
  simp only [actionPre_bind_fun, preSet, preModify, afterPushPre_eq_actionPre,
    initFramePre_eq_actionPre]
  cases continuation <;> cases debugAssertions <;> cases before.stack.frames.isEmpty <;>
    simp [actionPre_throw]

/-- Trivially sized dead locals with local race tracking disabled become
uninitialized immediates without running layout or allocation queries. -/
theorem storageLive_trivial_dead (storage : MachineHooks.StorageHooks K U) (localId : LocalId)
    (post : Unit → State → Prop) (onError : Errors) (before : State)
    (frame updated : Frame Provenance LocalLayout MachineHooks.FrameExtra) (ty : TyId)
    (slot : LocalState Provenance LocalLayout)
    (current : before.stack.currentFrame? = some frame)
    (nonempty : before.stack.frames.isEmpty = false)
    (selected : frame.getLocal localId = .ok slot) (dead : slot.value = .dead)
    (localType : frame.body.locals[localId]? = some ty)
    (trivial : storage.veryTriviallySized ty = .ok true)
    (noRace : frame.extra.dataRace = none)
    (replaced : frame.replaceLocalValue localId (.live (.immediate .uninit)) = .ok updated) :
    actionPre (MachineHooks.storageLiveDyn storage localId .none) post onError before =
      post () {before with stack := ⟨before.stack.frames.pop.push updated⟩} := by
  simp only [MachineHooks.storageLiveDyn, MachineHooks.currentFrame, actionPre_bind, preGet, current,
    actionPre_pure, selected, MachineHooks.storageResult_ok, localType, trivial, ↓reduceIte,
    MemPlaceMeta.hasMeta, Bool.false_eq_true]
  simp only [MachineHooks.afterLocalWrite, MachineHooks.currentFrame, actionPre_bind, preGet, current,
    actionPre_pure, noRace, selected, MachineHooks.storageResult_ok, replaced]
  simp only [MachineHooks.setCurrentFrame, actionPre_bind, preGet, nonempty, Bool.false_eq_true,
    ↓reduceIte, dead, MachineHooks.deallocateLocal_dead, preSet, actionPre_pure]

/-- The return slot becomes live before annotation checks. The selected
temporary slots then become live in source order. -/
def liveTempsPre (storage : MachineHooks.StorageHooks K U) (post : State → Prop)
    (onError : Errors) : List LocalId → State → Prop
  | [] => post
  | id :: ids => actionPre (MachineHooks.storageLiveDyn storage id .none)
      (fun _ => liveTempsPre storage post onError ids) onError

private theorem liveTempsPre_eq (storage : MachineHooks.StorageHooks K U)
    (post : PUnit → State → Prop) (onError : Errors) (ids : List LocalId) :
    liveTempsPre storage (post ()) onError ids =
      actionPre (forIn ids PUnit.unit (fun id _ => do
        MachineHooks.storageLiveDyn storage id .none
        pure (.yield ()))) post onError := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp only [liveTempsPre, List.forIn_cons, actionPre_bind_fun, ih]
    congr 1

/-- Publish the first MIR location only after all applicable storage operations
succeed. Any failure leaves the return slot and earlier temporary effects intact. -/
def pushDonePre (h : CallMachine.Lifecycle K U C) (post : Unit → State → Prop)
    (onError : Errors) : State → Prop :=
  actionPre (MachineHooks.storageLiveDyn h.storage 0 .none) (fun _ state =>
    match state.stack.currentFrame? with
    | none => onError (.stack .emptyStack) state
    | some frame =>
      match CallMachine.alwaysLiveVarsAndTemps frame.body with
      | .error error => onError error state
      | .ok ids =>
        liveTempsPre h.storage (fun ready =>
          match ready.stack.updateCurrentLocation (.mir .start) with
          | .ok stack => post () {ready with stack}
          | .error error => onError (.stack error) ready) onError ids.toList state) onError

theorem pushDonePre_eq_actionPre (h : CallMachine.Lifecycle K U C) (post : Unit → State → Prop)
    (onError : Errors) :
    pushDonePre h post onError = actionPre (CallMachine.pushDone h) post onError := by
  simp only [pushDonePre, CallMachine.pushDone, actionPre_bind_fun]
  congr 1
  funext value state
  simp only [MachineHooks.currentFrame, actionPre_bind, preGet]
  cases current : state.stack.currentFrame? with
  | none => rfl
  | some frame =>
    simp only [actionPre_pure]
    cases selected : CallMachine.alwaysLiveVarsAndTemps frame.body with
    | error error => rfl
    | ok ids =>
      simp only [actionPre_bind, actionPre_pure, ← Array.forIn_toList]
      rw [liveTempsPre_eq h.storage (fun _ ready =>
        match ready.stack.updateCurrentLocation (.mir .start) with
        | .ok stack => post () {ready with stack}
        | .error error => onError (.stack error) ready) onError]
      congr 1
      funext value ready
      simp only [actionPre_bind, preGet]
      cases ready.stack.updateCurrentLocation (.mir .start) <;> rfl

section Canonical
variable [DecidableEq K]

theorem wp_pushRaw (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (fn : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (post : Unit → State → Prop) (onError : Errors) :
    wp ((ExecutionMachine.callHooks config limits).pushRaw choice fn body destination continuation)
        post onError =
      let checked := ExecutionMachine.withValidation config limits
      pushRawPre checked.lifecycle checked.compiler.debugAssertions fn body destination continuation
        post onError := by
  rw [pushRawPre_eq_actionPre, actionPre_eq_wp]
  rfl

theorem wp_afterFrameInit (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (post : Unit → State → Prop) (onError : Errors) :
    wp ((ExecutionMachine.callHooks config limits).afterFrameInit choice) post onError = post () :=
  rfl

theorem wp_pushDone (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (post : Unit → State → Prop) (onError : Errors) :
    wp ((ExecutionMachine.callHooks config limits).pushDone choice) post onError =
      pushDonePre (ExecutionMachine.withValidation config limits).lifecycle post onError := by
  rw [pushDonePre_eq_actionPre, actionPre_eq_wp]
  rfl

@[spec]
theorem spec_pushRaw (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (fn : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (post : Unit → State → Prop) (onError : Errors) :
    Triple ((ExecutionMachine.callHooks config limits).pushRaw choice fn body destination continuation)
      (let checked := ExecutionMachine.withValidation config limits
       pushRawPre checked.lifecycle checked.compiler.debugAssertions fn body destination continuation
         post onError) post onError := by
  apply Triple.iff.mpr
  rw [wp_pushRaw]
  exact fun _ h => h

@[spec]
theorem spec_afterFrameInit (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (post : Unit → State → Prop) (onError : Errors) :
    Triple ((ExecutionMachine.callHooks config limits).afterFrameInit choice) (post ()) post onError := by
  apply Triple.iff.mpr
  rw [wp_afterFrameInit]
  exact fun _ h => h

@[spec]
theorem spec_pushDone (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (post : Unit → State → Prop) (onError : Errors) :
    Triple ((ExecutionMachine.callHooks config limits).pushDone choice)
      (pushDonePre (ExecutionMachine.withValidation config limits).lifecycle post onError)
      post onError := by
  apply Triple.iff.mpr
  rw [wp_pushDone]
  exact fun _ h => h

theorem actionPre_pushRaw (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (fn : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace Provenance)
    (continuation : ReturnContinuation) (post : Unit → State → Prop) (onError : Errors) :
    actionPre ((ExecutionMachine.callHooks config limits).pushRaw choice fn body destination continuation)
        post onError =
      let checked := ExecutionMachine.withValidation config limits
      pushRawPre checked.lifecycle checked.compiler.debugAssertions fn body destination continuation
        post onError := by
  rw [actionPre_eq_wp, wp_pushRaw]

theorem actionPre_afterFrameInit (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (post : Unit → State → Prop) (onError : Errors) :
    actionPre ((ExecutionMachine.callHooks config limits).afterFrameInit choice) post onError = post () :=
  rfl

theorem actionPre_pushDone (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits) (choice : C)
    (post : Unit → State → Prop) (onError : Errors) :
    actionPre ((ExecutionMachine.callHooks config limits).pushDone choice) post onError =
      pushDonePre (ExecutionMachine.withValidation config limits).lifecycle post onError := by
  rw [actionPre_eq_wp, wp_pushDone]

end Canonical

end Miri.Verification.CallLifecycleWP

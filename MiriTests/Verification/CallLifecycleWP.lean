import Miri.Verification.CallLifecycleWP
import Miri.Verification.CallWP

namespace MiriTests.Verification.CallLifecycleWP

open Miri.Interpreter Miri.MIR Miri.Memory Miri.Verification
open Miri.Verification.CallLifecycleWP RvalueWP Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "State" => MachineHooks.State K U
local notation "Errors" => StepError → State → Prop
local notation "MachineFrame" => Frame Provenance LocalLayout MachineHooks.FrameExtra

private abbrev lifecycle (config : Config) (limits : ExecutionMachine.Limits) :=
  (ExecutionMachine.withValidation config limits).lifecycle

private def inserted (before : State) (fn : CallInstance) (body : LoadedBody)
    (destination : RuntimeStackPlace Provenance) (target : Option BasicBlockId)
    (span : SpanRef) (identity : LocalsIdentity) : State :=
  let frame := Frame.create body fn () (.goto target .Continue) destination span identity
  let initialized : MachineFrame := {
    body := frame.body, bodyIdentity := frame.bodyIdentity, functionInstance := frame.functionInstance
    extra := {
      borrowTracker := before.machine.borrowTracker.map fun _ => {}
      catchUnwind := none
      userRelevance := 0
      dataRace := before.machine.dataRace.map fun _ => {} }
    returnContinuation := frame.returnContinuation, returnPlace := frame.returnPlace
    localsIdentity := frame.localsIdentity
    locals := frame.locals, vaList := frame.vaList, trackCallerArg := frame.trackCallerArg
    location := frame.location }
  { before with stack := ⟨before.stack.frames.push initialized⟩ }

/-- Required-constant failure in an ordinary nested call keeps the newly
inserted preamble frame, including the fresh locals identity. -/
theorem nestedPushConstantFailure (config : Config) (limits : ExecutionMachine.Limits)
    (before : State) (machine : MachineHooks.MachineState K U) (fn : CallInstance)
    (body : LoadedBody) (destination : RuntimeStackPlace Provenance) (target : Option BasicBlockId)
    (span : SpanRef) (identity : LocalsIdentity) (error : StepError)
    (post : Unit → State → Prop) (onError : Errors)
    (nonempty : before.stack.frames.isEmpty = false)
    (fresh : (lifecycle config limits).freshLocalsIdentity before.machine = (machine, identity))
    (preamble : (lifecycle config limits).preambleSpan body {before with machine} =
      .ok span {before with machine})
    (tracked : (lifecycle config limits).compiler.requiresCallerLocation fn {before with machine} =
      .ok true {before with machine})
    (rejected : let failed := inserted {before with machine} fn body destination target span identity
      (lifecycle config limits).requiredConstants body failed = .error error failed)
    (classified : onError error (inserted {before with machine} fn body destination target span identity)) :
    Triple ((ExecutionMachine.callHooks config limits).pushRaw () fn body destination
      (.goto target .Continue)) (· = before) post onError := by
  vcgen
  rename_i state atEntry
  subst state
  simp only [pushRawPre, nonempty, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, fresh,
    actionPre_ok preamble, initFramePre, Frame.create, actionPre_ok tracked]
  change actionPre ((lifecycle config limits).requiredConstants body) _ onError
    (inserted {before with machine} fn body destination target span identity)
  simpa only [actionPre, rejected] using classified

omit [DecidableEq K] in
/-- When the relevance cache is empty, successful insertion chooses the new
top frame and writes its index into the active thread. -/
theorem cacheUsesNewTopFrame (machine : MachineHooks.MachineState K U)
    (older : Array MachineFrame) (callee : MachineFrame) (thread : Miri.Concurrency.ThreadRecord)
    (post : Unit → State → Prop) (onError : Errors)
    (active : machine.threads.activeThread? = some thread)
    (uncached : thread.topUserRelevantFrame = none) :
    actionPre (FrameRelevance.afterStackPush false) post onError ⟨⟨older.push callee⟩, machine⟩ ↔
      post () {stack := ⟨older.push callee⟩, machine := {machine with threads := {
        machine.threads with threads := machine.threads.threads.mapIdx fun i t =>
          if i == machine.threads.activeThread.toNat then
            {t with topUserRelevantFrame := some older.size} else t}}} := by
  rw [← afterPushPre_eq_actionPre]
  simp [afterPushPre, FrameRelevance.afterPushResult, Stack.currentFrame?, FrameRelevance.top,
    active, uncached]

/-- If the return slot can become live but the MIR's temporary annotations
are malformed, the error continuation observes the live return slot and the
original preamble location. This exercises the canonical publication equation
with the return-slot storage operation reduced to the updated frame. -/
theorem publishAnnotationFailure (config : Config) (limits : ExecutionMachine.Limits)
    (before : State) (frame updated : MachineFrame) (ty : TyId)
    (slot : LocalState Provenance LocalLayout) (error : StepError)
    (post : Unit → State → Prop) (onError : Errors)
    (current : before.stack.currentFrame? = some frame)
    (nonempty : before.stack.frames.isEmpty = false)
    (selected : frame.getLocal 0 = .ok slot) (dead : slot.value = .dead)
    (localType : frame.body.locals[0]? = some ty)
    (trivial : (lifecycle config limits).storage.veryTriviallySized ty = .ok true)
    (noRace : frame.extra.dataRace = none)
    (replaced : frame.replaceLocalValue 0 (.live (.immediate .uninit)) = .ok updated)
    (annotations : CallMachine.alwaysLiveVarsAndTemps updated.body = .error error) :
    actionPre ((ExecutionMachine.callHooks config limits).afterFrameInit ())
      (fun _ => actionPre ((ExecutionMachine.callHooks config limits).pushDone ()) post onError)
      onError before ↔ onError error {before with stack := ⟨before.stack.frames.pop.push updated⟩} := by
  rw [actionPre_afterFrameInit, actionPre_pushDone]
  unfold pushDonePre
  rw [storageLive_trivial_dead _ _ _ _ _ frame updated ty slot current nonempty selected dead
    localType trivial noRace replaced]
  simp [Stack.currentFrame?, annotations]

/-- In the common no-temporary case the canonical finish hook publishes the MIR
entry location after making the return slot live. The opaque compiler and
protection effects feed directly into the concrete lifecycle rule. -/
theorem finishPublishesReturnSlot (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (abi : Miri.ABI.FnAbi TyId) (destination : MPlaceTy Provenance)
    (preamble returnSpan : SpanRef)
    (before spanRead inReturn checked afterProtect restored : State)
    (frame updated : MachineFrame) (ty : TyId) (slot : LocalState Provenance LocalLayout)
    (stack : Stack Provenance LocalLayout MachineHooks.FrameExtra)
    (post : State → Prop) (onError : Errors)
    (span : (ExecutionMachine.callHooks config limits).localSpan body 0 before = .ok returnSpan spanRead)
    (returnLocation : Call.setSpan (ExecutionMachine.callHooks config limits) returnSpan spanRead = .ok () inReturn)
    (compatible : let call := ExecutionMachine.callHooks config limits
      call.checkArgumentCompat () (call.abiReturn abi) (call.abiReturn abi) inReturn = .ok true checked)
    (protect : (ExecutionMachine.callHooks config limits).protectArgument () destination checked =
      .ok () afterProtect)
    (restore : Call.setSpan (ExecutionMachine.callHooks config limits) preamble afterProtect = .ok () restored)
    (current : restored.stack.currentFrame? = some frame)
    (nonempty : restored.stack.frames.isEmpty = false)
    (selected : frame.getLocal 0 = .ok slot) (dead : slot.value = .dead)
    (localType : frame.body.locals[0]? = some ty)
    (trivial : (lifecycle config limits).storage.veryTriviallySized ty = .ok true)
    (noRace : frame.extra.dataRace = none)
    (replaced : frame.replaceLocalValue 0 (.live (.immediate .uninit)) = .ok updated)
    (annotations : CallMachine.alwaysLiveVarsAndTemps updated.body = .ok #[])
    (start : (⟨restored.stack.frames.pop.push updated⟩ :
      Stack Provenance LocalLayout MachineHooks.FrameExtra).updateCurrentLocation (.mir .start) =
        .ok stack) :
    wp (Call.finishFrameInit (ExecutionMachine.callHooks config limits) () body abi abi #[] false #[]
      ⟨.indirect destination.mplace, destination.layout⟩ preamble (0, 0))
      (fun _ => post) onError before ↔ post {restored with stack} := by
  rw [← actionPre_eq_wp, ← CallWP.finishFramePre_eq_actionPre]
  simp only [CallWP.finishFramePre, CallWP.setSpanPre_eq_actionPre, actionPre_ok span,
    actionPre_ok returnLocation, actionPre_ok compatible, actionPre_ok protect, actionPre_ok restore,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Array.size_empty,
    bne_self_eq_false, Nat.lt_irrefl, actionPre_afterFrameInit, actionPre_pushDone]
  unfold pushDonePre
  rw [storageLive_trivial_dead _ _ _ _ _ frame updated ty slot current nonempty selected dead
    localType trivial noRace replaced]
  simp [Stack.currentFrame?, annotations, liveTempsPre, start]

end MiriTests.Verification.CallLifecycleWP

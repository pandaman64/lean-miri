import duplicate_prefix.AsMutCurrentInstall
import duplicate_prefix.AsMutPush
import duplicate_prefix.AsMutFinish
import duplicate_prefix.CallLocalRead

namespace DuplicatePrefix.AsMutCurrentEntry
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

noncomputable def rawFrame (options : EvalConfigurationCore.Options) (state : RootState)
    (dest : RuntimeStackPlace Provenance) :=
  AsMutFrame.rawFrame options.userRelevantCrates (AsMutPush.fresh state.machine).1 dest (AsMutPush.fresh state.machine).2

noncomputable def done (frame : CompilerFrameContext.ActualFrame) :=
  AsMutDone.doneFrame {frame with location := .unwinding AsMutEntryFacts.asMutPreamble}

theorem coreOfInstall
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (older : Array CompilerFrameContext.ActualFrame) (caller installed : CompilerFrameContext.ActualFrame)
    (machine after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (index : MIR.LocalId) (valid : index < caller.locals.size)
    (old value : Immediate Provenance)
    (destCached : caller.locals[index].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : caller.locals[index].value = .live (.immediate old))
    (clocks : caller.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (thread : ThreadRecord) (relevantIndex : Nat) (relevantFrame : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let h := ExecutionMachine.callHooks cfg limits
    let before := Storage.withCurrent older caller machine
    let dest := (LocalPlaces.localRuntimePlace older.size caller index CopyCompilerFacts.destPointerLayout).stackView
    let raw := rawFrame options before dest
    let pushed := (AsMutPush.completed options.userRelevantCrates before dest relevantFrame).machine
    FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates before dest).stack
      thread.topUserRelevantFrame = some relevantIndex →
    (AsMutPush.pushed options.userRelevantCrates before dest).stack.frames[relevantIndex]? = some relevantFrame →
    h.withRetagMode () .FnEntry (AsMutCurrentInstall.action h value) (Storage.withCurrent (older.push caller) raw pushed) =
      .ok (1,1) (Storage.withCurrent (older.push caller) installed after) →
    installed.body = HelperCompilerFacts.asMutPtrBody.body →
    installed.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity →
    installed.functionInstance = HelperCompilerFacts.asMutPtrCall.callee →
    (installedValid : 0 < installed.locals.size) →
    installed.locals[0].value = .dead →
    installed.extra.dataRace = none →
    AsMutCallCore.core h ⟨.immediate value,RootCompilerFacts.sliceLayout⟩ dest before =
      .ok () (Storage.withCurrent (older.push caller) (done installed) after) := by
  intro cfg h before dest raw pushed top populated argument body identity callee valid0 dead0 noClocks
  have destination := CallLocalRead.place_to_op_cached options limits remaining span debug older caller machine index
    CopyCompilerFacts.destPointerLayout old valid destLive destCached (by decide +kernel) clocks ghost
  have pushedEq := AsMutPush.actual_push options () remaining span before dest thread relevantIndex relevantFrame
    active top populated
  have pushActual : h.pushRaw () HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody dest
      (.goto (some 7) .Unreachable) before =
      .ok () (Storage.withCurrent (older.push caller) raw pushed) := by
    change CallMachine.pushRaw cfg.lifecycle cfg.compiler.debugAssertions
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody dest
      (.goto (some 7) .Unreachable) before = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).debug,debug]
    exact pushedEq
  have current := CallEntryLocals.get_frame options limits remaining span (older.push caller) raw pushed
  have saved : raw.location = .unwinding AsMutEntryFacts.asMutPreamble := rfl
  have callerLocation : raw.trackCallerArg = none := rfl
  have setRaw : h.setFrame raw (Storage.withCurrent (older.push caller) raw pushed) =
      .ok () (Storage.withCurrent (older.push caller) raw pushed) := by
    exact CallEntryLocals.set_frame options limits remaining span (older.push caller) raw raw pushed
  have rawNoCaller : {raw with trackCallerArg := none} = raw := by
    rw [← callerLocation]
  have finished := AsMutFinish.finish options limits remaining span (older.push caller) installed after
    AsMutEntryFacts.asMutPreamble body identity callee valid0 dead0 noClocks
  unfold AsMutCallCore.core
  simp only [bind,EStateM.bind]
  erw [destination]
  dsimp only
  erw [pushActual]
  dsimp only
  erw [current]
  dsimp only
  rw [saved]
  simp only [pure,Pure.pure,EStateM.pure,bind,EStateM.bind]
  rw [←saved,rawNoCaller,setRaw]
  dsimp only
  unfold AsMutCurrentInstall.action at argument
  simp only [bind,EStateM.bind,pure,Pure.pure,EStateM.pure] at argument
  rw [argument]
  dsimp only
  change AsMutFinish.action h AsMutEntryFacts.asMutPreamble (Storage.withCurrent (older.push caller) installed after) = _
  exact finished

end DuplicatePrefix.AsMutCurrentEntry

#print axioms DuplicatePrefix.AsMutCurrentEntry.coreOfInstall

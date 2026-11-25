import ReflectedCallEntry

/-! Staged return equations for the reconstructed, protected `update` frame. -/

namespace CalleeSummaryReflected
open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.TreeBorrows Miri.Verification
open PointerObservation.Fixture GeneratedBodySafety

noncomputable def writeEntry : Except String (Config × State) := do
  let (config, callerProgram, caller) ← atBorrowedCall
  let compiler := reflectedRuntimeCompiler
  let some body := callerProgram.down.bodies[1]? | throw "compiled update body missing"
  let calls := compiler.lifecycle.calls.calls
  let some instanceBody := calls.bodies.find? (fun entry => entry.bodyIndex == body.identity.index)
    | throw "compiled update instance missing"
  let fn := instanceBody.fnInstance
  let some callerFrame := caller.stack.currentFrame? | throw "root frame missing"
  let some output := callerFrame.locals[4]?.bind (·.layout) | throw "return layout missing"
  let some arg := callerFrame.locals[5]?.bind (·.layout) | throw "argument layout missing"
  let checked := ExecutionMachine.withValidation config limits
  let hooks := ExecutionMachine.callHooks checked limits
  let (ready, prehook) := (ExecutionMachine.stepHooks config limits).beforeTerminator () caller
  if let .error error := prehook then throw (reprStr error)
  let destination : RuntimeStackPlace Provenance := .frameLocal 0 4 none output callerFrame.localsIdentity
  let pushed : Except String (ULift.{1} State) :=
    match hooks.pushRaw () fn body destination (.goto (some 1) .Unreachable) ready with
    | .ok () state => .ok (ULift.up state)
    | .error error _ => .error (reprStr error)
  let pushed ← pushed
  let pushed := pushed.down
  let some frame := pushed.stack.currentFrame? | throw "raw callee frame missing"
  let some live := pushed.machine.memory.live[allocId]? | throw "allocation missing"
  let some tracker := pushed.machine.borrowTracker | throw "borrow tracker missing"
  let some scope := frame.extra.borrowTracker | throw "callee borrow scope missing"
  let size := Size.ofBytes 1
  let (global, calleeProtector) := ({tracker.global with nextPointerTag := ⟨5, by decide⟩}).addProtector
    scope allocId calleeBorrow .StrongProtector
  let location := Tree.LocationState.newAccessed (.ReservedFrz false) .None
  let read := live.allocation.extra.performBorrowAccessRange (.concrete callBorrow)
    Size.ZERO size .Read global.protectedTags .VisitChildrenOfAccessed
  if read.status != .Completed then throw "callee retag read failed"
  let inserted := read.tree.newChild Size.ZERO (.concrete callBorrow) calleeBorrow
    (Miri.DataStructures.DedupRangeMap.new size location) (.ReservedFrz false) true
  if let .error error := inserted.outcome then throw (reprStr error)
  let extra := {frame.extra with borrowTracker := some calleeProtector}
  let argument := Immediate.scalar (Scalar.fromPointer config.access.runtime.base (pointer calleeBorrow 0))
  let locals := #[localImmediate .uninit, localImmediate argument (some arg)]
  let frame := {frame with extra, locals}
  let updated := {live with allocation := live.allocation.setExtra inserted.tree}
  let memory := {pushed.machine.memory with live := pushed.machine.memory.live.insert allocId updated}
  let machine := {pushed.machine with memory, borrowTracker := some {tracker with global}}
  let seeded := {pushed with stack := ⟨pushed.stack.frames.pop.push frame⟩, machine}
  match hooks.pushDone () seeded with
  | .ok () entered => .ok (config, entered)
  | .error error _ => .error (reprStr error)

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert
set_option maxRecDepth 65536
set_option maxHeartbeats 1900000
set_option cbv.maxSteps 160000
set_option pp.maxSteps 300


/-- State immediately before the emitted Return after committing the
protected scalar write and initializing the callee's return local. -/
noncomputable def returnEntry : Except String (Config × State) := do
  let (config, before) ← writeEntry
  let some frame := before.stack.currentFrame? | throw "callee missing"
  let some entry := before.machine.memory.live[allocId]? | throw "allocation missing"
  let some tracker := before.machine.borrowTracker | throw "borrow tracker missing"
  let bytes := allocRange Size.ZERO (Size.ofBytes 1)
  let write := entry.allocation.extra.performBorrowAccessRange (.concrete calleeBorrow)
    Size.ZERO (Size.ofBytes 1) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  if write.status != .Completed then throw "protected write failed"
  let value := Scalar.fromScalarInt (ScalarInt.ofUInt8 42)
  let allocation := entry.allocation.setExtra write.tree
  let written : Except String (ULift.{1} (Allocation Provenance BorrowTree)) :=
    match allocation.writeScalar config.access.runtime.base bytes value with
    | .ok () done => .ok (ULift.up done)
    | .error err _ => .error (reprStr err)
  let allocation ← written
  let stored := {entry with allocation := allocation.down}
  let memory := {before.machine.memory with live := before.machine.memory.live.insert allocId stored}
  let value := Scalar.fromScalarInt (ScalarInt.ofUInt8 7)
  let cached ← ((frame.getOrCacheLocalLayout 0 frame.returnPlace.toRuntimePlace.layout).map ULift.up).mapError reprStr
  let updated ← ((cached.down.1.setLocalOperand 0 (.immediate (.scalar value))).map ULift.up).mapError reprStr
  let frame := {updated.down with location := .mir ⟨0, 2⟩}
  let stack := ⟨before.stack.frames.pop.push frame⟩
  pure (config, {before with stack, machine := {before.machine with memory}})



/-- Run the canonical terminator pre-hook. Its counter and clock effects
are retained in every subsequent return phase. -/
noncomputable def returnReady : Except String (Config × State) := do
  let (config, before) ← returnEntry
  let (ready, result) := (ExecutionMachine.stepHooks config limits).beforeTerminator () before
  if let .error error := result then throw (reprStr error)
  pure (config, ready)

/-- Release the active callee's single protector, update relevance, then pop.
The callee frame remains active throughout the protector release. -/
noncomputable def expectedPop : Except String (Config × State × Frame Provenance LocalLayout MachineHooks.FrameExtra) := do
  let (config, state) ← returnReady
  let some active := state.stack.currentFrame? | throw "callee missing"
  let some owned := active.extra.borrowTracker | throw "callee tracker missing"
  let some tracker := state.machine.borrowTracker | throw "borrow tracker missing"
  let some slot := state.machine.memory.live[allocId]? | throw "caller allocation missing"
  let released := slot.allocation.extra.releaseProtector calleeBorrow tracker.global.protectedTags
  if released.status != .Released then throw "callee protector release failed"
  let slot := {slot with allocation := slot.allocation.setExtra released.tree}
  let memory := {state.machine.memory with live := state.machine.memory.live.insert allocId slot}
  let tracker := {tracker with global := tracker.global.endCall owned}
  let released := {state with machine := {state.machine with memory, borrowTracker := some tracker}}
  let ready ← match FrameRelevance.beforeStackPop released with
    | .ok () ready => pure (ULift.up ready)
    | .error error _ => throw (reprStr error)
  let popped ← ((ready.down.stack.popFrame).map ULift.up).mapError reprStr
  pure (config, {ready.down with stack := popped.down.1}, popped.down.2)

/-- Caller state after its immediate result local receives the returned byte. -/
noncomputable def expectedCopied : Except String (Config × State × Frame Provenance LocalLayout MachineHooks.FrameExtra) := do
  let (config, popped, callee) ← expectedPop
  let some frame := popped.stack.currentFrame? | throw "resumed caller missing"
  let value := Immediate.scalar (Scalar.fromScalarInt (Prov := Provenance) (ScalarInt.ofUInt8 7))
  let updated ← ((frame.setLocalOperand 4 (.immediate value)).map ULift.up).mapError reprStr
  let copied := {popped with stack := ⟨popped.stack.frames.pop.push updated.down⟩}
  pure (config, copied, callee)

noncomputable def expectedResume : Except String (Config × State) := do
  let (config, copied, _) ← expectedCopied
  let (resumed, result) := ControlFlow.goToBlock 1 copied
  if let .error error := result then throw (reprStr error)
  pure (config, resumed)
theorem returnReadReflected :
    match returnReady with
    | .error _ => False
    | .ok (config, before) =>
      match before.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout => (ExecutionMachine.terminatorHooks config limits).returnOperand () before =
          (before, .ok ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 7))), layout⟩) := by
  cbv <;> rfl

/-- Release and remove the active frame with the actual canonical pop callback. -/
theorem returnPopReflected :
    match returnReady, expectedPop with
    | .ok (config, before), .ok (_, after, frame) =>
      (ExecutionMachine.terminatorHooks config limits).popFrame () before = (after, .ok frame)
    | _, _ => False := by
  cbv <;> rfl

/-- Copy the return byte into caller local 4 before destination validation. -/
theorem copyNoValidateReflected (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    match expectedPop, expectedCopied with
    | .ok (config, before, frame), .ok (_, after, _) =>
      match frame.locals[0]?.bind (·.layout) with
      | none => False
      | some layout =>
        let value : OpTy Provenance := ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 7))), layout⟩
        let validated := ExecutionMachine.withValidation config limits
        PlaceReadWriteWP.copyNoValidatePre (ExecutionMachine.projectionHooks validated).place validated.copy
          () value frame.returnPlace.toRuntimePlace true post onError before = post () after
    | _, _ => False := by
  cbv

/-- The detached callee frame has no indirect locals or varargs to deallocate. -/
theorem returnCleanupReflected :
    match expectedCopied with
    | .ok (config, before, frame) =>
      (ExecutionMachine.terminatorHooks config limits).cleanupFrame () false frame before = (before, .ok .normal)
    | .error _ => False := by
  cbv <;> rfl

/-- The assembled Shallow policy requests validation after the return copy. -/
theorem returnCopyEnforced :
    match expectedCopied with
    | .ok (config, state, frame) =>
      let checked := ExecutionMachine.withValidation config limits
      (ExecutionMachine.projectionHooks checked).place.enforceValidity () frame.returnPlace.toRuntimePlace.layout state =
        .ok true state
    | .error _ => False := by
  cbv <;> rfl

theorem sameReturnLayout :
    match expectedPop with
    | .ok (_, _, frame) => frame.locals[0]?.bind (·.layout) = some frame.returnPlace.toRuntimePlace.layout
    | .error _ => False := by
  cbv <;> rfl

/-- The return stays in the ordinary callee block and resumes caller block 1. -/
theorem returnShape :
    match returnReady, expectedPop with
    | .ok (_, ready), .ok (_, _, frame) =>
        ready.stack.currentFrame? = some frame ∧ frame.location = .mir ⟨0, 2⟩ ∧
        frame.body.basicBlocks[0]?.map (·.cleanup) = some false ∧
        frame.returnContinuation = .goto (some 1) .Unreachable
    | _, _ => False := by
  cbv <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem prehookRuns (config c' : Config) (before ready : State)
    (entered : returnEntry = .ok (config, before))
    (prepared : returnReady = .ok (c', ready)) :
    (ExecutionMachine.stepHooks config limits).beforeTerminator () before = (ready, .ok ()) := by
  unfold returnReady at prepared
  rw [entered] at prepared
  rcases actual : (ExecutionMachine.stepHooks config limits).beforeTerminator () before with ⟨after, result⟩
  cases result with
  | error error =>
    simp only [bind, Bind.bind, Except.bind, actual] at prepared
    contradiction
  | ok value =>
    cases value
    simp only [bind, Bind.bind, Except.bind, actual, pure, Pure.pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at prepared
    cases prepared.2
    rfl

/-- The reconstructed callee selects the emitted Return at bb0.2. -/
theorem returnSelectedReflected :
    match returnEntry with
    | .ok (_, before) => BodyCFG.selected before = some (⟨0, 2⟩, mir_1_bb0_2)
    | .error _ => False := by
  cbv <;> rfl

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``returnReadReflected, ``returnPopReflected, ``copyNoValidateReflected,
      ``returnCleanupReflected, ``returnCopyEnforced, ``sameReturnLayout,
      ``returnShape, ``prehookRuns, ``returnSelectedReflected] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

end CalleeSummaryReflected

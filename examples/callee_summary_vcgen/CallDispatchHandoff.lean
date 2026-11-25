import CallAbiLiteral
import Miri.Verification.CallDispatchWP

/-! Checked call-site arguments and destination for the emitted borrowed call. -/

namespace CalleeSummaryReflected
open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.TreeBorrows Miri.Verification
open PointerObservation.Fixture

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option cbv.maxSteps 170000
set_option pp.maxSteps 90
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert

attribute [local cbv_opaque] CompilerInstanceAbi.abiOfInstance reflectedRuntimeAbi

/-- Evaluate the emitted destination and operands after the canonical terminator
preamble, then pass the resolved callee, ABI, and cached argument to the
dispatch continuation. The callback receives the state left by the preamble. -/
theorem emittedCallHandoff
    (post : RuntimeStackPlace Provenance → EvaluatedCall Provenance Unit ExternAbi (FnAbi TyId) → State → Prop)
    (failure : StepError → State → Prop) :
    match atBorrowedCall with
    | .error _ => False
    | .ok (config, _, before) =>
      match GeneratedBodySafety.mir_0_bb0_7, before.stack.currentFrame? with
      | .terminator ⟨_, .Call func args dest ..⟩, some frame =>
        match frame.getLocalOperand 5, frame.getLocalLayout 5, frame.getLocalLayout 4 with
        | .ok operand, .ok (some layout), .ok (some destinationLayout) =>
          let checked := ExecutionMachine.withValidation config limits
          let hooks := ExecutionMachine.callHooks checked limits
          let preamble := TerminatorMachine.beforeTerminatorWithChoice checked.terminators
            (checked.preemptionChoice ())
          RvalueWP.actionPre preamble (fun _ =>
            RvalueWP.actionPre (hooks.evalPlace () dest false) (fun destination =>
              RvalueWP.actionPre (Call.evalCalleeAndArgs hooks () func args dest)
                (post destination) failure) failure) failure before =
            RvalueWP.actionPre preamble (fun _ =>
              post (.frameLocal 0 4 none destinationLayout frame.localsIdentity)
                ⟨.Instance 1, #[.Copy ⟨operand, layout⟩], .Rust, some reflectedRuntimeAbi, false⟩)
              failure before
        | _, _, _ => False
      | _, _ => False := by
  -- Rewrite the closed ABI query before reducing its dependent argument loop.
  cbv
  conv =>
    pattern (CompilerInstanceAbi.abiOfInstance _ _ _)
    tactic =>
      exact callAbiLiteralQuery
  cbv

private theorem emittedDispatchQueries :
    match atBorrowedCall with
    | .error _ => False
    | .ok (config, program, before) =>
      match before.stack.currentFrame?, program.down.bodies.find? (·.identity.index == 1) with
      | some frame, some body =>
        match frame.getLocalOperand 5, frame.getLocalLayout 5, frame.getLocalLayout 4 with
        | .ok operand, .ok (some layout), .ok (some destinationLayout) =>
          let checked := ExecutionMachine.withValidation config limits
          let hooks := ExecutionMachine.callHooks checked limits
          let args : Array (FnArg Provenance) := #[.Copy ⟨operand, layout⟩]
          let destination : RuntimeStackPlace Provenance :=
            .frameLocal 0 4 none destinationLayout frame.localsIdentity
          RvalueWP.actionPre
            (TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()))
            (fun _ ready =>
              hooks.instanceKind 1 ready = .ok (.Item 1) ready ∧
              hooks.isRustCall .Rust = false ∧
              hooks.findMirOrEvalFn () 1 reflectedRuntimeAbi args destination (some 1) .Unreachable ready =
                .ok (some (body, 1)) ready)
            (fun _ _ => False) before
        | _, _, _ => False
      | _, _ => False := by
  cbv

/-- Dispatch the resolved Rust item to the exact frame initializer. The
handoff retains the caller's destination, argument, return target, and error continuation. -/
theorem emittedDispatchHandoff (post : State → Prop) (failure : StepError → State → Prop) :
    match atBorrowedCall with
    | .error _ => False
    | .ok (config, program, before) =>
      match before.stack.currentFrame?, program.down.bodies.find? (·.identity.index == 1) with
      | some frame, some body =>
        match frame.getLocalOperand 5, frame.getLocalLayout 5, frame.getLocalLayout 4 with
        | .ok operand, .ok (some layout), .ok (some destinationLayout) =>
          let checked := ExecutionMachine.withValidation config limits
          let hooks := ExecutionMachine.callHooks checked limits
          let args : Array (FnArg Provenance) := #[.Copy ⟨operand, layout⟩]
          let destination : RuntimeStackPlace Provenance :=
            .frameLocal 0 4 none destinationLayout frame.localsIdentity
          let request : CallRequest Provenance Unit ExternAbi (FnAbi TyId) :=
            ⟨.Instance 1, .Rust, some reflectedRuntimeAbi, args, false, destination, some 1, .Unreachable⟩
          RvalueWP.actionPre
            (TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()))
            (fun _ ready =>
              CallWP.dispatchPre hooks () post failure limits.callDispatch request ready =
                CallWP.initStackFramePre hooks () 1 body reflectedRuntimeAbi args false destination
                  (.goto (some 1) .Unreachable) post failure (CallWP.canonicalRetagPullback checked limits ()) ready)
            failure before
        | _, _, _ => False
      | _, _ => False := by
  have queries := emittedDispatchQueries
  cases entered : atBorrowedCall with
  | error error => simp only [entered] at queries
  | ok result =>
    obtain ⟨config, program, before⟩ := result
    simp only [entered] at queries
    cases foundFrame : before.stack.currentFrame? with
    | none => simp only [foundFrame] at queries
    | some frame =>
      cases foundBody : program.down.bodies.find? (·.identity.index == 1) with
      | none => simp only [foundFrame, foundBody] at queries
      | some body =>
        cases foundOperand : frame.getLocalOperand 5 with
        | error error => simp only [foundFrame, foundBody, foundOperand] at queries
        | ok operand =>
          cases foundLayout : frame.getLocalLayout 5 with
          | error error => simp only [foundFrame, foundBody, foundOperand, foundLayout] at queries
          | ok sourceLayout =>
            cases sourceLayout with
            | none => simp only [foundFrame, foundBody, foundOperand, foundLayout] at queries
            | some layout =>
              cases foundDest : frame.getLocalLayout 4 with
              | error error => simp only [foundFrame, foundBody, foundOperand, foundLayout, foundDest] at queries
              | ok destLayout =>
                cases destLayout with
                | none => simp only [foundFrame, foundBody, foundOperand, foundLayout, foundDest] at queries
                | some destinationLayout =>
                  simp only [foundFrame, foundBody, foundOperand, foundLayout, foundDest] at queries ⊢
                  let checked := ExecutionMachine.withValidation config limits
                  let hooks := ExecutionMachine.callHooks checked limits
                  let args : Array (FnArg Provenance) := #[.Copy ⟨operand, layout⟩]
                  let destination : RuntimeStackPlace Provenance :=
                    .frameLocal 0 4 none destinationLayout frame.localsIdentity
                  let request : CallRequest Provenance Unit ExternAbi (FnAbi TyId) :=
                    ⟨.Instance 1, .Rust, some reflectedRuntimeAbi, args, false, destination, some 1, .Unreachable⟩
                  let preamble := TerminatorMachine.beforeTerminatorWithChoice checked.terminators
                    (checked.preemptionChoice ())
                  change RvalueWP.actionPre preamble _ _ before at queries ⊢
                  cases ready : preamble before with
                  | error error failed => simp only [RvalueWP.actionPre, ready] at queries
                  | ok _ readyState =>
                    simp only [RvalueWP.actionPre, ready] at queries ⊢
                    change CallWP.dispatchPre hooks () post failure 32 request readyState = _
                    have load : hooks.findMirOrEvalFn () 1 reflectedRuntimeAbi request.args
                        request.destination request.target
                        (if hooks.abiCanUnwind reflectedRuntimeAbi then request.unwind else .Unreachable)
                        readyState = .ok (some (body, 1)) readyState := by
                      simpa only [request, ite_self] using queries.2.2
                    rw [CallWP.dispatchPre_item hooks () 31 request post failure readyState readyState readyState
                      1 1 1 body reflectedRuntimeAbi rfl rfl queries.1 queries.2.1 load]
                    rw [CallWP.initStackFramePre_eq_wp (scope := CallWP.canonicalRetagPullback checked limits ()),
                      ← RvalueWP.actionPre_eq_wp]
                    simp only [request, ite_self] <;> rfl

private theorem protectedDepth (after : State) (observed : argumentHasStrongProtector after = true) :
    after.stack.frames.size = 2 := by
  simp only [argumentHasStrongProtector, CalleeSummaryExample.argumentHasStrongProtector,
    Id.run, pure, Pure.pure] at observed
  split at observed <;> try contradiction
  split at observed <;> try contradiction
  split at observed <;> try contradiction
  split at observed <;> try contradiction
  exact (of_decide_eq_true observed).1

/-- The canonical preamble preserves the caller stack. -/
theorem emittedCallPreambleDepth :
    match atBorrowedCall with
    | .error _ => False
    | .ok (config, _, before) =>
      let checked := ExecutionMachine.withValidation config limits
      RvalueWP.actionPre
        (TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()))
        (fun _ ready => ready.stack.frames.size = 1 ∧ ready.stack = before.stack) (fun _ _ => False) before := by
  cbv

private theorem callFrameIndex (config : Config) (state : State) (nonempty : state.stack.frames.isEmpty = false) :
    let hooks := ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits
    hooks.frameIndex state = .ok (state.stack.frames.size - 1) state := by
  change ((do
    match (← get).stack.frameIndex with
    | .ok index => pure index
    | .error error => throw (.stack error)) : RvalueM State Nat) state = _
  simp [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, Except.pure, Stack.frameIndex, nonempty]

/-- Read the caller cursor through the canonical call hooks. -/
theorem callCursor (config : Config) (before : State)
    (depth : before.stack.frames.size = 1)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (current : before.stack.currentFrame? = some frame) :
    let hooks := ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits
    hooks.frameIndex before = .ok 0 before ∧ hooks.getFrame before = .ok frame before := by
  have nonempty : before.stack.frames.isEmpty = false := by
    rw [Array.isEmpty_eq_false_iff]
    intro empty
    have impossible := congrArg Array.size empty
    simp [depth] at impossible
  constructor
  · simpa only [depth, Nat.sub_self] using callFrameIndex config before nonempty
  · change MachineHooks.currentFrame before = _
    simp [MachineHooks.currentFrame, get, getThe, MonadStateOf.get, EStateM.get,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, current]

/-- A protected callee frame advances past both ordinary-call progress
checks. The returned state passes directly to the success continuation. -/
theorem protectedCallProgress (config : Config) (before after : State)
    (depth : before.stack.frames.size = 1) (observed : argumentHasStrongProtector after = true)
    (location : FrameLocation) (post : State → Prop) (failure : StepError → State → Prop) :
    let hooks := ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits
    let finish := fun state : State =>
      if (some (1 : BasicBlockId)).isSome && state.stack.frames.size == before.stack.frames.size &&
          state.stack.currentFrame?.map (·.location) == before.stack.currentFrame?.map (·.location) then
        failure (.invalidProgram "evaluating this call made no progress") state
      else post state
    RvalueWP.actionPre hooks.stackIsEmpty (fun empty afterEmpty =>
      if empty then finish afterEmpty
      else RvalueWP.actionPre hooks.frameIndex (fun index afterIndex =>
        if index == 0 then
          RvalueWP.actionPre hooks.getFrame (fun frame afterFrame =>
            if frame.location == location then
              failure (.invalidProgram "evaluating this call made no progress") afterFrame
            else finish afterFrame) failure afterIndex
        else finish afterIndex) failure afterEmpty) failure after = post after := by
  let hooks := ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits
  have depthAfter := protectedDepth after observed
  have nonempty : after.stack.frames.isEmpty = false := by
    rw [Array.isEmpty_eq_false_iff]
    intro empty
    have impossible := congrArg Array.size empty
    simp [depthAfter] at impossible
  have empty : hooks.stackIsEmpty after = .ok false after := by
    change EStateM.Result.ok (ε := StepError) after.stack.frames.isEmpty after = _
    rw [nonempty]
  have index : hooks.frameIndex after = .ok 1 after := by
    simpa only [depthAfter] using callFrameIndex config after nonempty
  change RvalueWP.actionPre hooks.stackIsEmpty _ failure after = _
  rw [RvalueWP.actionPre_ok empty]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [RvalueWP.actionPre_ok index]
  simp [depth, depthAfter]

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``emittedCallHandoff, ``emittedDispatchHandoff,
      ``emittedCallPreambleDepth, ``callCursor, ``protectedCallProgress] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms emittedCallHandoff
#print axioms emittedDispatchHandoff
#print axioms protectedCallProgress
end CalleeSummaryReflected

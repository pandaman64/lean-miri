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

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``emittedCallHandoff, ``emittedDispatchHandoff] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms emittedCallHandoff
#print axioms emittedDispatchHandoff
end CalleeSummaryReflected

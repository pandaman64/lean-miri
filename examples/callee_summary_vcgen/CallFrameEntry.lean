import CallAbiLiteral
import Miri.Verification.PointerFormationWP

/-! Verify the exported call's frame creation and argument protection. -/

namespace CalleeSummaryReflected
open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.TreeBorrows Miri.Verification
open PointerObservation.Fixture

set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
set_option cbv.maxSteps 160000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert
attribute [local cbv_opaque] CompilerInstanceAbi.abiOfInstance
attribute [local cbv_opaque] ValidityVisitor.validatePlace ValidityVisitor.visit TypedRetag.machineRetagPtrValue
attribute [local cbv_eval] ValidityVisitor.validatePlace_shallow

local macro "check_call_reference" mutable:term : tactic => `(tactic|
  conv =>
    pattern ValidityVisitor.visit _ _ _ _ _ _
    tactic =>
      refine ValidityVisitor.visit_reference_local _ _ 31 _ _ _ ?retagged ?written
        $mutable ?pointer ?adjusted ?place ?scalar ?dyn ?classified ?read ?ranges ?reset
        ?metadata ?sized ?sizeAlign ?live ?access ?retag ?write ?formed ?nonNull ?inhabited
        ?alignment ?tracking
      case classified => cbv <;> rfl
      case read => cbv <;> rfl
      case ranges => rfl
      case reset => rfl
      case metadata => cbv <;> rfl
      case sized => cbv <;> rfl
      case sizeAlign => cbv <;> rfl
      case live => rfl
      case access => cbv <;> rfl
      case retag =>
        conv => lhs; cbv
        refine PointerFormationWP.machineRetagPtrValue_ok _ _ _ _ _ _ _ ?checks
        conv => cbv
        constructor <;> rfl
      case write => cbv <;> rfl
      case formed => cbv <;> rfl
      case nonNull => cbv <;> rfl
      case inhabited => cbv <;> rfl
      case alignment => cbv <;> rfl
      case tracking => rfl)

/-- The canonical frame initializer copies the argument into the callee
and protects the resulting reference in the live callee frame. -/
theorem initActualFrame :
    match atBorrowedCall with
    | .error _ => False
    | .ok (config, program, before) =>
      match before.stack.currentFrame?, program.down.bodies.find? (·.identity.index == 1),
          CallResolution.abiOfInstance reflectedRuntimeCompiler.lifecycle.calls.calls 1 #[] with
      | some frame, some body, .ok abi =>
        match frame.getLocal 5, frame.getLocalLayout 4 with
        | .ok ⟨.live operand, some sourceLayout⟩, .ok (some destinationLayout) =>
          let checked := ExecutionMachine.withValidation config limits
          let hooks := ExecutionMachine.callHooks checked limits
          let destination : RuntimeStackPlace Provenance :=
            .frameLocal 0 4 none destinationLayout frame.localsIdentity
          let args : Array (FnArg Provenance) := #[.Copy ⟨operand, sourceLayout⟩]
          RvalueWP.actionPre
            (TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()))
            (fun _ => CallWP.initStackFramePre hooks () 1 body abi args false destination
              (.goto (some 1) .Unreachable) (fun after => argumentHasStrongProtector after = true)
              (fun _ _ => False) (CallWP.canonicalRetagPullback checked limits ()))
            (fun _ _ => False) before
        | _, _ => False
      | _, _, _ => False := by
  rw [callAbiLiteralResolution]
  conv => cbv
  conv =>
    pattern CompilerInstanceAbi.abiOfInstance _ _ _
    tactic => exact callAbiLiteralQuery
  conv => cbv
  check_call_reference true
  conv => cbv
  trivial

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``initActualFrame] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms initActualFrame
end CalleeSummaryReflected

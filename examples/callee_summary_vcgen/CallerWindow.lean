import CalleeReturn
import CallerObservation

/-! The emitted caller checks the returned byte, observes the protected
callee write, and accesses the same allocation after protector release. -/

namespace CalleeSummaryExample

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification
open PointerObservation.Fixture
open RvalueWP Miri.TreeBorrows

set_option maxHeartbeats 4500000
set_option maxRecDepth 65536
set_option cbv.maxSteps 300000
set_option pp.maxSteps 350
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
attribute [local cbv_eval] Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert
attribute [local cbv_opaque] evalPre ValidityVisitor.validatePlace ValidityVisitor.visit
attribute [local cbv_eval] ValidityVisitor.validatePlace_shallow

private theorem usePre {P S C V : Type} (hooks : RvalueHooks P S C V) (choice : C)
    (operand : Operand) (retag : WithRetag) (dest : Place)
    (post : S → Prop) (failure : StepError → S → Prop) (before : S) :
    evalPre hooks choice (.Use operand retag) dest post failure before =
      actionPre (hooks.evalPlace choice dest true) (fun target =>
        actionPre (hooks.evalOperand choice operand (some (hooks.placeLayout target))) (fun value =>
          actionPre (hooks.withRetagMode choice (if retag == .Yes then .Default else .None)
            (hooks.copyOp choice value target)) (fun _ => post) failure) failure) failure before := rfl

private theorem binaryPre {P S C V : Type} (hooks : RvalueHooks P S C V) (choice : C)
    (operator : BinOp) (left right : Operand) (dest : Place)
    (post : S → Prop) (failure : StepError → S → Prop) (before : S) :
    evalPre hooks choice (.BinaryOp operator left right) dest post failure before =
      actionPre (hooks.evalPlace choice dest true) (fun target =>
        let layout := hooks.placeLayout target
        actionPre (hooks.evalOperand choice left (if operator.leftHomogeneous then some layout else none))
          (fun left => actionPre (hooks.readImmediate choice left) (fun left =>
            actionPre (hooks.evalOperand choice right (if operator.rightHomogeneous then some left.layout else none))
              (fun right => actionPre (hooks.readImmediate choice right) (fun right =>
                actionPre (hooks.binaryOp choice operator left right) (fun result =>
                  if result.layout == layout then
                    actionPre (hooks.writeImmediate choice result.imm target) (fun _ => post) failure
                  else failure (.invalidProgram "rvalue result layout mismatch")) failure) failure) failure)
              failure) failure) failure before := rfl

attribute [local cbv_eval] usePre binaryPre

attribute [local cbv_opaque] writeImmediateAfterAccess
attribute [local cbv_eval] writeImmediateAfterAccess_scalar

local macro "validate_caller_uint " byte:term : tactic =>
  `(tactic| (
    conv =>
      pattern (ValidityVisitor.visit _ _ 32 _ _ _)
      tactic =>
        refine ValidityVisitor.visit_integer (P := Provenance) _ _ 31 _ _ _
          (Scalar.fromScalarInt (ScalarInt.ofUInt8 $byte)) ?_ ?_ ?_ ?_ ?_
        all_goals first | rfl | cbv
    conv => cbv))

local macro "validate_caller_false" : tactic =>
  `(tactic| (
    conv =>
      pattern (ValidityVisitor.visit _ _ 32 _ _ _)
      tactic =>
        refine ValidityVisitor.visit_boolean (P := Provenance) _ _ 31 _ _ _
          (Scalar.fromBool false) ?_ false ?_ ?_ ?_ ?_ ?_
        all_goals first | rfl | cbv
    conv => cbv))

local macro "validate_caller_unit" : tactic =>
  `(tactic| (
    conv =>
      pattern (ValidityVisitor.visit _ _ 32 _ _ _)
      tactic =>
        refine ValidityVisitor.visit_fieldless (P := Provenance) _ _ 31 _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals first | rfl | cbv
    conv => cbv))

local macro "caller_row" : tactic =>
  `(tactic| (
    conv => cbv
    refine ⟨rfl, ?_⟩
    intro choice _
    cases choice))

/-- Starting from the exact returned state, the emitted checks take their
accepting branches at bb3.0 and bb5.0, then write 99 to the caller allocation. -/
theorem generatedCallerObservation :
    match CalleeSummaryReflected.expectedResume with
    | .error _ => False
    | .ok (config, state) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun final => bytesAt 0 final = some (.ok #[99])) (fun _ _ => False)
        (callerRows config) state := by
  -- bb1 checks the callee result.
  caller_row
  caller_row
  caller_row
  caller_row
  caller_row
  caller_row
  conv => cbv
  validate_caller_uint 7
  caller_row
  conv => cbv
  validate_caller_false
  caller_row
  -- bb3 reads and checks the byte written by the callee.
  caller_row
  caller_row
  conv => cbv
  validate_caller_unit
  caller_row
  caller_row
  caller_row
  caller_row
  caller_row
  caller_row
  conv => cbv
  validate_caller_uint 42
  caller_row
  conv => cbv
  validate_caller_false
  caller_row
  -- bb5 writes through the caller place.
  caller_row
  caller_row
  conv => cbv
  validate_caller_unit
  caller_row
  caller_row
  caller_row
  conv => cbv
  conv =>
    pattern (ValidityVisitor.visit _ _ 32 _ _ _)
    tactic =>
      refine ValidityVisitor.visit_integer_memory (P := Provenance) _ _ 31 _ _ _
        (Scalar.fromScalarInt (ScalarInt.ofUInt8 99)) ?layout ?mem ?ranges ?updated
        ?classified ?read ?clear ?operand ?reset ?tracked ?sized ?marked
      case classified => cbv <;> rfl
      case read => cbv <;> rfl
      case clear => cbv <;> rfl
      case operand => cbv <;> rfl
      case reset => cbv <;> rfl
      case tracked => cbv <;> rfl
      case sized => cbv <;> rfl
      case marked => cbv <;> rfl
  conv => cbv
  try rfl

open Lean Elab Command in
run_cmd liftTermElabM do
  for dependency in (← collectAxioms ``generatedCallerObservation) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "generatedCallerObservation depends on unapproved axiom {dependency}"

#print axioms generatedCallerObservation

end CalleeSummaryExample

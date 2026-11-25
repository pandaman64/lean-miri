import GeneratedPointer

/-! Verify the imported mutable-reference store at its actual prepared entry. -/
namespace PointerObservation

open Miri.ABI Miri.Interpreter Miri.Memory Miri.Verification Fixture

set_option maxHeartbeats 2000000
set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
attribute [local cbv_opaque] RvalueWP.evalPre ValidityVisitor.validatePlace ValidityVisitor.visit
attribute [local cbv_eval] ValidityVisitor.validatePlace_shallow
attribute [local cbv_opaque] writeImmediateAfterAccess
attribute [local cbv_eval] writeImmediateAfterAccess_scalar
attribute [local cbv_opaque] TypedRetag.machineRetagPtrValue

local macro "advance_mutable_row" : tactic =>
  `(tactic| (refine ⟨rfl, ?_⟩; intro choice _; cases choice; conv => cbv))

/-- Both mutable reborrows and the store succeed for every initialized byte.
The emitted endpoint observes byte 73 through the second fresh tag. -/
theorem mutableWriteWindow (initial : UInt8) :
    match scenario 0 initial false with
    | .error _ => False
    | .ok (config, before) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun after => observed .mutableWrite initial after (.ok ()) = true)
        (fun error after => observed .mutableWrite initial after (.error error) = true)
        ((GeneratedBodySafety.window_0_bb0_0 config limits).take 6) before := by
  conv => cbv
  advance_mutable_row
  advance_mutable_row
  advance_mutable_row
  miri_check_fixture_reference true
  conv => cbv
  advance_mutable_row
  miri_check_fixture_reference true
  conv => cbv
  advance_mutable_row
  advance_mutable_row
  conv =>
    pattern ValidityVisitor.visit _ _ 32 _ _ _
    tactic =>
      refine ValidityVisitor.visit_integer_memory (P := Provenance) _ _ 31 _ _ _
        ?value ?layout ?memory ?ranges ?updated ?classified ?read ?clear ?operand
        ?reset ?tracked ?sized ?marked
      case classified => cbv <;> rfl
      case read => cbv <;> rfl
      case clear => cbv <;> rfl
      case operand => cbv <;> rfl
      case reset => cbv <;> rfl
      case tracked => cbv <;> rfl
      case sized => cbv <;> rfl
      case marked => cbv <;> rfl
  conv => cbv
  trivial

/-- The fixture's executable check is true for every initialized byte. -/
theorem mutableWriteChecked (initial : UInt8) : checked .mutableWrite initial = true :=
  (generatedPrefix_iff_checked .mutableWrite initial).mp (mutableWriteWindow initial)

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``mutableWriteWindow, ``mutableWriteChecked] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms mutableWriteWindow

end PointerObservation

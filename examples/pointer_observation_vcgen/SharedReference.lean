import GeneratedPointer
import Miri.Verification.CopyInitialWP

namespace PointerObservation

open Miri.ABI Miri.Interpreter Miri.Memory Miri.Verification Fixture
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
attribute [local cbv_opaque] Allocation.readScalar MemoryObservationWP.scalarFromImage Scalar.toUInt8 Scalar.fromScalarInt ScalarInt.ofUInt8
private theorem scalarFromImage_one (layout : TargetDataLayout) (start : UInt64)
    (byte : UInt8) (provenance : ProvenanceMap Provenance) :
    MemoryObservationWP.scalarFromImage layout ⟨⟨start⟩, ⟨1⟩⟩ false
      (.ok #[byte]) (.ok (.ok ())) provenance = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 byte)) :=
  CopyInitialWP.scalarFromImage_byte layout ⟨start⟩ byte provenance
attribute [local cbv_eval] MemoryObservationWP.readScalar_eq_image scalarFromImage_one CopyInitialWP.toUInt8_byte
attribute [local cbv_opaque] RvalueWP.evalPre ValidityVisitor.validatePlace ValidityVisitor.visit
attribute [local cbv_eval] ValidityVisitor.validatePlace_shallow
attribute [local cbv_opaque] TypedRetag.machineRetagPtrValue
/-- The first three emitted shared-read rows create a fresh reference and
read the initial byte through tag 3, with no accepted error outcome. -/
theorem generatedSharedRead (initial : UInt8) :
    match scenario 2 initial false with
    | .error _ => False
    | .ok (config, before) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun after => observed .sharedRead initial after (.ok ()) = true)
        (fun error after => observed .sharedRead initial after (.error error) = true)
        ((GeneratedBodySafety.window_2_bb0_0 config limits).take 3) before := by
  conv => cbv
  constructor
  · rfl
  · intro choice _
    cases choice
    conv => cbv
    constructor
    · rfl
    · intro choice _
      cases choice
      conv => cbv
      miri_check_fixture_reference false
      conv => cbv
      constructor
      · rfl
      · intro choice _
        cases choice
        conv => cbv
        conv =>
          pattern ValidityVisitor.visit _ _ _ _ _ _
          tactic =>
            refine ValidityVisitor.visit_integer _ _ 31 _ _ _ ?value ?layout
              ?classified ?read ?clear ?ranges
            case classified => cbv <;> rfl
            case read => cbv <;> rfl
            case clear => cbv <;> rfl
            case ranges => rfl
        conv => cbv
        trivial

open Lean Elab Command in
run_cmd liftTermElabM do
  for dependency in (← collectAxioms ``generatedSharedRead) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "generatedSharedRead depends on unapproved axiom {dependency}"

#print axioms generatedSharedRead
end PointerObservation

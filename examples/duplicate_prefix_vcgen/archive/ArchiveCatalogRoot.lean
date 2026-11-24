import Miri.Verification.BodyVCGen
import duplicate_prefix.RootBody

namespace Miri.Verification.BodyVCGen

theorem loadProgram_root (input : Miri.Input.ExecutionInput) (root : Nat) :
    (loadProgram input root).map (·.root) = loadRoot input root := by
  unfold loadProgram loadRoot
  cases lowered : Miri.Input.lowerProgram input.document with
  | error failure => rfl
  | ok program =>
    simp only [bind, Except.bind]
    cases prepared : Miri.Input.CallResolution.prepare program with
    | error failure => rfl
    | ok ready =>
      simp only [prepared, bind]
      split <;> rfl

end Miri.Verification.BodyVCGen

namespace DuplicatePrefix.RootBody

open Miri.Verification

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option cbv.maxSteps 5000000

/-- The compiler-selected archived root has the exact body and identity used
by the current saved VC. The generic loader lemma avoids evaluating its graph. -/
theorem generated_catalog_root :
    (BodyVCGen.loadProgram Program.imported 0).map (·.root) = .ok reflected.body := by
  rw [BodyVCGen.loadProgram_root]
  cbv

#print axioms generated_catalog_root
end DuplicatePrefix.RootBody

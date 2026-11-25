import Pointer
import GeneratedPointerRows

namespace PointerObservation

open Miri.Interpreter Miri.Verification Fixture

private def emittedRows (config : Config) (observation : Observation) :
    List (GeneratedBodyVC.WindowRow config limits) :=
  let window := match observation with
    | .sharedRead => GeneratedBodySafety.window_2_bb0_0 config limits
    | .mutableWrite => GeneratedBodySafety.window_0_bb0_0 config limits
    | .rawWrite | .frozenWrite => GeneratedBodySafety.window_1_bb0_0 config limits
  window.take (selectedRows observation).2.2.length

/-- The emitted windows preserve the byte, tag and failure observations
checked on the imported pointer statements. -/
theorem generatedPrefix_iff_checked (observation : Observation) (initial : UInt8) :
    (let (root, restricted, _) := selectedRows observation
     match scenario root initial restricted with
     | .error _ => False
     | .ok (config, before) =>
       GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
         (fun after => observed observation initial after (.ok ()) = true)
         (fun error after => observed observation initial after (.error error) = true)
         (emittedRows config observation) before) ↔ checked observation initial = true := by
  rw [← required_iff_checked]
  have sameRows (config : Config) :
      (emittedRows config observation).map (fun row => (row.location.pc, row.reduced.node)) =
        ((selectedRows observation).2.2.zipIdx 0).map (fun (node, index) => (⟨0, index⟩, node)) := by
    cases observation <;> rfl
  rcases shape : selectedRows observation with ⟨root, restricted, rows⟩
  cases prepared : scenario root initial restricted with
  | error error => simp only [required, shape, prepared]
  | ok entered =>
    obtain ⟨config, before⟩ := entered
    simp only [required, shape, prepared]
    exact (prefixPre_iff_windowPrefixPre config _ _ 0 rows (emittedRows config observation) before
      (by simpa only [shape] using sameRows config)).symm

#print axioms generatedPrefix_iff_checked

end PointerObservation

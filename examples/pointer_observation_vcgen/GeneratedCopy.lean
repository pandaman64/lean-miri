import Copy
import GeneratedCopyRows

namespace PointerObservation.Copy

open Miri.Interpreter Miri.Verification Fixture

/-- The emitted window checks the same executable copy observation, with a
finite endpoint after the load and the actual failed state on invalidation. -/
theorem generatedPrefix_iff_checked (source destination : UInt8) (stale : Bool) :
    (match scenario source destination stale with
    | .error _ => False
    | .ok (config, entry) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun after => stale = false ∧ scalarAt after 0 = some source)
        (fun error after => stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source]))
        ((GeneratedBodySafety.window_0_bb0_5 config limits).take 6) entry) ↔
      checked source destination stale = true := by
  rw [← required_iff_checked]
  cases each : scenario source destination stale with
  | error error => simp only [required, each]
  | ok entered =>
    obtain ⟨config, entry⟩ := entered
    simp only [required, each]
    exact (prefixPre_iff_windowPrefixPre config _ _ 5 rows
      ((GeneratedBodySafety.window_0_bb0_5 config limits).take 6) entry (by rfl)).symm

#print axioms generatedPrefix_iff_checked

end PointerObservation.Copy

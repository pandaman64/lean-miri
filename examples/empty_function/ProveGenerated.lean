import Generated
import empty_function.GeneratedBodySafety

/-! Proof client for a VC file emitted by `tools/body-vc safety`. -/
namespace EmptyFunction.GeneratedProof

open Miri.Frontend Miri.Memory Miri.Interpreter Miri.Verification
open EmptyFunction.WholeCall EmptyFunction.Specification

set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

private theorem loadedSome : _root_.GeneratedBodySafety.loaded.toOption.isSome = true := by cbv

def freshProgram : BodyVCGen.LoadedProgram :=
  checkedSome _root_.GeneratedBodySafety.loaded.toOption loadedSome

private theorem loaded_eq (actual : Except String BodyVCGen.LoadedProgram)
    (loaded : actual.toOption.isSome = true) :
    actual = .ok (checkedSome actual.toOption loaded) := by
  cases actual with
  | error _ =>
    change false = true at loaded
    cases loaded
  | ok _ => rfl

private theorem freshLoaded : _root_.GeneratedBodySafety.loaded = .ok freshProgram :=
  loaded_eq _ loadedSome

/-- The fresh exporter output and the original safety proof select the same
MIR root, including its instructions and canonical body identifier. -/
theorem sameExportedRoot : freshProgram.root = EmptyFunction.Program.root.loaded := by
  cbv

/-- Every admitted immediate local destination satisfies the saved safety VC
once the caller's canonical loader selects the same root. -/
theorem savedVC (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (value : Immediate Provenance) (immediate : destination.oldOperand = .immediate value)
    (entry : State) (installed : install s p = .ok () entry)
    (generated : BodyVCGen.LoadedProgram) (loaded : _root_.GeneratedBodySafety.loaded = .ok generated)
    (sameRoot : generated.root = s.loaded) :
    _root_.GeneratedBodySafety.requiredForEveryChoiceAt s.cfg s.limits entry := by
  have safe := EmptyFunction.GeneratedBodySafety.localImmediate s metadata profile p runtime input
    destination value immediate
  unfold EmptyFunction.GeneratedBodySafety.noUBVC at safe
  rw [installed] at safe
  change (BodyVCGen.generateProgram s.cfg s.limits (EmptyFunction.GeneratedBodySafety.program s)
    (fun _ _ => True) (fun _ _ => True) BodyVCGen.noUB).pre entry at safe
  rw [BodyVCGen.generatedProgramPre_eq, WholeBodyWP.catalogBodyPre_iff] at safe
  simp only [_root_.GeneratedBodySafety.requiredForEveryChoiceAt,
    _root_.GeneratedBodySafety.requiredAt, loaded]
  rw [BodyVCGen.generatedProgramPre_eq, WholeBodyWP.catalogBodyPre_iff, sameRoot]
  exact safe

/-- The concrete saved VC for `empty_function` under the admitted local
immediate domain, at its binding in the canonical root catalog. -/
theorem emptyFunctionSafe (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (value : Immediate Provenance) (immediate : destination.oldOperand = .immediate value)
    (entry : State) (installed : install s p = .ok () entry)
    (canonical : s.loaded.identity = EmptyFunction.Program.root.loaded.identity) :
    _root_.GeneratedBodySafety.requiredForEveryChoiceAt s.cfg s.limits entry := by
  apply savedVC s metadata profile p runtime input destination value immediate entry installed
    freshProgram freshLoaded
  rw [sameExportedRoot]
  have mir := metadata.body.symm
  have identity := canonical.symm
  cases source : EmptyFunction.Program.root.loaded with
  | mk sourceId sourceBody =>
    cases actual : s.loaded with
    | mk actualId actualBody =>
      simp only [source, actual] at mir identity
      cases mir
      cases identity
      rfl

#print axioms sameExportedRoot
#print axioms savedVC
#print axioms emptyFunctionSafe
end EmptyFunction.GeneratedProof

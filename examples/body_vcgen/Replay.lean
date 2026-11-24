import Miri.Frontend.ImportMIR
import MiriTests.Verification.WholeBodyReplay

/-! Replay certificates for the actual imported program. The machine state
and configuration are supplied by the production runner or a proof client. -/
namespace BodyVCGenReplayExample

open Miri.ABI Miri.Frontend Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification
open Miri.Verification.WholeBodyWP MiriTests.Verification.WholeBodyReplay

set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

import_mir "examples/body_vcgen/input.json" as input

private def loaded := (BodyVCGen.loadProgram input 0).toOption
private theorem loadedSome : loaded.isSome = true := by cbv

def program : BodyVCGen.LoadedProgram := checkedSome loaded loadedSome

/-- The immediate arguments to `count_up(1, 3, true)`, using the compiler's
actual layouts for `u8` and `bool`. -/
def arguments (byte boolean : LocalLayout) :
    Except ScalarError (Array (RvalueImmTy Provenance)) := do
  let first ← Scalar.fromUInt (BitVec.ofNat 128 1) byte.layout.size
  let limit ← Scalar.fromUInt (BitVec.ofNat 128 3) byte.layout.size
  pure #[⟨.scalar first, byte⟩, ⟨.scalar limit, byte⟩, ⟨.scalar (Scalar.fromBool true), boolean⟩]

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

/-- After actual root preparation, a checked normal replay proves the matching
post and refutes the same generated VC with an impossible success post. -/
theorem successAndFalsePost
    (config : Config) (limits : ExecutionMachine.Limits)
    (launch : C) (byte boolean : LocalLayout) (args : Array (RvalueImmTy Provenance))
    (dest : MPlaceTy Provenance) (span : SpanRef) (choose : State → C)
    (initial entry returned : State) (budget : Nat)
    (launched : (do
      let actual ← (match arguments byte boolean with
        | .ok values => pure values
        | .error error => throw (StepError.invalidProgram (reprStr error)) : MachineHooks.M K U _)
      BodyVCGen.prepareRoot config limits program launch actual (some dest) span) initial = .ok () entry)
    (argsOk : arguments byte boolean = .ok args)
    (entered : entryMatchesLoaded program.root entry)
    (checked : replay (ExecutionMachine.step config limits) choose (fun s => s.stack.frames.size)
      entry.stack.frames.size budget entry = some (returned, .ok .scopeExit)) :
    BodyVCGen.preparedProgramPre config limits program launch args (some dest) span
      (selected choose) (fun exit after => exit = .scopeExit ∧ after = returned) (fun _ _ => False) initial ∧
    ¬ BodyVCGen.preparedProgramPre config limits program launch args (some dest) span
      (selected choose) (fun _ _ => False) (fun _ _ => False) initial := by
  have prepared : BodyVCGen.prepareRoot config limits program launch args (some dest) span initial = .ok () entry := by
    simpa [argsOk, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure] using launched
  refine ⟨?_, ?_⟩
  · exact (preparedProgramPre_iff_replay _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      prepared entered checked).mpr ⟨rfl, rfl⟩
  · intro valid
    exact (preparedProgramPre_iff_replay _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      prepared entered checked).mp valid

/-- An actual UB certificate for an imported root refutes the generated VC
that rejects UB, independently of its success post. -/
theorem rejectsUndefinedBehavior
    (config : Config) (limits : ExecutionMachine.Limits)
    (opened : BodyVCGen.LoadedProgram) (choose : State → C) (allowed : State → C → Prop)
    (entry failed : State) (budget : Nat) (error : StepError)
    (post : Exit → State → Prop)
    (checked : replay (ExecutionMachine.step config limits) choose (fun s => s.stack.frames.size)
      entry.stack.frames.size budget entry = some (failed, .error error))
    (admitted : ∀ state, allowed state (choose state))
    (undefinedBehavior : RunLoop.reportsUB error = true) :
    ¬ (BodyVCGen.generateProgram config limits opened allowed post
      (fun error _ => RunLoop.reportsUB error = false)).pre entry := by
  intro accepted
  rw [BodyVCGen.generatedProgramPre_eq, catalogBodyPre_iff] at accepted
  have witness := replay_sound_for _ _ _ _ _ _ _ _ _ admitted checked
  have classified := accepted.2 _ _ witness
  change RunLoop.reportsUB error = false at classified
  simp only [undefinedBehavior, Bool.true_eq_false] at classified

#print axioms successAndFalsePost
#print axioms rejectsUndefinedBehavior

end BodyVCGenReplayExample

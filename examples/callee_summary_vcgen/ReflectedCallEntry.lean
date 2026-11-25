import Generated
import CallCompilerData
import CallEntry
import empty_function.Configuration
import pointer_observation_vcgen.Fixture

/-! The call-site fixture using the prepared compiler data constants. -/

namespace CalleeSummaryReflected

open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.TreeBorrows Miri.Verification
open PointerObservation.Fixture

abbrev callBorrow := CalleeSummaryExample.callBorrow
abbrev calleeBorrow := CalleeSummaryExample.calleeBorrow
abbrev argumentHasStrongProtector := CalleeSummaryExample.argumentHasStrongProtector

noncomputable def atBorrowedCall : Except String (Config × ULift.{1} BodyVCGen.LoadedProgram × State) := do
  let compiler := reflectedRuntimeCompiler
  let image := AllocationImage.Imported.withSourceIndex #[] #[]
  let types ← compiler.initialArrays.map ULift.up
  let layouts ← (EvalEntryMachine.layouts compiler).map ULift.up
  let span ← (CompilerContextSpan.rootSpan compiler.program).map ULift.up
  let program := reflectedRuntimeProgram
  let compiled : EvalPreparation.Prepared := ⟨compiler, image, types.down, layouts.down, span.down⟩
  let options := {EmptyFunction.Configuration.exampleOptions limits 32 32 32 32 .Shallow ⟨false, false⟩ with
    panicUnwinds := false, userRelevantCrates := #[0]}
  let config ← (EmptyFunction.Configuration.rootConfig compiled reflectedRuntimeBytes options () 32).mapError reprStr
  CalleeSummaryExample.assembleBorrowedCall config compiled program

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option cbv.maxSteps 100000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert

theorem borrowedCallReady : atBorrowedCall.isOk = true := by
  cbv

theorem borrowedCallSelected :
    atBorrowedCall.toOption.bind (fun (_, _, before) => BodyCFG.selected before) =
      some (⟨0, 7⟩, GeneratedBodySafety.mir_0_bb0_7) := by
  cbv

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``borrowedCallReady, ``borrowedCallSelected] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms borrowedCallReady
#print axioms borrowedCallSelected

end CalleeSummaryReflected

import ReflectedCallEntry

namespace CalleeSummaryReflected
open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.Verification
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option cbv.maxSteps 180000
attribute [local cbv_opaque] SourceAbi.compute Std.HashMap.emptyWithCapacity Std.HashMap.insert
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty

theorem callAbiLiteralQuery :
    CompilerInstanceAbi.abiOfInstance reflectedRuntimeCompiler.lifecycle.instances 1 #[] =
      .ok reflectedRuntimeAbi := by
  conv => lhs; cbv
  simp only [SourceAbi.compute, Std.Legacy.Range.forIn'_eq_forIn'_range',
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  conv => lhs; cbv
  rfl

theorem callAbiLiteralResolution :
    CallResolution.abiOfInstance reflectedRuntimeCompiler.lifecycle.calls.calls 1 #[] =
      .ok reflectedRuntimeAbi := callAbiLiteralQuery

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``callAbiLiteralQuery, ``callAbiLiteralResolution] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms callAbiLiteralQuery
#print axioms callAbiLiteralResolution
end CalleeSummaryReflected

import GeneratedPointerRows

open Lean Elab Command Meta
open Miri.Verification

run_cmd liftTermElabM do
  for row in [``GeneratedBodySafety.transfer_0_bb0_2,
      ``GeneratedBodySafety.transfer_1_bb0_1, ``GeneratedBodySafety.transfer_2_bb0_1] do
    let declaration ← getConstInfo row
    forallTelescope declaration.type fun arguments _ => do
      let transfer := mkAppN (mkConst row (declaration.levelParams.map Level.param)) arguments
      let pre ← whnf (← mkAppM ``GeneratedBodyVC.ReducedNode.pre #[transfer])
      unless (pre.find? (·.isConstOf ``PointerFormationWP.pointerRetagPre)).isSome do
        throwError "{row}.pre did not expose the typed pointer retag"
      if (pre.find? (·.isConstOf ``RvalueWP.evalPre)).isSome then
        throwError "{row}.pre still contains the generic rvalue rule"

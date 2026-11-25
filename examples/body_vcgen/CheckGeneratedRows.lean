import Generated

/-! Check the transfer predicates emitted by the default generator for the
saved `examples/body_vcgen/input.json` and its `count_up` root. -/

open Lean Elab Command Meta
open Miri.Interpreter Miri.Verification

run_cmd liftTermElabM do
  let rows := [
    (``GeneratedBodySafety.transfer_0_bb0_2, [``PlaceReadWriteWP.copyPre]),
    (``GeneratedBodySafety.transfer_0_bb1_5,
      [``MemoryWP.immediateReadPre, ``PlaceReadWriteWP.writePre])]
  let unresolved := [``RvalueWP.evalPre, ``OperandMachine.evalOperand,
    ``PlaceDynamic.evalPlace, ``PlaceMachine.readImmediate, ``writePlaceImmediate, ``copyRuntimePlace]
  for (row, expected) in rows do
    let declaration ← getConstInfo row
    forallTelescope declaration.type fun arguments _ => do
      let transfer := mkAppN (mkConst row (declaration.levelParams.map Level.param)) arguments
      -- Reduce the projection and any alias that shares an identical row.
      let pre ← whnf (← mkAppM ``GeneratedBodyVC.ReducedNode.pre #[transfer])
      for name in expected do
        unless (pre.find? (·.isConstOf name)).isSome do
          throwError "{row}.pre is missing {name}"
      for name in unresolved do
        if (pre.find? (·.isConstOf name)).isSome then
          throwError "{row}.pre still contains {name}"

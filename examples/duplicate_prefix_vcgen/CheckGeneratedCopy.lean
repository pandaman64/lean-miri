import Representative

/-! Check the actual copy transfer even when the imported standard library
puts the intrinsic at a different MIR location. -/
open Lean Elab Command Meta Miri.MIR Miri.Verification in
run_cmd liftTermElabM do
  let env ← getEnv
  let mut checked := 0
  for (name, declaration) in env.constants.toList do
    let .str `GeneratedBodySafety namePart := name | continue
    unless namePart.startsWith "mir_" do continue
    let .defnInfo imported := declaration | continue
    unless (imported.value.find? (·.isConstOf ``NonDivergingIntrinsic.CopyNonOverlapping)).isSome do
      continue
    let row := `GeneratedBodySafety ++ Name.mkSimple s!"transfer_{(namePart.drop 4).toString}"
    let transfer ← getConstInfo row
    forallTelescope transfer.type fun arguments _ => do
      let applied := mkAppN (mkConst row (transfer.levelParams.map Level.param)) arguments
      let pre ← whnf (← mkAppM ``GeneratedBodyVC.ReducedNode.pre #[applied])
      unless (pre.find? (·.isConstOf ``CopyTreeWP.copyPre)).isSome do
        throwError "generated copy transfer {row} is missing its tree-aware copy predicate"
      if (pre.find? fun expression => expression.isConstOf ``Miri.Interpreter.OperandMachine.evalOperand ||
          expression.isConstOf ``Miri.Interpreter.Intrinsics.evalNondivergingWith).isSome then
        throwError "generated copy transfer {row} still evaluates a raw MIR operand or intrinsic"
    checked := checked + 1
    logInfo m!"Checked generated copy transfer {row}"
    if row == `GeneratedBodySafety.transfer_5_bb7_8 then
      let legacy : BodyCFG.Node := .statement (.Intrinsic (.CopyNonOverlapping
        ⟨.Move ⟨14, #[]⟩, .Move ⟨15, #[]⟩, .Move ⟨16, #[]⟩⟩))
      if ← isDefEq imported.value (toExpr legacy) then
        logInfo "The fixed copy-site proof matches the imported MIR."
  if checked == 0 then throwError "imported duplicate_prefix has no generated CopyNonOverlapping transfer"

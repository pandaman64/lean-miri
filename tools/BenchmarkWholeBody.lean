import Miri.Verification.BodyVCGen
import Miri.Frontend.ImportMIR
import Lean

/-! Build and typecheck the named equation VCs for a synthetic MIR diamond chain.
The harness does not solve invariants or run the interpreter. -/
namespace Miri.BenchmarkWholeBody

open Lean Meta Elab Command Term
open Miri.MIR Miri.Interpreter Miri.Verification Std.WP

private def source : Miri.MIR.SourceInfo := ⟨⟨0⟩, 0⟩
private def discriminant : Miri.MIR.Operand := .Copy ⟨1, #[]⟩

private def block (kind : TerminatorKind) : BasicBlock :=
  ⟨#[⟨source, .Nop⟩], ⟨source, kind⟩, false⟩

private def diamonds (count : Nat) : Body :=
  let arms := (Array.range count).foldl (fun blocks index =>
    let head := 3 * index
    let split := block (.SwitchInt discriminant ⟨#[.Case 0 (head + 1)], head + 2⟩)
    let arm := block (.Goto (head + 3) #[])
    ((blocks.push split).push arm).push arm) #[]
  ⟨.Runtime .Optimized, 1, none, #[0, 0], arms.push (block .Return)⟩

@[noinline] private def phase (label : String) (action : Unit → TermElabM α) : TermElabM α := do
  let start ← IO.monoNanosNow
  let result ← action ()
  let elapsed ← IO.monoNanosNow
  IO.println s!"{label}_ns={elapsed - start}"
  return result

private def verifyGraph (diamonds : Nat) (cfg : BodyCFG.Compiled)
    (equations : Array BodyCFG.Equation) : TermElabM Unit := do
  let blocks := 3 * diamonds + 1
  unless cfg.blocks.size == blocks && equations.size == 2 * blocks do
    throwError "unexpected block or equation count"
  let mut incoming := Array.replicate equations.size (0 : Nat)
  let mut edges := 0
  for index in [:equations.size] do
    let some equation := equations[index]? | throwError "missing equation"
    let expectedPC : Location := ⟨index / 2, index % 2⟩
    unless equation.pc == expectedPC do throwError "duplicate or out-of-order PC"
    for target in equation.targets do
      let slot := target.block * 2 + target.statementIndex
      unless (equations[slot]?).map BodyCFG.Equation.pc == some target do
        throwError "unresolved equation edge"
      incoming := incoming.modify slot (· + 1)
      edges := edges + 1
  let joins := incoming.countP (· == 2)
  unless edges == 7 * diamonds + 1 && joins == diamonds &&
      (incoming[0]? == some 0) && (incoming.extract 1 incoming.size).all (fun degree => degree == 1 || degree == 2) do
    throwError "incorrect shared diamond topology"
  IO.println s!"blocks={blocks} equations={equations.size} edges={edges} joins={joins}"

private partial def expressionNodes : Expr → Nat
  | .app fn arg => 1 + expressionNodes fn + expressionNodes arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
    1 + expressionNodes domain + expressionNodes body
  | .letE _ type val body _ => 1 + expressionNodes type + expressionNodes val + expressionNodes body
  | .mdata _ child | .proj _ _ child => 1 + expressionNodes child
  | _ => 1

/-- Reflect the already compiled equations once. Record this cost separately
from instantiating the actual public verification condition. -/
private def reflectEquations (equations : Array BodyCFG.Equation) : TermElabM (Array Expr) := do
  let env ← getEnv
  equations.mapM fun equation => do
    let syntaxTree ← ofExcept (Parser.runParserCategory env `term (reprStr equation))
    let value ← elabTerm syntaxTree (some (mkConst ``BodyCFG.Equation))
    instantiateMVars value

/-- Apply the mapper from the actual public proposition array. Reducing
the whole array in the kernel would repeatedly replay graph computations.
The harness carries no copy of the one-instruction WP. -/
private def materialize (array : Expr) (equations : Array Expr) :
    TermElabM (Array Expr) := do
  let mapped ← withTransparency .all <|
    withCanUnfoldPred (fun _ decl => pure (decl.name != ``Array.map)) (whnf array)
  unless mapped.isAppOfArity ``Array.map 4 do
    throwError "expected generated equation map, found {mapped.getAppFn}"
  let mapper := mapped.getAppArgs[2]!
  equations.mapM fun equation => withTransparency .all (whnf (mkApp mapper equation))

private def checkEntry (triple : Expr) (locals : Array Expr) : TermElabM Unit := do
  let goal ← mkFreshExprSyntheticOpaqueMVar triple
  let tactic ← `(tactic| vcgen)
  let goals ← phase "vcgen" fun _ => Tactic.run goal.mvarId! (Tactic.evalTactic tactic)
  let [entryGoal] := goals | throwError "expected exactly one generated entry goal"
  phase "entry" fun _ => entryGoal.withContext do
    let target ← withTransparency .all (whnf (← entryGoal.getType))
    unless target.isAppOf ``And do throwError "missing compiled entry guard"
    for parameter in [locals[3]!, locals[4]!] do
      unless (target.find? (· == parameter)).isSome do
        throwError "the generated entry VC lost a postcondition"
    unless (target.find? (· == locals[6]!)).isNone do
      throwError "the entry VC has an invariant parameter"
    unless (← inferType target).isProp do throwError "the entry VC is not a proposition"

private def checkVCs (vcs locals : Array Expr) : TermElabM Unit := do
  phase "typecheck" fun _ => do
    for vc in vcs do
      unless (← inferType vc).isProp do throwError "the generated equation VC is not a proposition"
      for parameter in [locals[3]!, locals[4]!] do
        unless (vc.find? (· == parameter)).isSome do
          throwError "the generated equation VC lost a postcondition"
  let sizes := vcs.map expressionNodes
  IO.println s!"vcs={vcs.size} expression_nodes={sizes.sum} max_expression_nodes={sizes.max?.getD 0}"

private def measureDiamonds (count : TSyntax `num) : TermElabM Unit := do
  let body ← phase "source" fun _ => do pure (diamonds count.getNat)
  let graph ← phase "compile" fun _ => do pure (BodyCFG.compile body)
  let equations ← phase "equations" fun _ => do pure graph.equations
  verifyGraph count.getNat graph equations
  let template ← elabTerm
    (← `(fun
      (config : ExecutionMachine.Config Unit Unit Unit Unit Unit Unit) (limits : ExecutionMachine.Limits)
      (allowed : MachineHooks.State Unit Unit → Unit → Prop)
      (post : WholeBodyWP.Exit → MachineHooks.State Unit Unit → Prop)
      (failure : StepError → MachineHooks.State Unit Unit → Prop)
      (before : MachineHooks.State Unit Unit)
      (atPC : Location → MachineHooks.State Unit Unit → Prop)
      (fallback : MachineHooks.State Unit Unit → Prop) =>
      let body := diamonds $count
      let generated := BodyVCGen.generate config limits body allowed post failure
      (Std.WP.Triple (BodyVCGen.run config limits body allowed) (· = before) post failure,
        generated.equations atPC fallback))) none
  synthesizeSyntheticMVarsNoPostponing
  lambdaTelescope (← instantiateMVars template) fun locals result => do
    let args := (← whnf result).getAppArgs
    unless args.size == 4 do throwError "missing generated whole-body condition"
    checkEntry args[2]! locals
    let payloads ← phase "reflect" fun _ => reflectEquations equations
    let vcs ← phase "generate" fun _ => materialize args[3]! payloads
    checkVCs vcs locals

elab "#benchmark_whole_body " count:num : command => liftTermElabM do
  measureDiamonds count

private def tableCounts (equations : Array BodyCFG.Equation) : Nat × Nat :=
  let (edges, incoming) := equations.foldl (fun (edges, counts) equation =>
    (edges + equation.targets.size, equation.targets.foldl (fun counts pc =>
        counts.insert (pc.block, pc.statementIndex) ((counts.getD (pc.block, pc.statementIndex) 0 : Nat) + 1))
        counts)) ((0, ∅) : Nat × Std.HashMap (Nat × Nat) Nat)
  (edges, incoming.toArray.countP (fun entry => entry.2 > 1))

private def identityTerm (identity : BodyIdentity) : TermElabM Expr :=
  mkAppM ``BodyIdentity.ofCanonicalIndex #[mkNatLit identity.index]

/-- Open the production option mapper at a body which is present in the
evaluated catalogue. Keep the catalogue lookup itself in the expression. -/
private def programTable (optional : Expr) (defaultCfg : Expr) : TermElabM Expr := do
  let option ← withTransparency .all <|
    withCanUnfoldPred (fun _ decl => pure (decl.name != ``Option.map)) (whnf optional)
  unless option.isAppOfArity ``Option.map 4 do
    throwError "expected generated catalogue lookup, found {option.getAppFn}"
  let args := option.getAppArgs
  let cfg ← mkAppM ``Option.getD #[args[3]!, defaultCfg]
  return mkApp args[2]! cfg

private unsafe def measureImported (input : TSyntax `ident) (root : TSyntax `num) : TermElabM Unit := do
  let program ← phase "source" fun _ => do
    let expression ← elabTerm (← `(BodyVCGen.loadProgram $input $root)) none
    synthesizeSyntheticMVarsNoPostponing
    let expected ← elabTerm (← `(Except String BodyVCGen.LoadedProgram)) none
    let result ← evalExpr (Except String BodyVCGen.LoadedProgram) expected (← instantiateMVars expression)
    match result with
    | .ok program => pure program
    | .error message => throwError "cannot load benchmark root: {message}"
  let graph ← phase "compile" fun _ => do pure (BodyCFG.compileProgram program.bodies)
  unless graph.graphs.size == program.bodies.size && (graph.lookup program.root.identity).isSome do
    throwError "duplicate or missing body identity in the benchmark catalogue"
  let tables ← phase "equations" fun _ => program.bodies.mapM fun source => do
    let some cfg := graph.lookup source.identity | throwError "generated catalogue lost a body"
    return (source.identity, cfg.equations)
  let blocks := (program.bodies.map (·.body.basicBlocks.size)).sum
  let largestCallee := program.bodies.foldl (fun size source =>
    if source.identity == program.root.identity then size else max size source.body.basicBlocks.size) 0
  let equationCount := (tables.map (·.2.size)).sum
  let counts := tables.map fun table => tableCounts table.2
  IO.println s!"bodies={tables.size} root_blocks={program.root.body.basicBlocks.size} largest_callee_blocks={largestCallee}"
  IO.println s!"blocks={blocks} equations={equationCount} edges={(counts.map Prod.fst).sum} joins={(counts.map Prod.snd).sum}"
  let template ← elabTerm
    (← `(fun
      (config : ExecutionMachine.Config Unit Unit Unit Unit Unit Unit) (limits : ExecutionMachine.Limits)
      (allowed : MachineHooks.State Unit Unit → Unit → Prop)
      (post : WholeBodyWP.Exit → MachineHooks.State Unit Unit → Prop)
      (failure : StepError → MachineHooks.State Unit Unit → Prop)
      (before : MachineHooks.State Unit Unit)
      (atPC : BodyCFG.ProgramLocation → MachineHooks.State Unit Unit → Prop)
      (fallback : MachineHooks.State Unit Unit → Prop) =>
      let program := (BodyVCGen.loadProgram $input $root).toOption.getD
        (⟨0, ⟨BodyIdentity.ofCanonicalIndex 0, diamonds 0⟩, #[]⟩ : BodyVCGen.LoadedProgram)
      let generated := BodyVCGen.generateProgram config limits program allowed post failure
      (Std.WP.Triple (BodyVCGen.runProgram config limits program allowed) (· = before) post failure,
        generated.equations atPC fallback))) none
  synthesizeSyntheticMVarsNoPostponing
  lambdaTelescope (← instantiateMVars template) fun locals result => do
    let args := (← whnf result).getAppArgs
    unless args.size == 4 do throwError "missing generated whole-program condition"
    checkEntry args[2]! locals
    let defaultCfg ← elabTerm (← `(BodyCFG.compile (diamonds 0))) none
    let payloads ← phase "reflect" fun _ => tables.mapM fun (identity, equations) => do
      return (← identityTerm identity, ← reflectEquations equations)
    let vcs ← phase "generate" fun _ => do
      let mut vcs := Array.emptyWithCapacity equationCount
      for (identity, equations) in payloads do
        let array ← programTable (mkApp args[3]! identity) defaultCfg
        vcs := vcs ++ (← materialize array equations)
      return vcs
    checkVCs vcs locals

syntax (name := benchmarkImportedBody) "#benchmark_imported_body " ident num : command

@[command_elab benchmarkImportedBody] unsafe def elabImported : CommandElab
  | `(#benchmark_imported_body $input:ident $root:num) => liftTermElabM (measureImported input root)
  | _ => throwUnsupportedSyntax

end Miri.BenchmarkWholeBody

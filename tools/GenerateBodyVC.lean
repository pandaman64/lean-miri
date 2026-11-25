import Miri.Frontend.ImportMIR
import Miri.Verification.BodyVCGen

open Lean Miri Miri.Input Miri.Interpreter Miri.MIR Miri.Verification

private def opcode (node : BodyCFG.Node) : String :=
  let raw := match node with
    | .statement kind => reprStr kind
    | .terminator term => reprStr term.kind
  let constructor := (raw.splitOn " ").head!
  ((constructor.splitOn ".").getLast!).trimAscii.toString

private def locJson (loc : Location) : Json :=
  toJson #[loc.block, loc.statementIndex]

private def selectedRoot (input : ExecutionInput) (requested : Option String) : Except String (Nat × String) := do
  let roots := input.document.bodyRoots
  let candidates := (roots.mapIdx fun index root => (index, root)).filter fun (_, root) =>
    !root.isStatic && requested.all (· == root.defPath)
  let #[found] := candidates |
    throw ("expected one executable root; available: " ++
      String.intercalate ", " (roots.toList.map (·.defPath)))
  pure (found.1, found.2.defPath)

def main (args : List String) : IO UInt32 := do
  let inputFile :: rest := args | throw (IO.userError "expected a MIR JSON path")
  let requested := rest.head?
  let decoded ← Input.decodeFile inputFile
  let (input, rootIndex, rootName) ← match decoded >>= fun input =>
      (selectedRoot input requested).map fun (index, name) => (input, index, name) with
    | .ok result => pure result
    | .error error => throw (IO.userError error)
  let start ← IO.monoNanosNow
  let loaded ← match BodyVCGen.loadProgram input rootIndex with
    | .ok loaded => pure loaded
    | .error error => throw (IO.userError error)
  let graph := BodyCFG.compileProgram loaded.bodies
  let mut representatives : Std.HashMap String (Array (BodyCFG.Node × BodyCFG.ProgramLocation)) := {}
  let mut functions := #[]
  for body in loaded.bodies do
    let mut equations := #[]
    if let some cfg := graph.lookup body.identity then
      for equation in cfg.equations do
        let here : BodyCFG.ProgramLocation := ⟨body.identity, equation.pc⟩
        let key := reprStr equation.node
        let candidates := representatives[key]?.getD #[]
        let representative ← match candidates.find? (fun (node, _) => node = equation.node) with
          | some (_, earlier) => pure earlier
          | none =>
            representatives := representatives.insert key (candidates.push (equation.node, here))
            pure here
        let statement := match equation.node with
          | .statement _ => true
          | .terminator _ => false
        let call := match equation.node with
          | .terminator { kind := .Call .., .. } => true
          | _ => false
        equations := equations.push (Json.mkObj [("pc", locJson equation.pc),
          ("operation", toJson (opcode equation.node)),
          ("targets", Json.arr (equation.targets.map locJson)), ("statement", toJson statement),
          ("call", toJson call),
          ("representative", toJson #[representative.body.index, representative.pc.block,
            representative.pc.statementIndex])])
    functions := functions.push (Json.mkObj [("identity", toJson body.identity.index),
      ("equations", Json.arr equations)])
  let output := Json.mkObj [("rootIndex", toJson rootIndex),
    ("root", toJson rootName),
    ("rootIdentity", toJson loaded.root.identity.index), ("bodies", Json.arr functions)]
  let rendered := output.compress
  let generated ← IO.monoNanosNow
  IO.eprintln s!"Loaded and compiled MIR equations in {generated - start} ns"
  IO.println rendered
  pure 0

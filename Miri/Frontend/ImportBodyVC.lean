import Miri.Frontend.ImportMIR
import Miri.Verification.GeneratedBodyVC

namespace Miri.Frontend

open Lean Elab Command Miri.Verification

deriving instance ToExpr for BodyCFG.Node

/-- Import the paired MIR and bind the instructions of its canonical bodies
as constructor values for instruction-local VC simplification. -/
elab "import_body_vc_mir " path:str root:num " as " name:ident : command => do
  let source := System.FilePath.mk (← read).fileName
  let file := source.parent.getD "." / path.getString
  let input ← match ← liftIO (Input.decodeFile file) with
    | .ok input => pure input
    | .error error => throwErrorAt path "MIR import failed: {error}"
  let program ← match BodyVCGen.loadProgram input root.getNat with
    | .ok program => pure program
    | .error error => throwErrorAt root "MIR VC root failed: {error}"
  let namespaceName ← getCurrNamespace
  addInputDecl (namespaceName ++ name.getId) input
  let graph := BodyCFG.compileProgram program.bodies
  liftCoreM <| withOptions (Elab.async.set · false) do
    for body in program.bodies do
      let some cfg := graph.lookup body.identity | continue
      for eq in cfg.equations do
        let suffix := s!"mir_{body.identity.index}_bb{eq.pc.block}_{eq.pc.statementIndex}"
        let declName := namespaceName ++ Name.mkSimple suffix
        addAndCompile <| .defnDecl {
          name := declName,
          levelParams := [],
          type := mkConst ``BodyCFG.Node,
          value := toExpr eq.node,
          hints := .regular 0,
          «safety» := .safe
        }
        enableRealizationsForConst declName

end Miri.Frontend

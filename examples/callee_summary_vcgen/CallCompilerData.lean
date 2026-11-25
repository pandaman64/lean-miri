import Miri.Frontend.ImportBodyVC
import Miri.Input.EvalPreparation
import Miri.Input.EvalConfigurationCore
import Miri.Input.CompilerGlobalBytes

/-! Reify compiler metadata from the generated caller's saved export. The
elaborator builds data constants for the checked normalization, using the same
preparation and ABI queries as the executable fixture. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 50000000
open Lean Elab Command Miri Miri.ABI Miri.Input Miri.Frontend

instance {α : Type u} {ε : Type v} [ToLevel.{u}] [ToLevel.{v}] [ToExpr α] [ToExpr ε] :
    ToExpr (Except ε α) where
  toTypeExpr := mkApp2 (mkConst ``Except [toLevel.{v}, toLevel.{u}]) (toTypeExpr ε) (toTypeExpr α)
  toExpr
    | .ok value => mkApp3 (mkConst ``Except.ok [toLevel.{v}, toLevel.{u}]) (toTypeExpr ε) (toTypeExpr α) (toExpr value)
    | .error error => mkApp3 (mkConst ``Except.error [toLevel.{v}, toLevel.{u}]) (toTypeExpr ε) (toTypeExpr α) (toExpr error)

deriving instance ToExpr for ByteArray

@[instance_reducible] private def quoteHashMap {α β : Type} [BEq α] [Hashable α] [ToExpr α] [ToExpr β]
    (beq hash : Expr) : ToExpr (Std.HashMap α β) where
  toTypeExpr := mkApp4 (mkConst ``Std.HashMap [0, 0]) (toTypeExpr α) (toTypeExpr β) beq hash
  toExpr map := mkApp5 (mkConst ``Std.HashMap.ofList [0, 0]) (toTypeExpr α) (toTypeExpr β) beq hash
    (toExpr map.toList)

@[instance_reducible] private def natMapBEq : BEq Nat := inferInstance
@[instance_reducible] private def u32MapBEq : BEq UInt32 := inferInstance

instance {β : Type} [ToExpr β] : ToExpr (Std.HashMap Nat β) :=
  quoteHashMap (mkConst ``natMapBEq) (mkConst ``instHashableNat)

instance {β : Type} [ToExpr β] : ToExpr (Std.HashMap UInt32 β) :=
  quoteHashMap (mkConst ``u32MapBEq) (mkConst ``instHashableUInt32)

open Lean Elab Command in
private partial def deriveQuote (name : Name) : StateT NameSet CommandElabM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let some info := (← getEnv).find? name | return
  if !name.toString.startsWith "Miri." then return
  match info with
  | .inductInfo indInfo =>
    let existing ← liftM <| liftTermElabM <| Meta.forallTelescopeReducing indInfo.type fun xs _ => do
      Meta.synthInstance? (← Meta.mkAppM ``ToExpr
        #[mkAppN (mkConst name (indInfo.levelParams.map Level.param)) xs])
    if existing.isSome then return
    for ctor in indInfo.ctors do
      for dependency in (← getConstInfo ctor).type.getUsedConstants do
        if dependency != name then deriveQuote dependency
    liftM <| elabCommand (← `(deriving instance ToExpr for $(mkIdent name)))
  | .defnInfo definition =>
    let typeFormer ← liftM <| liftTermElabM <|
      Meta.forallTelescopeReducing definition.type fun _ body => pure body.isSort
    if typeFormer then
      for dependency in definition.value.getUsedConstants do
        if dependency != name then deriveQuote dependency
  | _ => pure ()

open Lean Elab Command in
run_cmd do
  discard <| (deriveQuote ``CompilerProviders.Prepared).run {}
  discard <| (deriveQuote ``Miri.Verification.BodyVCGen.LoadedProgram).run {}

deriving instance ToExpr for ArgExtension
deriving instance ToExpr for ArgAttributes
deriving instance ToExpr for RegKind
deriving instance ToExpr for Reg
deriving instance ToExpr for Uniform
deriving instance ToExpr for CastTarget
deriving instance ToExpr for IndirectMode
deriving instance ToExpr for PassMode
deriving instance ToExpr for ArgAbi
deriving instance ToExpr for FnAbi

deriving instance ToExpr for CompilerGlobalBytes.Prepared

run_cmd do
  let file := (System.FilePath.mk (← read).fileName).parent.getD "." / "Generated.mir.json"
  let result ← liftIO (Miri.Input.decodeFile file)
  let decoded ← match result with
    | .ok input => pure input
    | .error error => throwError "{error}"
  let loaded ← match Miri.Verification.BodyVCGen.loadProgram decoded 0 with
    | .ok program => pure program
    | .error error => throwError "{error}"
  let lowered ← match Miri.Input.lowerProgram decoded.document with
    | .ok lowered => pure lowered
    | .error error => throwError "{error}"
  let attempt := EvalPreparation.prepare lowered
  let prepared ← match attempt.outcome with
    | .ok prepared => pure prepared
    | .error error => throwError "{error}"
  unless prepared.image.source.isEmpty && prepared.image.initializers.isEmpty do
    throwError "the reflected call fixture requires an empty compiler allocation image"
  let compiler := prepared.compiler
  let bytes ← match CompilerGlobalBytes.prepare compiler.program compiler.runtime attempt.memory with
    | .ok bytes => pure bytes
    | .error error => throwError "{error}"
  let abi ← match CompilerInstanceAbi.abiOfInstance compiler.lifecycle.instances 1 #[] with
    | .ok abi => pure abi
    | .error error => throwError "{error}"
  for (name, type, value) in [
      (`reflectedRuntimeCompiler, mkConst ``CompilerProviders.Prepared, toExpr compiler),
      (`reflectedRuntimeProgram, mkConst ``Miri.Verification.BodyVCGen.LoadedProgram, toExpr loaded),
      (`reflectedRuntimeBytes, mkConst ``CompilerGlobalBytes.Prepared, toExpr bytes),
      (`reflectedRuntimeAbi, mkApp (mkConst ``FnAbi) (mkConst ``MIR.TyId), toExpr abi)] do
    liftCoreM <| addDecl <| .defnDecl {
      name, levelParams := [], type, value, hints := .regular 0, «safety» := .safe }
    for dependency in (← liftCoreM <| collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

import duplicate_prefix.LanguageGuardCurrentFacts
import duplicate_prefix.RootCompilerFacts
import duplicate_prefix.CanonicalConfigFacts

namespace DuplicatePrefix.LanguageGuardCurrentABI
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open LanguageGuardCurrentFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def context : CompilerFacts.Context :=
  ⟨PreparedReflection.actual.runtime, PreparedReflection.actual.compiler.lifecycle.instances.program, none⟩

private def policy : SourceAbiPolicy :=
  ⟨"x86_64", false, false, true, false, 536870912, true, false, false, false, true⟩

private def definition (id : Nat) : SourceAbiDefinition :=
  ⟨id, ⟨#[], 0, .Safe, .Rust, false, none⟩, none, false, true, false, false, false, false⟩

private def checkedOk {E A : Type} : (result : Except E A) → result.isOk = true → A
  | .ok answer, _ => answer
  | .error _, impossible => False.elim (by cases impossible)

noncomputable def abi : FnAbi MIR.TyId :=
  checkedOk (PreparedReflection.actual.abiResults[9]'(by decide +kernel)) (by decide +kernel)

def query (callee : CallInstance) := CompilerInstanceAbi.abiOfInstance
  PreparedReflection.actual.compiler.lifecycle.instances callee #[]

theorem parent_dispatch : query parentCall.callee =
    SourceAbi.compute policy context.runtime.target (SourceAbiRuntime.queries context policy)
      (definition 9).signature #[] (some (definition 9)) true := by
  have instanceEq : parentCall.callee = 9 := rfl
  rw [instanceEq]
  unfold query CompilerInstanceAbi.abiOfInstance SourceAbiRuntime.ofInstance
  rfl

theorem leaf_dispatch : query leafCall.callee =
    SourceAbi.compute policy context.runtime.target (SourceAbiRuntime.queries context policy)
      (definition 21).signature #[] (some (definition 21)) true := by
  have instanceEq : leafCall.callee = 21 := rfl
  rw [instanceEq]
  unfold query CompilerInstanceAbi.abiOfInstance SourceAbiRuntime.ofInstance
  rfl

private theorem queriesBool :
    (SourceAbiRuntime.queries context policy).lookup 0 = .ok RootCompilerFacts.boolLayout := by
  change (PreparedReflection.actual.runtime.lookup 0).mapError toString = _
  rw [RootCompilerFacts.bool_layout_eq]
  rfl

private theorem boolBackend : RootCompilerFacts.boolLayout.layout.backendRepr =
    .Scalar (.Initialized (value := .Int .I8 false) (validRange := ⟨0,1⟩)) := rfl

private theorem compute (id : Nat) : SourceAbi.compute policy context.runtime.target
    (SourceAbiRuntime.queries context policy) (definition id).signature #[] (some (definition id)) true =
    .ok abi := by
  have nonzero : RootCompilerFacts.boolLayout.layout.isZst = false := rfl
  have rust : ((ExternAbi.Rust : ExternAbi) == .RustCall) = false := rfl
  have architecture : (policy.architecture == "x86_64") = true := rfl
  have panicAbort : policy.panicUnwinds = false := rfl
  simp [SourceAbi.compute, definition, architecture, rust, SourceAbi.canonicalConvention, SourceAbi.canUnwind,
    bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure, queriesBool, CanonAbi.isRusticAbi]
  simp [SourceAbi.argument, SourceAbi.scalarAttributes, boolBackend, nonzero, bind, Bind.bind,
    Except.bind, pure, Pure.pure, Except.pure, Scalar.isUninitValid, Align.ONE, WrappingRange.contains,
    ArgAttributes.new, panicAbort]
  try rfl

theorem parent_query : query parentCall.callee = .ok abi := by rw [parent_dispatch,compute]
theorem leaf_query : query leafCall.callee = .ok abi := by rw [leaf_dispatch,compute]

theorem flags : abi.args.size = 0 ∧ abi.cVariadic = false ∧ abi.canUnwind = false ∧
    abi.ret.layout = RootCompilerFacts.boolLayout := by decide +kernel

theorem canonical (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (callee : CallInstance)
    (fromSource : query callee = .ok abi) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).fnAbiOfInstance
      () callee #[] = (pure abi : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) := by
  funext state
  change (PreparedContracts.actualConfig options () remaining span).calls.compiler.fnAbiOfInstance () callee #[] state = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  dsimp only [CompilerCallConstruction.compiler, CompilerExecutionCallLeaves.make]
  unfold_internal ".CompilerExecutionCallLeaves.lift"
  unfold query at fromSource
  rw [fromSource]

end DuplicatePrefix.LanguageGuardCurrentABI

#print axioms DuplicatePrefix.LanguageGuardCurrentABI.parent_query
#print axioms DuplicatePrefix.LanguageGuardCurrentABI.leaf_query
#print axioms DuplicatePrefix.LanguageGuardCurrentABI.canonical

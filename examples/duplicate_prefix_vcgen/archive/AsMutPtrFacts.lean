import duplicate_prefix.WideValidityQueries
import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.PtrMetadataHelper
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.AsMutPtrFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ScalarValidityQueries WideValidityQueries
noncomputable section
private def checkedOk {E V : Type} : (value : Except E V) → value.isOk = true → V
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
private theorem checkedOk_eq {E V : Type} (value : Except E V) (supported : value.isOk = true) :
    value = .ok (checkedOk value supported) := by
  cases value with
  | ok value => rfl
  | error error => cases supported
def rawLayoutQuery := (PreparedReflection.actual.layoutResults[82]'(by decide +kernel))
theorem raw_layout_supported : rawLayoutQuery.isOk = true := by decide +kernel
def rawLayout := checkedOk rawLayoutQuery raw_layout_supported
private theorem raw_layout_exact :
    (PreparedReflection.actual.runtime.lookup 82).toOption = some rawLayout := by
  have observation : PreparedReflection.actual.runtime.node 82 =
      .ok PreparedReflection.actual.runtime.source.types[82] := by rfl
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : PreparedReflection.actual.runtime.source.types[82].sourceLayout.normalizedType = 82 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : PreparedReflection.actual.runtime.source.types[82]? =
      some PreparedReflection.actual.runtime.source.types[82] := by rfl
  have shape : PreparedReflection.actual.runtime.source.types[82].shape = .rawPointer 2 .Mut := by rfl
  have ordinary : PreparedReflection.actual.runtime.source.types[82].sourceLayout.specialFloat = none := by rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
    Except.toOption, get, MonadLift.monadLift, Except.map, Functor.map,
    Std.HashMap.getElem?_empty, hrow, normalized, shape, ordinary]
  try with_unfolding_all rfl

theorem raw_layout_eq : PreparedReflection.actual.runtime.lookup 82 = .ok rawLayout := by
  have h := raw_layout_exact
  generalize PreparedReflection.actual.runtime.lookup 82 = result at h ⊢
  cases result <;> simpa [Except.toOption] using h

theorem raw_type : rawLayout.ty = 82 := by with_unfolding_all rfl
theorem raw_sized : rawLayout.layout.isSized = true := by with_unfolding_all rfl
theorem raw_size : rawLayout.layout.size = Size.ofBytes 16 := by with_unfolding_all rfl
theorem raw_data : rawLayout.layout = PtrMetadataHelper.rawLayout.layout := by with_unfolding_all rfl
theorem raw_readable : ∃ pa pb ra rb offset, rawLayout.layout.backendRepr =
    .ScalarPair (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset) := by
  rw [raw_data]
  exact PtrMetadataHelper.raw_readable
theorem raw_no_padding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false rawLayout = .ok false := by decide +kernel
theorem raw_slice_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 82 = .ok (.rawPointer 2 false) := by
  unfold CompilerFactAdapters.validityKind
  unfold_raw_validity_helpers
  dsimp only
  have nodes (id : TypeId) : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node id =
      PreparedReflection.actual.runtime.node id :=
    RootMetadataQueries.context_node id
  simp only [nodes]
  change (do
    let sized ← CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 2 "is_sized"
    pure (ValidityVisitor.TypeKind.rawPointer 2 sized)) = .ok (ValidityVisitor.TypeKind.rawPointer 2 false)
  rw [slice_unsized]
  rfl
theorem hooks_raw_slice_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 82 = pure (.rawPointer 2 false) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [raw_slice_kind]
  with_unfolding_all rfl

theorem hooks_raw_slice_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 82 = pure "*mut [u8]" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 82 =
      PreparedReflection.actual.runtime.node 82 :=
    RootMetadataQueries.context_node 82
  rw [node]
  with_unfolding_all rfl

theorem context_raw_layout : CompilerFacts.layoutOf RootMetadataQueries.context 82 = .ok rawLayout := by
  unfold CompilerFacts.layoutOf
  rw [show RootMetadataQueries.context.runtime.lookup 82 = PreparedReflection.actual.runtime.lookup 82 from
    by rfl]
  rw [raw_layout_eq]
  rfl

theorem raw_builtin_deref : CompilerFacts.builtinDeref RootMetadataQueries.context 82 true = .ok (some 2) := by
  with_unfolding_all rfl

theorem compiler_raw_deref {K U C : Type} (choice : C) :
    (CompilerExecutionProviders.pointerCompiler (K := K) (U := U)
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts).builtinDeref choice 82 = pure (some 2) := by
  simp only [CompilerExecutionProviders.pointerCompiler]
  rw [show PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context = RootMetadataQueries.context from rfl,
    raw_builtin_deref]
  unfold_internal ".CompilerExecutionProviders.liftResult"
  unfold_internal ".CompilerExecutionProviders.query"
  rfl

theorem cast_raw_info : CompilerFactAdapters.castTypeInfo
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 82 = .ok (.rawPointer 2) := by decide +kernel

theorem cast_thin_info : CompilerFactAdapters.castTypeInfo
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 8 = .ok (.rawPointer 3) := by decide +kernel

theorem raw_retag_shape : CompilerFacts.retagTypeShape RootMetadataQueries.context 82 =
    .ok ⟨false, false, true, false⟩ := by
  with_unfolding_all rfl

theorem body_locals : HelperCompilerFacts.asMutPtrBody.body.locals = #[8,1,8,82,82] := by with_unfolding_all rfl

def block := HelperCompilerFacts.asMutPtrBody.body.basicBlocks[0]'(by decide +kernel)

theorem body_block : HelperCompilerFacts.asMutPtrBody.body.basicBlocks[0]? = some block := by
  with_unfolding_all rfl

theorem statement_kinds : block.statements.map (·.kind) = #[
    .StorageLive 2, .StorageLive 3, .StorageLive 4,
    .Assign ⟨4,#[]⟩ (.RawPtr .Mut ⟨1,#[.Deref]⟩),
    .Assign ⟨3,#[]⟩ (.Use (.Copy ⟨4,#[]⟩) .Yes),
    .Assign ⟨2,#[]⟩ (.Cast .PtrToPtr (.Move ⟨3,#[]⟩) 8),
    .Assign ⟨0,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes),
    .StorageDead 4, .StorageDead 3, .StorageDead 2] := by with_unfolding_all rfl

theorem terminator_return : block.terminator.kind = .Return := by with_unfolding_all rfl

theorem normal_block : block.cleanup = false := by with_unfolding_all rfl

open Lean Elab Command in
run_cmd do
  for declaration in [``context_raw_layout, ``raw_builtin_deref, ``compiler_raw_deref, ``cast_raw_info, ``cast_thin_info, ``raw_retag_shape, ``body_locals, ``body_block, ``statement_kinds, ``terminator_return, ``normal_block, ``raw_layout_eq, ``raw_type, ``raw_sized, ``raw_size, ``raw_data, ``raw_readable,
      ``raw_no_padding, ``raw_slice_kind, ``hooks_raw_slice_kind, ``hooks_raw_slice_name] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end
end DuplicatePrefix.AsMutPtrFacts

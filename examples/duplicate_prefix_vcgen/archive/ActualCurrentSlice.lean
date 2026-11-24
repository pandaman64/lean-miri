import duplicate_prefix.CopyCompilerFacts
import duplicate_prefix.CanonicalConfigFacts

namespace DuplicatePrefix.ActualCurrentSlice
open Miri Miri.Input Miri.ABI Miri.Interpreter
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

noncomputable def layout : LocalLayout :=
  (PreparedReflection.actual.layoutResults[2]'(by decide +kernel)).toOption.getD RootCompilerFacts.sliceLayout

private theorem reflection_match : (PreparedReflection.actual.runtime.lookup 2).toOption = some layout := by
  let metadata := PreparedReflection.actual.runtime
  have observation : metadata.node 2 = .ok metadata.source.types[2] := by rfl
  change (metadata.lookup 2).toOption = _
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : metadata.source.types[2].sourceLayout.normalizedType = 2 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : metadata.source.types[2]? = some metadata.source.types[2] := by rfl
  have shape : metadata.source.types[2].shape = .slice 3 := by rfl
  have ordinary : metadata.source.types[2].sourceLayout.specialFloat = none := by rfl
  have noX87 : metadata.source.types[2].sourceLayout.isX87F80 = false := rfl
  have element : ConcreteTypeLayout.calculate.go metadata.source metadata.target metadata.source.types.size 3
      ({} : Std.HashMap Nat LayoutData) =
      .ok (CopyCompilerFacts.byteLayout.layout, ({} : Std.HashMap Nat LayoutData).insert 3
        CopyCompilerFacts.byteLayout.layout) := by
    have fuel : metadata.source.types.size = 194 := rfl
    rw [fuel, ConcreteTypeLayout.calculate.go.eq_2]
    unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
    have elemRow : metadata.source.types[3]? = some metadata.source.types[3] := by rfl
    have elemNorm : metadata.source.types[3].sourceLayout.normalizedType = 3 := rfl
    have elemShape : metadata.source.types[3].shape = .uint (.known .u8) := by rfl
    have elemOrdinary : metadata.source.types[3].sourceLayout.specialFloat = none := by rfl
    have elemNoX87 : metadata.source.types[3].sourceLayout.isX87F80 = false := rfl
    simp [StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet,
      Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
      get, modify, MonadStateOf.modifyGet, MonadLift.monadLift, Except.map, Functor.map,
      Std.HashMap.getElem?_empty, elemRow, elemNorm, elemShape, elemOrdinary, elemNoX87]
    try with_unfolding_all rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
    Except.toOption, get, MonadLift.monadLift, Except.map, Functor.map,
    Std.HashMap.getElem?_empty, hrow, normalized, shape, ordinary, noX87, element]
  with_unfolding_all rfl

theorem lookup : PreparedReflection.actual.runtime.lookup 2 = .ok layout := by
  have result := reflection_match
  generalize PreparedReflection.actual.runtime.lookup 2 = actual at result ⊢
  cases actual
  · simp [Except.toOption] at result
  · simpa [Except.toOption] using result

theorem align : layout.layout.align.abi.pow2 = 0 := by decide +kernel

theorem ty : layout.ty = 2 := by decide +kernel

theorem compilerLayout :
    CompilerFacts.layoutOf PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 2 = .ok layout := by
  change (PreparedReflection.actual.runtime.lookup 2).mapError toString = .ok layout
  rw [lookup]
  rfl

end DuplicatePrefix.ActualCurrentSlice

#print axioms DuplicatePrefix.ActualCurrentSlice.lookup

#print axioms DuplicatePrefix.ActualCurrentSlice.compilerLayout

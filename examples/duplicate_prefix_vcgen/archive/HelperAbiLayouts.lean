import duplicate_prefix.RootCompilerCore
import Init.Data.List.Monadic

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.HelperAbiLayouts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter

private def checkedOk {Error Value : Type} : (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
private theorem checkedOk_eq {Error Value : Type} (result : Except Error Value) (supported : result.isOk = true) :
    result = .ok (checkedOk result supported) := by
  cases result with
  | ok value => rfl
  | error reason => cases supported

def unitLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[5]'(by decide +kernel)) (by decide +kernel)

private theorem unit_layout_exact :
    (PreparedReflection.actual.runtime.lookup 5).toOption = some unitLayout := by
  have observation : PreparedReflection.actual.runtime.node 5 =
      .ok PreparedReflection.actual.runtime.source.types[5] := by rfl
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : PreparedReflection.actual.runtime.source.types[5].sourceLayout.normalizedType = 5 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : PreparedReflection.actual.runtime.source.types[5]? =
      some PreparedReflection.actual.runtime.source.types[5] := by rfl
  have shape : PreparedReflection.actual.runtime.source.types[5].shape = .tuple #[] := by rfl
  have ordinary : PreparedReflection.actual.runtime.source.types[5].sourceLayout.specialFloat = none := by rfl
  have notX87 : PreparedReflection.actual.runtime.source.types[5].sourceLayout.isX87F80 = false := rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet, StateT.map, modify, modifyGet, MonadStateOf.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
    Except.toOption, get, MonadLift.monadLift, Except.map, Functor.map,
    Std.HashMap.getElem?_empty, hrow, normalized, shape, ordinary, notX87]
  unfold ConcreteLayout.univariant
  unfold_internal ".ConcreteLayout.univariantBiased"
  unfold_internal ".ConcreteTypeLayout.defaultRepr"
  with_unfolding_all rfl

theorem unit_layout_eq : PreparedReflection.actual.runtime.lookup 5 = .ok unitLayout := by
  have h := unit_layout_exact
  generalize PreparedReflection.actual.runtime.lookup 5 = result at h ⊢
  cases result <;> simpa [Except.toOption] using h

def sharedSliceLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[7]'(by decide +kernel)) (by decide +kernel)

private theorem shared_slice_layout_exact :
    (PreparedReflection.actual.runtime.lookup 7).toOption = some sharedSliceLayout := by
  have observation : PreparedReflection.actual.runtime.node 7 =
      .ok PreparedReflection.actual.runtime.source.types[7] := by rfl
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : PreparedReflection.actual.runtime.source.types[7].sourceLayout.normalizedType = 7 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : PreparedReflection.actual.runtime.source.types[7]? =
      some PreparedReflection.actual.runtime.source.types[7] := by rfl
  have shape : PreparedReflection.actual.runtime.source.types[7].shape = .reference 2 .Not .Erased := by rfl
  have ordinary : PreparedReflection.actual.runtime.source.types[7].sourceLayout.specialFloat = none := by rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
    Except.toOption, get, MonadLift.monadLift, Except.map, Functor.map,
    Std.HashMap.getElem?_empty, hrow, normalized, shape, ordinary]
  try rfl

theorem shared_slice_layout_eq : PreparedReflection.actual.runtime.lookup 7 = .ok sharedSliceLayout := by
  have h := shared_slice_layout_exact
  generalize PreparedReflection.actual.runtime.lookup 7 = result at h ⊢
  cases result <;> simpa [Except.toOption] using h

def callerLocationLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[36]'(by decide +kernel)) (by decide +kernel)

private theorem caller_location_layout_exact :
    (PreparedReflection.actual.runtime.lookup 36).toOption = some callerLocationLayout := by
  have observation : PreparedReflection.actual.runtime.node 36 =
      .ok PreparedReflection.actual.runtime.source.types[36] := by rfl
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : PreparedReflection.actual.runtime.source.types[36].sourceLayout.normalizedType = 36 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : PreparedReflection.actual.runtime.source.types[36]? =
      some PreparedReflection.actual.runtime.source.types[36] := by rfl
  have shape : PreparedReflection.actual.runtime.source.types[36].shape = .reference 37 .Not .Erased := by rfl
  have ordinary : PreparedReflection.actual.runtime.source.types[36].sourceLayout.specialFloat = none := by rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
    Except.toOption, get, MonadLift.monadLift, Except.map, Functor.map,
    Std.HashMap.getElem?_empty, hrow, normalized, shape, ordinary]
  try rfl

theorem caller_location_layout_eq : PreparedReflection.actual.runtime.lookup 36 = .ok callerLocationLayout := by
  have h := caller_location_layout_exact
  generalize PreparedReflection.actual.runtime.lookup 36 = result at h ⊢
  cases result <;> simpa [Except.toOption] using h


/-- The compiler's caller-location type is emitted with a region-bearing ID
and uses the same concrete layout as its erased type. -/
theorem caller_location_layout_alias :
    PreparedReflection.actual.runtime.lookup 35 = .ok callerLocationLayout := by
  have layout := caller_location_layout_eq
  have node35 : PreparedReflection.actual.runtime.node 35 =
      .ok PreparedReflection.actual.runtime.source.types[35] := rfl
  have node36 : PreparedReflection.actual.runtime.node 36 =
      .ok PreparedReflection.actual.runtime.source.types[36] := rfl
  have norm35 : PreparedReflection.actual.runtime.source.types[35].sourceLayout.normalizedType = 36 := rfl
  have norm36 : PreparedReflection.actual.runtime.source.types[36].sourceLayout.normalizedType = 36 := rfl
  simp only [RuntimeMetadata.lookup, node35, bind, Bind.bind, Except.bind, norm35]
  simp only [RuntimeMetadata.lookup, node36, bind, Bind.bind, Except.bind, norm36] at layout
  generalize ConcreteTypeLayout.calculate PreparedReflection.actual.runtime.source
    PreparedReflection.actual.runtime.target 36 = result at layout ⊢
  cases result <;> simpa [Except.mapError, Pure.pure, Except.pure] using layout

end
end DuplicatePrefix.HelperAbiLayouts

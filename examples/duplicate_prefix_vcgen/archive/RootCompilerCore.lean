import duplicate_prefix.PreparedContracts

/-! Kernel-checked immutable compiler queries for the fixed root instance.
No query below assumes successful execution or a memory access. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootCompilerFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter

noncomputable def rootAbiQuery := CompilerInstanceAbi.abiOfInstance
  PreparedReflection.actual.compiler.lifecycle.instances RootBody.reflected.functionInstance #[]

private def checkedOk {Error Value : Type} :
    (value : Except Error Value) → value.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

private theorem checkedOk_eq {Error Value : Type}
    (value : Except Error Value) (success : value.isOk = true) :
    value = .ok (checkedOk value success) := by
  cases value with
  | ok value => rfl
  | error error => cases success

/-- The fixed root ABI table row, linked to the actual instance lookup below. -/
def rootAbi : FnAbi MIR.TyId := checkedOk (PreparedReflection.actual.abiResults[0]'(by decide +kernel)) (by decide +kernel)

theorem root_abi_shape :
    (rootAbi.args.map (·.layout.ty), rootAbi.ret.layout.ty,
      rootAbi.cVariadic, rootAbi.fixedCount.toNat, rootAbi.conv, rootAbi.canUnwind) =
    (#[1, 4], 0, false, 2, .Rust, false) := by decide +kernel


def usizeLayout : TyAndLayout MIR.TyId :=
  checkedOk (PreparedReflection.actual.layoutResults[4]'(by decide +kernel)) (by decide +kernel)

private theorem usizeLayoutExact: (PreparedReflection.actual.runtime.lookup 4).toOption = some usizeLayout := by
  have observation : PreparedReflection.actual.runtime.node 4 =
      .ok PreparedReflection.actual.runtime.source.types[4] := by rfl
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : PreparedReflection.actual.runtime.source.types[4].sourceLayout.normalizedType = 4 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : PreparedReflection.actual.runtime.source.types[4]? =
      some PreparedReflection.actual.runtime.source.types[4] := by rfl
  have shape : PreparedReflection.actual.runtime.source.types[4].shape =
      .uint (.known .usize) := by rfl
  have ordinary : PreparedReflection.actual.runtime.source.types[4].sourceLayout.specialFloat = none := by rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
    Except.toOption, get, MonadLift.monadLift, Except.map, Functor.map,
    Std.HashMap.getElem?_empty, hrow, normalized, shape, ordinary]
  try rfl
theorem usize_layout_eq :
    PreparedReflection.actual.runtime.lookup 4 = .ok usizeLayout := by
  have h := usizeLayoutExact
  generalize PreparedReflection.actual.runtime.lookup 4 = result at h ⊢
  cases result <;> simpa [Except.toOption] using h


theorem usize_layout_supported :
    (PreparedReflection.actual.runtime.lookup 4).isOk = true := by rw [usize_layout_eq]; rfl

theorem usize_layout_shape :
    (usizeLayout.ty, usizeLayout.layout.size.bytes.toNat,
      usizeLayout.layout.align.abi.pow2) = (4, 8, 3) := by decide +kernel

theorem root_storage_trivial_bool :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 0 = .ok true := by decide +kernel

theorem root_storage_trivial_type2 :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 5 = .ok true := by decide +kernel

theorem root_storage_trivial_usize :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 4 = .ok true := by decide +kernel

theorem bool_layout_supported :
    (PreparedReflection.actual.runtime.lookup 0).isOk = true := by decide +kernel

def boolLayout : TyAndLayout MIR.TyId :=
  checkedOk (PreparedReflection.actual.layoutResults[0]'(by decide +kernel)) (by decide +kernel)

theorem bool_layout_eq : PreparedReflection.actual.runtime.lookup 0 = .ok boolLayout := by decide +kernel

theorem bool_layout_shape :
    (boolLayout.ty, boolLayout.layout.size.bytes.toNat,
      boolLayout.layout.align.abi.pow2) = (0, 1, 0) := by decide +kernel

theorem bool_layout_geometry : boolLayout.layout.size = Size.ofBytes 1 ∧
    boolLayout.layout.align.abi = Align.ONE := by decide +kernel

theorem bool_primitive_layout_eq :
    PreparedReflection.actual.compiler.primitiveLayout "bool" = .ok boolLayout := by with_unfolding_all rfl

theorem usize_primitive_layout_eq :
    PreparedReflection.actual.compiler.primitiveLayout "usize" = .ok usizeLayout := by
  change (PreparedReflection.actual.runtime.lookup 4).mapError toString = .ok usizeLayout
  rw [usize_layout_eq]
  rfl


def sliceLayout : TyAndLayout MIR.TyId :=
  checkedOk (PreparedReflection.actual.layoutResults[1]'(by decide +kernel)) (by decide +kernel)

private theorem sliceLayoutExact: (PreparedReflection.actual.runtime.lookup 1).toOption = some sliceLayout := by
  have observation : PreparedReflection.actual.runtime.node 1 =
      .ok PreparedReflection.actual.runtime.source.types[1] := by rfl
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : PreparedReflection.actual.runtime.source.types[1].sourceLayout.normalizedType = 1 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : PreparedReflection.actual.runtime.source.types[1]? =
      some PreparedReflection.actual.runtime.source.types[1] := by rfl
  have shape : PreparedReflection.actual.runtime.source.types[1].shape =
      .reference 2 .Mut .Erased := by rfl
  have ordinary : PreparedReflection.actual.runtime.source.types[1].sourceLayout.specialFloat = none := by rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet,
    Bind.bind, Pure.pure, Except.bind, Except.pure, MonadStateOf.get, getThe, liftM, monadLift,
    Except.toOption, get, MonadLift.monadLift, Except.map, Functor.map,
    Std.HashMap.getElem?_empty, hrow, normalized, shape, ordinary]
  try rfl
theorem slice_layout_eq :
    PreparedReflection.actual.runtime.lookup 1 = .ok sliceLayout := by
  have h := sliceLayoutExact
  generalize PreparedReflection.actual.runtime.lookup 1 = result at h ⊢
  cases result <;> simpa [Except.toOption] using h


theorem slice_layout_supported :
    (PreparedReflection.actual.runtime.lookup 1).isOk = true := by rw [slice_layout_eq]; rfl

theorem slice_layout_shape :
    (sliceLayout.ty, sliceLayout.layout.size.bytes.toNat, sliceLayout.layout.align.abi.pow2) =
      (1, 16, 3) := by decide +kernel

theorem root_abi_layouts :
    (rootAbi.args.getD 0 rootAbi.ret).layout = sliceLayout ∧
    (rootAbi.args.getD 1 rootAbi.ret).layout = usizeLayout ∧
    rootAbi.ret.layout = boolLayout := by
  constructor
  · with_unfolding_all rfl
  constructor <;> with_unfolding_all rfl

theorem root_storage_trivial_slice :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 1 = .ok true := by decide +kernel

theorem root_storage_trivial_never :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.runtime 6 = .ok true := by decide +kernel

open Lean Elab Command in
run_cmd do
  for declaration in #[``rootAbi,
      ``root_abi_shape, ``usize_layout_supported,
      ``usize_layout_eq, ``usize_layout_shape, ``root_storage_trivial_bool,
      ``root_storage_trivial_type2, ``root_storage_trivial_usize,
      ``bool_layout_supported, ``bool_layout_eq, ``bool_layout_shape,
      ``bool_primitive_layout_eq, ``usize_primitive_layout_eq, ``slice_layout_supported,
      ``slice_layout_eq, ``slice_layout_shape, ``root_abi_layouts, ``root_storage_trivial_slice,
      ``root_storage_trivial_never] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

#print axioms root_abi_shape
end
end DuplicatePrefix.RootCompilerFacts

import duplicate_prefix.RootCompilerCore
import Init.Data.List.Monadic

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace DuplicatePrefix.LocationPointeeLayout
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

private def adtAt (id : TypeId) : Option AdtShape :=
  match (PreparedReflection.actual.runtime.source.types[id]?).map (fun (row : TypeNode) => row.shape) with
  | some (TypeShape.adt value) => some value
  | _ => none

private def locationAdt : AdtShape := (adtAt 37).get (by decide +kernel)
private def nonnullAdt : AdtShape := (adtAt 38).get (by decide +kernel)
private def phantomAdt : AdtShape := (adtAt 41).get (by decide +kernel)

def locationLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[37]'(by decide +kernel)) (by decide +kernel)

open Lean Elab in
elab "full_scalar_at" : term => do
  let candidates := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".ConcreteTypeLayout.fullScalar" then some name else none
  match candidates with
  | [name] => return mkConst name
  | _ => throwError "expected exact concrete layout fullScalar"

private def rawPointerScalar : Scalar :=
  .Initialized (value := .Pointer AddressSpace.ZERO) (validRange := ⟨0, 18446744073709551615⟩)
private def restrictedPointerScalar : Scalar :=
  .Initialized (value := .Pointer AddressSpace.ZERO) (validRange := ⟨1, 18446744073709551615⟩)
private def usizeScalar : Scalar :=
  .Initialized (value := .Int .I64 false) (validRange := ⟨0, 18446744073709551615⟩)

private theorem rawPointerFull :
    full_scalar_at PreparedReflection.actual.runtime.target (.Pointer AddressSpace.ZERO) =
      .ok rawPointerScalar := rfl
private theorem usizeFull :
    full_scalar_at PreparedReflection.actual.runtime.target (.Int .I64 false) = .ok usizeScalar := rfl
private theorem pointerTailStr :
    ConcreteTypeLayout.pointerTail PreparedReflection.actual.runtime.source 195 34 = .ok .str := rfl
private theorem pointerInteger : PreparedReflection.actual.runtime.target.ptrSizedInteger = .ok .I64 := rfl
private theorem rawKind : PreparedReflection.actual.runtime.source.types[40].shapeKind = .rawPointer := rfl

private def rawStrLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[40]'(by decide +kernel)) (by decide +kernel)

private theorem strPair :
    ConcreteLayout.scalarPair PreparedReflection.actual.runtime.target rawPointerScalar usizeScalar =
      .ok rawStrLayout.layout := rfl
private theorem strPairRepr : rawStrLayout.layout.backendRepr =
    .ScalarPair (a := rawPointerScalar) (b := usizeScalar) (bOffset := Size.ofBytes 8) := rfl
private theorem rawRange : rawPointerScalar.validRange PreparedReflection.actual.runtime.target =
    .ok ⟨0,18446744073709551615⟩ := rfl
private theorem restrictRange : rawPointerScalar.setValidRange ⟨1#128,18446744073709551615#128⟩ =
     .ok restrictedPointerScalar := rfl


private theorem mapErrorOk (f : Error → Error') (value : Value) :
    (Except.ok value : Except Error Value).mapError f = .ok value := rfl

open Lean Elab in
elab "integer_at" : term => do
  let candidates := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".ConcreteTypeLayout.integer" then some name else none
  match candidates with
  | [name] => return mkConst name
  | _ => throwError "expected exact concrete layout integer"

private def u32Scalar : Scalar :=
  .Initialized (value := .Int .I32 false) (validRange := ⟨0,4294967295⟩)
private def u32Layout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[21]'(by decide +kernel)) (by decide +kernel)
private theorem u32Integer :
    integer_at PreparedReflection.actual.runtime.target .u32 = .ok .I32 := rfl
private theorem u32Full :
    full_scalar_at PreparedReflection.actual.runtime.target (.Int .I32 false) = .ok u32Scalar := rfl
private theorem u32Concrete :
    ConcreteLayout.scalarLayout PreparedReflection.actual.runtime.target u32Scalar =
      .ok u32Layout.layout := rfl
private theorem nonnullSized :
    SourceDeclarationQueries.maybeUnsized PreparedReflection.actual.runtime.source.sourceTraits
      nonnullAdt.definition = .ok false := by decide +kernel
private theorem phantomSized :
    SourceDeclarationQueries.maybeUnsized PreparedReflection.actual.runtime.source.sourceTraits
      phantomAdt.definition = .ok false := rfl
private theorem locationSized :
    SourceDeclarationQueries.maybeUnsized PreparedReflection.actual.runtime.source.sourceTraits
      locationAdt.definition = .ok false := by decide +kernel


private def patternStrLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[39]'(by decide +kernel)) (by decide +kernel)
private def nonnullLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[38]'(by decide +kernel)) (by decide +kernel)
private def phantomLayout : LocalLayout :=
  checkedOk (PreparedReflection.actual.layoutResults[41]'(by decide +kernel)) (by decide +kernel)
private theorem nonnullLayoutCalc : ConcreteLayout.univariant PreparedReflection.actual.runtime.target
    nonnullAdt.representation #[patternStrLayout.layout] .alwaysSized = .ok nonnullLayout.layout := by
  unfold ConcreteLayout.univariant
  unfold_internal ".ConcreteLayout.univariantBiased"
  with_unfolding_all rfl
private theorem nonnullLayoutExpanded :
    ConcreteLayout.univariant PreparedReflection.actual.runtime.target nonnullAdt.representation
      #[{
        fields := .Arbitrary [Size.ZERO].toArray [0].toArray
        variants := rawStrLayout.layout.variants
        backendRepr := .ScalarPair (a := restrictedPointerScalar) (b := usizeScalar) (bOffset := Size.ofBytes 8)
        largestNiche := some ⟨Size.ZERO, restrictedPointerScalar.primitive, ⟨BitVec.ofNat 128 1,BitVec.ofNat 128 18446744073709551615⟩⟩
        uninhabited := rawStrLayout.layout.uninhabited
        align := rawStrLayout.layout.align
        size := rawStrLayout.layout.size
        maxReprAlign := rawStrLayout.layout.maxReprAlign
        unadjustedAbiAlign := rawStrLayout.layout.unadjustedAbiAlign
        reprC := rawStrLayout.layout.reprC
        randomizationSeed := rawStrLayout.layout.randomizationSeed }]
      .alwaysSized = .ok nonnullLayout.layout := by
  exact nonnullLayoutCalc

private theorem phantomLayoutCalc : ConcreteLayout.univariant PreparedReflection.actual.runtime.target
    phantomAdt.representation #[] .alwaysSized = .ok phantomLayout.layout := by
  unfold ConcreteLayout.univariant
  unfold_internal ".ConcreteLayout.univariantBiased"
  with_unfolding_all rfl
private theorem locationLayoutCalc : ConcreteLayout.univariant PreparedReflection.actual.runtime.target
    locationAdt.representation #[nonnullLayout.layout,u32Layout.layout,u32Layout.layout,phantomLayout.layout]
    .alwaysSized = .ok locationLayout.layout := by
  unfold ConcreteLayout.univariant
  unfold_internal ".ConcreteLayout.univariantBiased"
  cbv

theorem locationLayoutExact :
    (PreparedReflection.actual.runtime.lookup 37).toOption = some locationLayout := by
  have observation : PreparedReflection.actual.runtime.node 37 =
      .ok PreparedReflection.actual.runtime.source.types[37] := by rfl
  rw [RuntimeMetadata.lookup, observation]
  simp only [bind, Bind.bind, Except.bind]
  have normalized : PreparedReflection.actual.runtime.source.types[37].sourceLayout.normalizedType = 37 := rfl
  rw [normalized]
  unfold ConcreteTypeLayout.calculate
  rw [ConcreteTypeLayout.calculate.go.eq_2]
  unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
  have hrow : PreparedReflection.actual.runtime.source.types[37]? =
      some PreparedReflection.actual.runtime.source.types[37] := by rfl
  have shape37 : PreparedReflection.actual.runtime.source.types[37].shape = .adt locationAdt := rfl
  have variant37 : locationAdt.variants = #[⟨0,"Location",#[
      ⟨0,"filename",38⟩, ⟨1,"line",21⟩, ⟨2,"col",21⟩, ⟨3,"_filename",41⟩]⟩] := rfl
  have notSimd37 : PreparedReflection.actual.runtime.source.types[37].sourceLayout.simd = none := rfl
  have kind37 : locationAdt.kind = .structKind := rfl
  have float37 : PreparedReflection.actual.runtime.source.types[37].sourceLayout.specialFloat = none := rfl
  have notX8737 : PreparedReflection.actual.runtime.source.types[37].sourceLayout.isX87F80 = false := rfl
  have row21 : PreparedReflection.actual.runtime.source.types[21]? = some PreparedReflection.actual.runtime.source.types[21] := rfl
  have norm21 : PreparedReflection.actual.runtime.source.types[21].sourceLayout.normalizedType = 21 := rfl
  have shape21 : PreparedReflection.actual.runtime.source.types[21].shape = .uint (.known .u32) := rfl
  have plain21 : PreparedReflection.actual.runtime.source.types[21].sourceLayout.specialFloat = none := rfl
  have notX8721 : PreparedReflection.actual.runtime.source.types[21].sourceLayout.isX87F80 = false := rfl
  have row38 : PreparedReflection.actual.runtime.source.types[38]? = some PreparedReflection.actual.runtime.source.types[38] := rfl
  have norm38 : PreparedReflection.actual.runtime.source.types[38].sourceLayout.normalizedType = 38 := rfl
  have shape38 : PreparedReflection.actual.runtime.source.types[38].shape = .adt nonnullAdt := rfl
  have plain38 : PreparedReflection.actual.runtime.source.types[38].sourceLayout.specialFloat = none := rfl
  have notX8738 : PreparedReflection.actual.runtime.source.types[38].sourceLayout.isX87F80 = false := rfl
  have row39 : PreparedReflection.actual.runtime.source.types[39]? = some PreparedReflection.actual.runtime.source.types[39] := rfl
  have norm39 : PreparedReflection.actual.runtime.source.types[39].sourceLayout.normalizedType = 39 := rfl
  have shape39 : PreparedReflection.actual.runtime.source.types[39].shape = .patternType 40 .notNull := rfl
  have plain39 : PreparedReflection.actual.runtime.source.types[39].sourceLayout.specialFloat = none := rfl
  have notX8739 : PreparedReflection.actual.runtime.source.types[39].sourceLayout.isX87F80 = false := rfl
  have row40 : PreparedReflection.actual.runtime.source.types[40]? = some PreparedReflection.actual.runtime.source.types[40] := rfl
  have norm40 : PreparedReflection.actual.runtime.source.types[40].sourceLayout.normalizedType = 40 := rfl
  have shape40 : PreparedReflection.actual.runtime.source.types[40].shape = .rawPointer 34 .Not := rfl
  have plain40 : PreparedReflection.actual.runtime.source.types[40].sourceLayout.specialFloat = none := rfl
  have notX8740 : PreparedReflection.actual.runtime.source.types[40].sourceLayout.isX87F80 = false := rfl
  have row41 : PreparedReflection.actual.runtime.source.types[41]? = some PreparedReflection.actual.runtime.source.types[41] := rfl
  have norm41 : PreparedReflection.actual.runtime.source.types[41].sourceLayout.normalizedType = 41 := rfl
  have shape41 : PreparedReflection.actual.runtime.source.types[41].shape = .adt phantomAdt := rfl
  have plain41 : PreparedReflection.actual.runtime.source.types[41].sourceLayout.specialFloat = none := rfl
  have notX8741 : PreparedReflection.actual.runtime.source.types[41].sourceLayout.isX87F80 = false := rfl
  have variants38 : nonnullAdt.variants = #[⟨0,"NonNull",#[⟨0,"pointer",39⟩]⟩] := rfl
  have kind38 : nonnullAdt.kind = .structKind := rfl
  have notSimd38 : PreparedReflection.actual.runtime.source.types[38].sourceLayout.simd = none := rfl
  have variants41 : phantomAdt.variants = #[⟨0,"PhantomData",#[]⟩] := rfl
  have kind41 : phantomAdt.kind = .structKind := rfl
  have notSimd41 : PreparedReflection.actual.runtime.source.types[41].sourceLayout.simd = none := rfl
  have noCell37 : PreparedReflection.actual.runtime.source.types[37].sourceLayout.isUnsafeCell = false := rfl
  have noPin37 : PreparedReflection.actual.runtime.source.types[37].sourceLayout.isUnsafePinned = false := rfl
  have noCell38 : PreparedReflection.actual.runtime.source.types[38].sourceLayout.isUnsafeCell = false := rfl
  have noPin38 : PreparedReflection.actual.runtime.source.types[38].sourceLayout.isUnsafePinned = false := rfl
  have noCell41 : PreparedReflection.actual.runtime.source.types[41].sourceLayout.isUnsafeCell = false := rfl
  have noPin41 : PreparedReflection.actual.runtime.source.types[41].sourceLayout.isUnsafePinned = false := rfl
  have typeCount : PreparedReflection.actual.runtime.source.types.size = 194 := rfl
  simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet, StateT.map,
    modify, modifyGet, MonadStateOf.modifyGet, Bind.bind, Pure.pure, Except.bind, Except.pure,
    MonadStateOf.get, getThe, liftM, monadLift, Except.toOption, get, MonadLift.monadLift,
    Except.map, Functor.map, Std.HashMap.getElem?_empty, hrow, normalized, shape37,
    variant37, notSimd37, kind37, float37, notX8737, Array.mapM_eq_mapM_toList, List.mapM, List.mapM.loop, row21, norm21, shape21, plain21, notX8721, row38, norm38, shape38, plain38, notX8738, row39, norm39, shape39, plain39, notX8739, row40, norm40, shape40, plain40, notX8740, row41, norm41, shape41, plain41, notX8741, variants38, kind38, notSimd38, variants41, kind41, notSimd41, noCell37, noPin37, noCell38, noPin38, noCell41, noPin41, typeCount
  , Std.HashMap.getElem?_insert, rawPointerFull, usizeFull, pointerTailStr, pointerInteger, rawKind,
     strPair, strPairRepr, rawRange, restrictRange, mapErrorOk, u32Integer, u32Full, u32Concrete,
     nonnullSized, phantomSized, locationSized, nonnullLayoutCalc, nonnullLayoutExpanded, phantomLayoutCalc, locationLayoutCalc]
  repeat' first
    | (rw [ConcreteTypeLayout.calculate.go.eq_2]
       try unfold_internal ".Miri.Input.ConcreteTypeLayout.typeNode"
       simp [StateT.run', StateT.bind, StateT.lift, StateT.pure, StateT.get, StateT.modifyGet, StateT.map,
    modify, modifyGet, MonadStateOf.modifyGet, Bind.bind, Pure.pure, Except.bind, Except.pure,
    MonadStateOf.get, getThe, liftM, monadLift, Except.toOption, get, MonadLift.monadLift,
    Except.map, Functor.map, Std.HashMap.getElem?_empty, hrow, normalized, shape37,
    variant37, notSimd37, kind37, float37, notX8737, Array.mapM_eq_mapM_toList, List.mapM, List.mapM.loop, row21, norm21, shape21, plain21, notX8721, row38, norm38, shape38, plain38, notX8738, row39, norm39, shape39, plain39, notX8739, row40, norm40, shape40, plain40, notX8740, row41, norm41, shape41, plain41, notX8741, variants38, kind38, notSimd38, variants41, kind41, notSimd41, noCell37, noPin37, noCell38, noPin38, noCell41, noPin41, typeCount
  , Std.HashMap.getElem?_insert, rawPointerFull, usizeFull, pointerTailStr, pointerInteger, rawKind,
     strPair, strPairRepr, rawRange, restrictRange, mapErrorOk, u32Integer, u32Full, u32Concrete,
     nonnullSized, phantomSized, locationSized, nonnullLayoutCalc, nonnullLayoutExpanded, phantomLayoutCalc, locationLayoutCalc])
  rfl

theorem location_layout_eq : PreparedReflection.actual.runtime.lookup 37 = .ok locationLayout := by
  have h := locationLayoutExact
  generalize PreparedReflection.actual.runtime.lookup 37 = result at h ⊢
  cases result <;> simpa [Except.toOption] using h

#print axioms location_layout_eq
end
end DuplicatePrefix.LocationPointeeLayout

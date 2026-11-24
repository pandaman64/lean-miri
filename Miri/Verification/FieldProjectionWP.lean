import Miri.Interpreter.PlaceDynamic
import Miri.Verification.RvalueWP

/-! Exact preconditions for the layout and offset checks in a field projection. -/

namespace Miri.Verification.FieldProjectionWP

open Miri.ABI Miri.Interpreter Miri.Memory RvalueWP

variable {P S C E : Type}

/-- A memory place uses the configured pointer offset operation. A local place
checks that the projected layout fits, checks both size additions, and retains
the frame, local ID and frame identity. -/
def offsetPre (hooks : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (amount : Size) (mode : OffsetMode)
    (metadata : MemPlaceMeta P) (layout : LocalLayout)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  match base.ref with
  | .memory place =>
    actionPre (hooks.place.memoryOffset choice place amount mode metadata)
      (fun result => post ⟨.memory result, layout⟩) onError
  | .local frame localId oldOffset identity =>
    if !layout.layout.isSized || metadata.hasMeta then
      onError (.invalidProgram "local projection cannot store metadata or unsized layout")
    else
      scalarCheckPre ((amount.add layout.layout.size).mapError
        fun error => .invalidProgram s!"place size: {repr error}") (fun bound =>
        if bound.bytes > base.layout.layout.size.bytes then
          onError (.invalidProgram "local projection exceeds enclosing place")
        else
          scalarCheckPre (((oldOffset.getD Size.ZERO).add amount).mapError
            fun error => .invalidProgram s!"place size: {repr error}") (fun offset =>
            post ⟨.local frame localId (some offset) identity, layout⟩) onError) onError

theorem actionPre_offsetWithMeta (hooks : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (amount : Size) (mode : OffsetMode)
    (metadata : MemPlaceMeta P) (layout : LocalLayout)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.offsetWithMeta hooks choice base amount mode metadata layout) post onError =
      offsetPre hooks choice base amount mode metadata layout post onError := by
  rcases base with ⟨ref, baseLayout⟩
  cases ref with
  | memory place =>
    simp only [PlaceDynamic.offsetWithMeta, offsetPre, actionPre_bind_fun]
    rfl
  | «local» frame localId oldOffset identity =>
    simp only [PlaceDynamic.offsetWithMeta, offsetPre]
    rw [actionPre_ite]
    split
    · rfl
    · cases amount.add layout.layout.size with
      | error => rfl
      | ok bound =>
        change actionPre ((pure bound : PlaceM S Size) >>= _) post onError =
          scalarCheckPre (.ok bound) _ onError
        rw [pure_bind, actionPre_ite]
        funext before
        simp only [scalarCheckPre]
        split
        · rfl
        · cases (oldOffset.getD Size.ZERO).add amount <;> rfl

/-- Reuse the parent's metadata only for an unsized field. The unsized branch
resolves dynamic alignment before applying any packed alignment restriction. -/
def fieldPre [PointerProvenance P] (hooks : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (index : Nat)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  scalarCheckPre ((base.layout.layout.fields.offset index).mapError
    fun error => .invalidProgram s!"place layout: {repr error}") (fun offset =>
    actionPre (hooks.field choice base.layout index) (fun layout =>
      if !layout.layout.isSized then
        if base.layout.layout.isSized then onError (.invalidProgram "unsized field in sized parent")
        else
          let metadata := match base.ref with | .memory place => place.metadata | .local .. => .none
          actionPre (DynamicLayout.alignmentFromMeta hooks.dynamic choice hooks.dynamicFuel metadata layout)
            (fun
              | some alignment =>
                actionPre (hooks.packedAlign choice base.layout.ty) (fun packed =>
                  let alignment := match packed with
                    | some cap => alignment.min cap
                    | none => alignment
                  scalarCheckPre ((offset.alignTo alignment).mapError
                    fun error => .invalidProgram (toString error)) (fun adjusted =>
                    offsetPre hooks choice base adjusted .inbounds metadata layout post onError) onError)
                  onError
              | none =>
                if offset != Size.ZERO then onError (.unsupported "ExternTypeField")
                else offsetPre hooks choice base offset .inbounds metadata layout post onError)
            onError
      else offsetPre hooks choice base offset .inbounds .none layout post onError) onError) onError

theorem actionPre_field [PointerProvenance P] (hooks : PlaceProjectionHooks P S C E)
    (choice : C) (base : RuntimePlace P) (index : Nat)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.field hooks choice base index) post onError =
      fieldPre hooks choice base index post onError := by
  simp only [PlaceDynamic.field, fieldPre]
  cases base.layout.layout.fields.offset index with
  | error => rfl
  | ok offset =>
    simp only [actionPre_bind_fun]
    change actionPre (hooks.field choice base.layout index) _ _ = _
    congr 1
    funext layout
    rw [actionPre_ite]
    split
    · rw [actionPre_ite]
      split
      · rfl
      · simp only [actionPre_bind_fun]
        rcases base with ⟨ref, parentLayout⟩
        cases ref <;> congr 1 <;> funext alignment <;> cases alignment
        all_goals first
          | rw [actionPre_ite]
            split
            · rfl
            · simp only [pure_bind, actionPre_offsetWithMeta] <;> rfl
          | rename_i align
            simp only [actionPre_bind_fun]
            congr 1
            funext packed
            cases offset.alignTo (match packed with | some cap => align.min cap | none => align) with
            | error => rfl
            | ok adjusted => simp only [actionPre_offsetWithMeta] <;> rfl

    · simp only [pure_bind, actionPre_offsetWithMeta] <;> rfl

end Miri.Verification.FieldProjectionWP

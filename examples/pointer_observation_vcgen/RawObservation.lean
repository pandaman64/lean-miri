import GeneratedPointer

/-! Verified observations of the imported raw-pointer store. -/
namespace PointerObservation

open Miri.ABI Miri.Interpreter Miri.Memory Miri.Verification Miri.MIR Fixture
open RvalueWP

set_option maxHeartbeats 2600000
set_option maxRecDepth 40000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
attribute [local cbv_opaque] evalPre writeImmediateAfterAccess
attribute [local cbv_eval] writeImmediateAfterAccess_scalar
attribute [local cbv_opaque] ValidityVisitor.validatePlace ValidityVisitor.visit
attribute [local cbv_eval] ValidityVisitor.validatePlace_shallow

private theorem usePre {P S C V : Type} (hooks : RvalueHooks P S C V) (choice : C)
    (operand : Operand) (retag : WithRetag) (dest : Place)
    (post : S → Prop) (failure : StepError → S → Prop) (before : S) :
    evalPre hooks choice (.Use operand retag) dest post failure before =
      actionPre (hooks.evalPlace choice dest true) (fun target =>
        actionPre (hooks.evalOperand choice operand (some (hooks.placeLayout target))) (fun value =>
          actionPre (hooks.withRetagMode choice (if retag == .Yes then .Default else .None)
            (hooks.copyOp choice value target)) (fun _ => post) failure) failure) failure before := rfl

private theorem rawPre {P S C V : Type} (hooks : RvalueHooks P S C V) (choice : C)
    (kind : RawPtrKind) (src dest : Place)
    (post : S → Prop) (failure : StepError → S → Prop) (before : S) :
    evalPre hooks choice (.RawPtr kind src) dest post failure before =
      actionPre (hooks.evalPlace choice dest true) (fun target =>
        actionPre (hooks.placeBaseRaw choice src) (fun baseRaw =>
          actionPre (hooks.evalPlace choice src false) (fun input =>
            actionPre (hooks.forceAllocation choice input) (fun memory =>
              actionPre (hooks.toRef choice memory) (fun immediate =>
                let value : RvalueImmTy P := ⟨immediate, hooks.placeLayout target⟩
                let write := fun adjusted : RvalueImmTy P =>
                  actionPre (hooks.writeImmediate choice adjusted.imm target) (fun _ => post) failure
                if !baseRaw && kind != .FakeForPtrMetadata then
                  actionPre (hooks.withRetagMode choice .Raw do
                    return (← hooks.retagPtrValue choice value value.layout.ty).getD value) write failure
                else write value) failure) failure) failure) failure) failure before := rfl

attribute [local cbv_eval] usePre rawPre

local macro "reduce_raw_pointer_visit" : tactic =>
  `(tactic|
    conv =>
      pattern (ValidityVisitor.visit _ _ 32 _ _ _)
      tactic =>
        refine ValidityVisitor.visit_raw_sized_pointer (P := Provenance) _ _ 31 _ _ _
          ?value ?layout 2 ?abi ?classified ?read ?backend ?pointer ?ranges
        case classified => cbv <;> rfl
        case read => cbv <;> rfl
        case backend => cbv <;> rfl
        case pointer => cbv <;> rfl
        case ranges => cbv <;> rfl)

/-- The raw store through the original tag succeeds for every initial byte. -/
theorem rawWriteRequired (initial : UInt8) : required .rawWrite initial := by
  cbv
  reduce_raw_pointer_visit
  cbv
  conv =>
    pattern (ValidityVisitor.visit _ _ 32 _ _ _)
    tactic =>
      refine ValidityVisitor.visit_integer_memory (P := Provenance) _ _ 31 _ _ _
        ?numeric_value ?numeric_layout ?numeric_memory ?numeric_ranges ?numeric_updated
        ?numeric_classified ?numeric_read ?numeric_clear ?numeric_operand
        ?numeric_reset ?numeric_tracked ?numeric_sized ?numeric_marked
      case numeric_classified => cbv <;> rfl
      case numeric_read => cbv <;> rfl
      case numeric_clear => cbv <;> rfl
      case numeric_operand => cbv <;> rfl
      case numeric_reset => cbv <;> rfl
      case numeric_tracked => cbv <;> rfl
      case numeric_sized => cbv <;> rfl
      case numeric_marked => cbv <;> rfl
  cbv
  simp only [eq_self, true_and]

/-- The emitted raw-write prefix observes byte 73 and the original tag. -/
theorem rawWriteWindow (initial : UInt8) :
    match scenario 1 initial false with
    | .error _ => False
    | .ok (config, before) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun after => observed .rawWrite initial after (.ok ()) = true)
        (fun error after => observed .rawWrite initial after (.error error) = true)
        ((GeneratedBodySafety.window_1_bb0_0 config limits).take 4) before := by
  exact (generatedPrefix_iff_checked .rawWrite initial).mpr
    ((required_iff_checked .rawWrite initial).mp (rawWriteRequired initial))

/-- The Frozen tag rejects the store and retains the original byte. -/
theorem frozenWriteRequired (initial : UInt8) : required .frozenWrite initial := by
  cbv
  reduce_raw_pointer_visit
  cbv
  simp only [eq_self, true_and]

/-- The emitted store reports the precise Frozen-tag error with the original
byte and the preserved raw pointer tag. -/
theorem frozenWriteWindow (initial : UInt8) :
    match scenario 1 initial true with
    | .error _ => False
    | .ok (config, before) =>
      GeneratedBodyVC.windowPrefixPre config limits (fun _ _ => True)
        (fun after => observed .frozenWrite initial after (.ok ()) = true)
        (fun error after => observed .frozenWrite initial after (.error error) = true)
        ((GeneratedBodySafety.window_1_bb0_0 config limits).take 4) before := by
  exact (generatedPrefix_iff_checked .frozenWrite initial).mpr
    ((required_iff_checked .frozenWrite initial).mp (frozenWriteRequired initial))

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``rawWriteRequired, ``rawWriteWindow, ``frozenWriteRequired, ``frozenWriteWindow] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms rawWriteWindow
#print axioms frozenWriteWindow

end PointerObservation

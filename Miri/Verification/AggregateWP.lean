import Miri.Verification.RvalueWP

/-! Pull back assignment continuations across the interpreter's aggregate
and repeat actions. Every intermediate effect retains its own failure state. -/
namespace Miri.Verification.AggregateWP

open Miri.ABI Miri.Interpreter Miri.MIR Miri.Memory Std.WP
open RvalueWP

variable {P S C V A : Type}

private theorem purePre (value : A) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (pure value) post onError = post value :=
  funext (actionPre_pure value post onError)

private theorem throwPre (error : StepError) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (throw error) post onError = onError error :=
  funext (actionPre_throw error post onError)

private theorem liftPre (result : Except StepError A)
    (post : A → S → Prop) (onError : StepError → S → Prop) :
    actionPre (aggregateLift result) post onError =
      match result with
      | .ok value => post value
      | .error error => onError error := by
  cases result <;> rfl

/-- A zero-length repeat still evaluates the operand, forces the destination
allocation and checks mutable access. A nonempty repeat copies the first
element, then uses the interpreter's bulk copy with the resulting bytes. -/
@[miri_rvalue] theorem actionPre_writeRepeat (h : AggregateHooks P S C V) (choice : C)
    (operand : Operand) (dest : V) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (writeRepeat h choice operand dest) post onError =
      actionPre (h.evalOperand choice operand none) (fun source =>
        if !source.layout.layout.isSized then onError (.invalidProgram "repeat source is unsized")
        else actionPre (h.forceAllocation choice dest) (fun allocated =>
          actionPre (h.length choice allocated) (fun length =>
            if length == 0 then actionPre (h.getPlaceAllocMut choice allocated) post onError
            else actionPre (h.projectIndex choice allocated 0) (fun first =>
              actionPre (h.copyOp choice source first) (fun _ =>
                let size := (h.placeLayout first).layout.size
                match h.placePointer first with
                | .ok firstPtr =>
                  match h.wrappingOffset firstPtr size with
                  | .ok restPtr =>
                    actionPre (h.memCopyRepeatedly choice firstPtr restPtr size (length - 1) true)
                      post onError
                  | .error error => onError error
                | .error error => onError error) onError) onError) onError) onError) onError := by
  simp only [writeRepeat, actionPre_bind_fun, actionPre_ite, throwPre, liftPre]
  congr 1
  funext source
  split
  · rfl
  · congr 1
    funext allocated
    congr 1
    funext length
    split
    · rfl
    · congr 1
      funext first
      congr 1
      funext _
      cases h.placePointer first with
      | error => rfl
      | ok firstPtr =>
        dsimp
        cases h.wrappingOffset firstPtr (h.placeLayout first).layout.size <;> rfl

/-- Process aggregate fields in their MIR order, preserving effects from
previous fields when a projection, operand evaluation or copy fails. -/
@[miri_rvalue] def fieldsPre (h : AggregateHooks P S C V) (choice : C)
    (operands : Array Operand) (dest : V) (activeField : Option FieldIndex)
    (post : S → Prop) (onError : StepError → S → Prop) : List Nat → S → Prop
  | [] => post
  | index :: remaining =>
    match operands[index]? with
    | none => onError (.invalidProgram "aggregate operand index")
    | some operand =>
      actionPre (h.projectField choice dest (activeField.getD index)) (fun field =>
        actionPre (h.evalOperand choice operand (some (h.placeLayout field))) (fun source =>
          actionPre (h.copyOpNoValidate choice source field false) (fun _ =>
            fieldsPre h choice operands dest activeField post onError remaining)
            onError) onError) onError

private theorem fieldsPre_eq (h : AggregateHooks P S C V) (choice : C)
    (operands : Array Operand) (dest : V) (activeField : Option FieldIndex)
    (post : S → Prop) (onError : StepError → S → Prop) (indices : List Nat) :
    actionPre
      (forIn indices PUnit.unit fun index _ => do
        let some operand := operands[index]? | do
          throw (.invalidProgram "aggregate operand index")
          pure (.yield PUnit.unit)
        let field ← h.projectField choice dest (activeField.getD index)
        let source ← h.evalOperand choice operand (some (h.placeLayout field))
        h.copyOpNoValidate choice source field false
        pure (.yield PUnit.unit))
      (fun _ => post) onError =
      fieldsPre h choice operands dest activeField post onError indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    rw [List.forIn_cons]
    simp only [fieldsPre]
    cases operands[index]? <;> simp only [ actionPre_bind_fun, purePre, throwPre, ih]

/-- Finish aggregate construction with the variant discriminant and the
interpreter's whole-place validity policy. -/
@[miri_rvalue] def finishPre (h : AggregateHooks P S C V) (choice : C) (dest : V)
    (variant : VariantIndex) (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    S → Prop :=
  actionPre (h.writeDiscriminant choice variant dest) (fun _ =>
    actionPre (h.enforceValidity choice (h.placeLayout dest)) (fun validate =>
      if validate then actionPre (h.validate choice dest) post onError else post ()) onError) onError

private def nonPointerPre (h : AggregateHooks P S C V) (choice : C) (operands : Array Operand)
    (dest variantDest : V) (variant : VariantIndex) (activeField : Option FieldIndex)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  let fields := fieldsPre h choice operands variantDest activeField
    (finishPre h choice dest variant post onError) onError (List.range' 0 operands.size)
  if activeField.isSome && operands.size != 1 then
    onError (.invalidProgram "union aggregate requires exactly one operand")
  else if activeField.isSome then actionPre (h.writeUninit choice dest) (fun _ => fields) onError
  else fields

private theorem actionPre_writeAggregate_tuple (h : AggregateHooks P S C V) (choice : C)
    (operands : Array Operand) (dest : V) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (writeAggregate h choice .Tuple operands dest) post onError =
      fieldsPre h choice operands dest none (finishPre h choice dest 0 post onError)
        onError (List.range' 0 operands.size) := by
  simp only [writeAggregate, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, actionPre_bind_fun, actionPre_ite, purePre]
  exact fieldsPre_eq h choice operands dest none (finishPre h choice dest 0 post onError)
    onError (List.range' 0 operands.size)

private theorem actionPre_writeAggregate_adt (h : AggregateHooks P S C V) (choice : C)
    (definition : DefId) (variant : VariantIndex) (args : Array GenericArg)
    (userType : Option UserTypeAnnotationIndex) (activeField : Option FieldIndex)
    (operands : Array Operand) (dest : V) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (writeAggregate h choice (.Adt definition variant args userType activeField) operands dest)
      post onError =
      actionPre (h.projectDowncast choice dest variant) (fun variantDest =>
        nonPointerPre h choice operands dest variantDest variant activeField post onError) onError := by
  simp only [writeAggregate, nonPointerPre, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, actionPre_bind_fun,
    actionPre_ite, purePre, throwPre]
  congr 1
  funext variantDest
  have fields := fieldsPre_eq h choice operands variantDest activeField
    (finishPre h choice dest variant post onError) onError (List.range' 0 operands.size)
  split
  · rfl
  · split
    · congr 1
      funext _
      exact fields
    · exact fields

private def rawPointerPre (h : AggregateHooks P S C V) (choice : C) (operands : Array Operand)
    (dest : V) (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  if operands.size != 2 then onError (.invalidProgram "raw pointer aggregate requires two operands")
  else
    match operands[0]?, operands[1]? with
    | none, _ => onError (.invalidProgram "missing raw pointer data")
    | _, none => onError (.invalidProgram "missing raw pointer metadata")
    | some data, some metadata =>
      actionPre (h.evalOperand choice data none) (fun data =>
        actionPre (h.readPointer choice data) (fun pointer =>
          actionPre (h.evalOperand choice metadata none) (fun metadata =>
            let copy := fun valueMetadata =>
              match Immediate.newPointerWithMeta pointer valueMetadata h.target with
              | .ok value =>
                actionPre (h.copyOp choice ⟨.immediate value, h.placeLayout dest⟩ dest) post onError
              | .error error =>
                onError (.invalidProgram s!"raw pointer aggregate representation failure: {repr error}")
            if metadata.layout.layout.isZst then copy .none
            else actionPre (h.readScalar choice metadata) (fun scalar => copy (.metadata scalar)) onError)
            onError) onError) onError

private theorem actionPre_writeAggregate_rawPointer (h : AggregateHooks P S C V) (choice : C)
    (pointee : TyId) (mutability : Miri.MIR.Mutability) (operands : Array Operand)
    (dest : V) (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    actionPre (writeAggregate h choice (.RawPtr pointee mutability) operands dest) post onError =
      rawPointerPre h choice operands dest post onError := by
  simp only [writeAggregate, rawPointerPre, actionPre_bind_fun, actionPre_ite, throwPre]
  split
  · rfl
  · cases operands[0]? with
    | none => simp only [actionPre_bind_fun, throwPre]
    | some dataOperand =>
      cases operands[1]? with
      | none => simp only [actionPre_bind_fun, throwPre]
      | some metadataOperand =>
        simp only [actionPre_bind_fun, actionPre_ite, purePre]
        congr 1
        funext data
        congr 1
        funext pointer
        congr 1
        funext metadata
        split
        · cases Immediate.newPointerWithMeta pointer .none h.target <;>
            simp only [actionPre_bind_fun, purePre, throwPre]
        · congr 1
          funext scalar
          cases Immediate.newPointerWithMeta pointer (.metadata scalar) h.target <;>
            simp only [actionPre_bind_fun, purePre, throwPre]

/-- Sequence the selected aggregate's effects, using the same field order and
discriminant/validation steps as the interpreter. Raw pointers are assembled
from their data pointer and metadata. -/
@[miri_rvalue] def aggregatePre (h : AggregateHooks P S C V) (choice : C)
    (kind : AggregateKind) (operands : Array Operand) (dest : V)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  match kind with
  | .Adt _ variant _ _ activeField =>
    actionPre (h.projectDowncast choice dest variant) (fun variantDest =>
      nonPointerPre h choice operands dest variantDest variant activeField post onError) onError
  | .RawPtr .. => rawPointerPre h choice operands dest post onError
  | .Array _ | .Tuple | .Closure .. | .Coroutine .. | .CoroutineClosure .. =>
    nonPointerPre h choice operands dest dest 0 none post onError

@[miri_rvalue] theorem actionPre_writeAggregate (h : AggregateHooks P S C V) (choice : C)
    (kind : AggregateKind) (operands : Array Operand) (dest : V)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    actionPre (writeAggregate h choice kind operands dest) post onError =
      aggregatePre h choice kind operands dest post onError := by
  cases kind with
  | Adt definition variant args userType activeField =>
    exact actionPre_writeAggregate_adt h choice definition variant args userType activeField
      operands dest post onError
  | RawPtr pointee mutability =>
    exact actionPre_writeAggregate_rawPointer h choice pointee mutability operands dest post onError
  | Array _ | Tuple | Closure _ _ | Coroutine _ _ | CoroutineClosure _ _ =>
    exact actionPre_writeAggregate_tuple h choice operands dest post onError

attribute [miri_rvalue] nonPointerPre rawPointerPre

section Canonical

variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host

@[miri_rvalue, spec] theorem canonical_writeRepeat (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (operand : Operand)
    (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).writeRepeat choice operand dest =
      writeRepeat (ExecutionMachine.aggregateHooks config limits) choice operand dest := rfl

@[miri_rvalue, spec] theorem canonical_writeAggregate (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (kind : AggregateKind)
    (operands : Array Operand) (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).writeAggregate choice kind operands dest =
      writeAggregate (ExecutionMachine.aggregateHooks config limits) choice kind operands dest := rfl

/-- The length of a sized repeat destination comes entirely from its layout.
A non-array reaches the typed error at the state left by allocation. -/
@[miri_rvalue] theorem actionPre_canonical_length_sized (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (dest : RuntimePlace Provenance)
    (post : UInt64 → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop)
    (sized : dest.layout.layout.isSized = true) :
    actionPre ((ExecutionMachine.aggregateHooks config limits).length choice dest) post onError =
      match dest.layout.layout.fields with
      | .Array _ count => post count
      | _ => onError (.invalidProgram "length of non-array") := by
  change actionPre (PlaceDynamic.length
    (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)) choice dest)
      post onError = _
  simp only [PlaceDynamic.length, sized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases dest.layout.layout.fields <;> rfl

private theorem aggregateLiftPre (result : Except StepError A)
    (post : A → S → Prop) (onError : StepError → S → Prop) :
    actionPre (aggregateLift result) post onError = scalarCheckPre result post onError := by
  cases result <;> rfl

/-- The data operand of a raw-pointer aggregate must decode as a pointer.
The read's failure state and the subsequent decoding errors remain distinct. -/
@[miri_rvalue] theorem actionPre_canonical_readPointer (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (source : OpTy Provenance)
    (post : Pointer (Option Provenance) → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) :
    actionPre ((ExecutionMachine.aggregateHooks config limits).readPointer choice source) post onError =
      actionPre (PlaceMachine.readImmediate config.access source) (fun value =>
        scalarCheckPre (value.imm.toScalar.mapError ScalarOps.immediateError) (fun scalar =>
          scalarCheckPre (scalar.toPointer config.access.runtime.base |>.mapError ScalarOps.scalarError)
            post onError) onError) onError := by
  change actionPre (PlaceMachine.readImmediate config.access source >>= fun value =>
    aggregateLift (value.imm.toScalar.mapError ScalarOps.immediateError) >>= fun scalar =>
      aggregateLift (scalar.toPointer config.access.runtime.base |>.mapError ScalarOps.scalarError))
      post onError = _
  simp only [actionPre_bind_fun, aggregateLiftPre]

/-- Scalar metadata decoding is a pure check after the operand read has
committed its access effects. -/
@[miri_rvalue] theorem actionPre_canonical_readScalar (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (source : OpTy Provenance)
    (post : Scalar Provenance → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) :
    actionPre ((ExecutionMachine.aggregateHooks config limits).readScalar choice source) post onError =
      actionPre (PlaceMachine.readImmediate config.access source) (fun value =>
        scalarCheckPre (value.imm.toScalar.mapError ScalarOps.immediateError) post onError) onError := by
  change actionPre (PlaceMachine.readImmediate config.access source >>= fun value =>
    aggregateLift (value.imm.toScalar.mapError ScalarOps.immediateError)) post onError = _
  simp only [actionPre_bind_fun, aggregateLiftPre]

end Canonical

end Miri.Verification.AggregateWP

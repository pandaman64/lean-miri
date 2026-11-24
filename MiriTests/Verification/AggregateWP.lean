import Miri.Verification.ExactWP
import Miri.Verification.AggregateWP

namespace MiriTests.Verification.AggregateWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.Verification
open RvalueWP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U

private theorem actionPre_error {S A : Type} {action : RvalueM S A} {before failed : S}
    {error : StepError} (ran : action before = .error error failed) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre action post onError before = onError error failed := by
  simp only [actionPre, ran]

/-- Even a zero-length repeat must report a failed mutable-access check
with the state returned by that check. -/
theorem zero_repeat_failure (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (place : Miri.MIR.Place) (operand : Miri.MIR.Operand)
    (count : Miri.MIR.TypeConstId) (dest allocated : RuntimePlace Provenance)
    (source : OpTy Provenance) (before evaluatedDestination evaluatedSource forced failed : State)
    (stride : Size)
    (error : StepError) (post : State → Prop) (onError : StepError → State → Prop)
    (destinationOk : PlaceDynamic.evalPlace
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
      choice place true before = .ok dest evaluatedDestination)
    (operandOk : (ExecutionMachine.aggregateHooks config limits).evalOperand choice operand none
      evaluatedDestination = .ok source evaluatedSource)
    (sized : source.layout.layout.isSized = true)
    (allocationOk : (ExecutionMachine.aggregateHooks config limits).forceAllocation choice dest
      evaluatedSource = .ok allocated forced)
    (allocatedSized : allocated.layout.layout.isSized = true)
    (shape : allocated.layout.layout.fields = .Array stride 0)
    (accessFailed : (ExecutionMachine.aggregateHooks config limits).getPlaceAllocMut choice allocated
      forced = .error error failed) :
    evalPre (ExecutionMachine.rvalueHooks config limits) choice (.Repeat operand count) place
      post onError before = onError error failed := by
  simp only [miri_rvalue, actionPre_ok destinationOk, actionPre_ok operandOk, sized,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, actionPre_ok allocationOk,
    allocatedSized, shape, beq_self_eq_true, actionPre_error accessFailed]

/-- Construction of a two-field tuple threads the successful first write
into the failed second write. -/
theorem tuple_second_copy_failure (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (dest field0 field1 : RuntimePlace Provenance)
    (operand0 operand1 : Miri.MIR.Operand) (source0 source1 : OpTy Provenance)
    (before projected0 evaluated0 copied0 projected1 evaluated1 failed : State)
    (error : StepError) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (project0 : (ExecutionMachine.aggregateHooks config limits).projectField choice dest 0 before =
      .ok field0 projected0)
    (eval0 : (ExecutionMachine.aggregateHooks config limits).evalOperand choice operand0
      (some ((ExecutionMachine.aggregateHooks config limits).placeLayout field0)) projected0 =
      .ok source0 evaluated0)
    (copy0 : (ExecutionMachine.aggregateHooks config limits).copyOpNoValidate choice source0 field0
      false evaluated0 = .ok () copied0)
    (project1 : (ExecutionMachine.aggregateHooks config limits).projectField choice dest 1 copied0 =
      .ok field1 projected1)
    (eval1 : (ExecutionMachine.aggregateHooks config limits).evalOperand choice operand1
      (some ((ExecutionMachine.aggregateHooks config limits).placeLayout field1)) projected1 =
      .ok source1 evaluated1)
    (copy1 : (ExecutionMachine.aggregateHooks config limits).copyOpNoValidate choice source1 field1
      false evaluated1 = .error error failed) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).writeAggregate choice .Tuple
      #[operand0, operand1] dest) post onError before = onError error failed := by
  simp only [miri_rvalue, show (#[operand0, operand1] : Array Miri.MIR.Operand).size = 2 from rfl,
    show List.range' 0 2 = [0, 1] from rfl, show (#[operand0, operand1] : Array Miri.MIR.Operand)[0]? =
      some operand0 from rfl, show (#[operand0, operand1] : Array Miri.MIR.Operand)[1]? =
      some operand1 from rfl, Option.getD_none, Option.isSome_none, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, actionPre_ok project0, actionPre_ok eval0,
    actionPre_ok copy0, actionPre_ok project1, actionPre_ok eval1, actionPre_error copy1]

/-- Uninitialized data in a raw-pointer aggregate fails before the metadata
operand is evaluated, in the state left by the successful operand read. -/
theorem raw_pointer_uninitialized_data (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (pointee : Miri.MIR.TyId) (mutability : Miri.MIR.Mutability)
    (data metadata : Miri.MIR.Operand) (source : OpTy Provenance)
    (dest : RuntimePlace Provenance) (before evaluated readState : State)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (operandOk : (ExecutionMachine.aggregateHooks config limits).evalOperand choice data none
      before = .ok source evaluated)
    (readOk : PlaceMachine.readImmediate config.access source evaluated =
      .ok ⟨.uninit, source.layout⟩ readState) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).writeAggregate choice
      (.RawPtr pointee mutability) #[data, metadata] dest) post onError before =
      onError (.invalidProgram "uninitialized immediate reached scalar operator") readState := by
  simp only [miri_rvalue, show (#[data, metadata] : Array Miri.MIR.Operand).size = 2 from rfl,
    show (#[data, metadata] : Array Miri.MIR.Operand)[0]? = some data from rfl,
    show (#[data, metadata] : Array Miri.MIR.Operand)[1]? = some metadata from rfl,
    show ((2 : Nat) != 2) = false from rfl, Bool.false_eq_true, ↓reduceIte,
    actionPre_ok operandOk, actionPre_ok readOk] <;> rfl

/-- When the source aliases the first destination element, the continue
condition takes its bytes from that element in the post-copy state. -/
theorem aliased_repeat (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : Miri.MIR.Operand) (dest allocated : RuntimePlace Provenance)
    (memory : MemPlace Provenance) (layout : LocalLayout)
    (rest : Pointer (Option Provenance)) (length : UInt64)
    (before evaluated forced measured projected copied : State)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (operandOk : (ExecutionMachine.aggregateHooks config limits).evalOperand choice operand none
      before = .ok ⟨.indirect memory, layout⟩ evaluated)
    (sized : layout.layout.isSized = true)
    (allocationOk : (ExecutionMachine.aggregateHooks config limits).forceAllocation choice dest
      evaluated = .ok allocated forced)
    (lengthOk : (ExecutionMachine.aggregateHooks config limits).length choice allocated forced =
      .ok length measured)
    (positive : (length == 0) = false)
    (indexOk : (ExecutionMachine.aggregateHooks config limits).projectIndex choice allocated 0 measured =
      .ok ⟨.memory memory, layout⟩ projected)
    (copyOk : (ExecutionMachine.aggregateHooks config limits).copyOp choice
      ⟨.indirect memory, layout⟩ ⟨.memory memory, layout⟩ projected = .ok () copied)
    (offsetOk : aggregateWrappingOffset config.arithmetic memory.ptr layout.layout.size = .ok rest) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).writeRepeat choice operand dest)
      post onError before =
      actionPre (GlobalMemoryCopyMachine.genericCopy config.access config.addresses config.arithmetic
        memory.ptr rest layout.layout.size (length - 1) true) post onError copied := by
  have pointer : (ExecutionMachine.aggregateHooks config limits).placePointer
      ⟨.memory memory, layout⟩ = .ok memory.ptr := rfl
  have offset : (ExecutionMachine.aggregateHooks config limits).wrappingOffset memory.ptr
      ((ExecutionMachine.aggregateHooks config limits).placeLayout ⟨.memory memory, layout⟩).layout.size =
        .ok rest := offsetOk
  simp only [miri_rvalue, actionPre_ok operandOk, sized, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, actionPre_ok allocationOk, actionPre_ok lengthOk, positive, actionPre_ok indexOk,
    actionPre_ok copyOk, pointer, offset]
  rfl

end MiriTests.Verification.AggregateWP

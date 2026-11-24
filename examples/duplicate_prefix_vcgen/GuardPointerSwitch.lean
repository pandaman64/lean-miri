import PreparedArguments
import empty_function.FrameExit
import Lean

namespace DuplicatePrefix.PreparedArguments
open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
open EmptyFunction.FrameExit

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => ValidityMachine.State K U

open Lean Elab Tactic in
elab "unfold_operand_leaf " suffix:str : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".OperandMachine." ++ suffix.getString) then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one operand helper named {suffix.getString}"

/-- The real Move operand of the pointer-add switch reads its live cached
Boolean directly. The typed scalar read performs no memory access. -/
theorem readPointerAddGuard
    (config : ExecutionMachine.Config K (ValidityMachine.UserState U) C O X Host)
    (limits : ExecutionMachine.Limits)
    (access : ValidityMachine.Access K U) (accessEq : config.access = access)
    (choice : C) (older : Array F) (caller : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (layout : LocalLayout) (slot : LocalState Provenance LocalLayout)
    (atSlot : caller.locals[4]? = some slot)
    (cached : slot.layout = some layout)
    (stored : slot.value = .live (.immediate (.scalar (Scalar.fromBool false))))
    (sized : layout.layout.backendRepr.isUnsized = false)
    (debug : config.compiler.debugAssertions = false)
    (scope : config.compiler.validationInProgress = ValidityMachine.validationInProgress)
    (noClocks : caller.extra.dataRace = none)
    (primitive : isPrimitiveReadable layout.layout.backendRepr = true)
    (retain : access.retainTouched machine none = machine) :
    let before := withCurrent older caller machine
    (ExecutionMachine.terminatorHooks config limits).evalDiscriminant choice
      (.Move ⟨4, #[]⟩) before = (before, .ok ⟨.scalar (Scalar.fromBool false), layout⟩) := by
  intro before
  let checked := ExecutionMachine.withValidation config limits
  let operand := ExecutionMachine.operandHooks checked
  have layoutAt : caller.getLocal 4 = .ok slot := by
    have h := Array.getElem?_eq_some_iff.mp atSlot
    simp [Frame.getLocal, h.1, h.2, pure, Pure.pure, Except.pure]
  have valueAt : caller.getLocalOperand 4 = .ok (.immediate (.scalar (Scalar.fromBool false))) := by
    simp [Frame.getLocalOperand, layoutAt, stored, LocalState.access, bind, Bind.bind,
      Except.bind, Except.mapError]
  have validation : operand.compiler.validationInProgress = ValidityMachine.validationInProgress := scope
  have typeCheck : operand.checkPlaceType choice ⟨4, #[]⟩
      ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ before = .ok () before := by
    have flag : checked.compiler.debugAssertions = false := debug
    simp [operand, ExecutionMachine.operandHooks, flag, pure, Pure.pure, EStateM.pure]
  have readLocal : OperandMachine.localToOp operand choice 4 none before =
      .ok ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ before := by
    unfold OperandMachine.localToOp
    unfold_operand_leaf "stack"
    unfold_operand_leaf "lift"
    cases ghost : machine.user.payload.ghost <;>
      simp [MachineHooks.currentFrame, Stack.currentFrame?, withCurrent,
        validation, ValidityMachine.validationInProgress, MachineHooks.afterLocalRead, before, noClocks,
        layoutAt, valueAt, cached, sized, ghost, get, getThe, MonadStateOf.get, EStateM.get,
        bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure, Except.mapError]
  have readOperand : OperandMachine.evalOperand operand choice (.Move ⟨4, #[]⟩) none before =
      .ok ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ before := by
    simp [OperandMachine.evalOperand, OperandMachine.evalPlaceToOp, readLocal, typeCheck,
      bind, Bind.bind, pure, Pure.pure, EStateM.bind, EStateM.pure]
  have scalar := readBooleanImmediate access layout before false primitive
  simp only [before, withCurrent, retain] at scalar
  change PlaceMachine.readImmediate access
    ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ before =
      .ok ⟨.scalar (Scalar.fromBool false), layout⟩ before at scalar
  change MachineHooks.run (do
    let value ← OperandMachine.evalOperand operand choice (.Move ⟨4, #[]⟩) none
    PlaceMachine.readImmediate checked.access value) before = _
  have actualAccess : checked.access = access := accessEq
  simp only [MachineHooks.run, Call.run, bind, Bind.bind, EStateM.bind, readOperand, actualAccess]
  erw [scalar]

theorem pointerAddSelectOffsetPath
    (config : ExecutionMachine.Config K (ValidityMachine.UserState U) C O X Host)
    (limits : ExecutionMachine.Limits)
    (access : ValidityMachine.Access K U) (accessEq : config.access = access)
    (choice : C) (older : Array F) (caller : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (layout : LocalLayout) (slot : LocalState Provenance LocalLayout)
    (atSlot : caller.locals[4]? = some slot)
    (cached : slot.layout = some layout)
    (stored : slot.value = .live (.immediate (.scalar (Scalar.fromBool false))))
    (sized : layout.layout.backendRepr.isUnsized = false)
    (debug : config.compiler.debugAssertions = false)
    (scope : config.compiler.validationInProgress = ValidityMachine.validationInProgress)
    (noClocks : caller.extra.dataRace = none)
    (primitive : isPrimitiveReadable layout.layout.backendRepr = true)
    (retain : access.retainTouched machine none = machine)
    (width : layout.layout.size = Size.ofBytes 1)
    (classification : let before := withCurrent older caller machine
      ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify choice layout.ty).run
        before = .ok .boolean before)
    (boolLayout : let before := withCurrent older caller machine
      ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout choice).run
        before = .ok layout before) :
    let before := withCurrent older caller machine
    ControlFlow.evalSwitchInt (ExecutionMachine.terminatorHooks config limits) choice (.Move ⟨4, #[]⟩)
      ⟨#[.Case 0 5], 2⟩ before =
      (withCurrent older {caller with location := .mir ⟨5, 0⟩} machine, .ok ()) := by
  intro before
  have discr := readPointerAddGuard config limits access accessEq choice older caller machine layout slot
    atSlot cached stored sized debug scope noClocks primitive retain
  have jumped := pointerAddFalseJump config limits choice layout before before before before width discr
    classification boolLayout
  change ControlFlow.evalSwitchInt (ExecutionMachine.terminatorHooks config limits) choice (.Move ⟨4, #[]⟩)
    ⟨#[.Case 0 5], 2⟩ before = ControlFlow.goToBlock 5 before at jumped
  rw [jumped]
  simp [ControlFlow.goToBlock, ControlFlow.setLocation, before, withCurrent, Stack.currentFrame?]

end DuplicatePrefix.PreparedArguments

#print axioms DuplicatePrefix.PreparedArguments.readPointerAddGuard

#print axioms DuplicatePrefix.PreparedArguments.pointerAddSelectOffsetPath

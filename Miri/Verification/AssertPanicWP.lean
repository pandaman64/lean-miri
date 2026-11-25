import Miri.Verification.CanonicalStepWP

/-! Exact continuations for failed assertions and their internal Rust calls. -/
namespace Miri.Verification.AssertPanicWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Std.WP
open RvalueWP (actionPre actionPre_bind_fun actionPre_eq_wp)

variable {K U C O X Host P S E FnABI ArgABI : Type}
local notation "State" => MachineHooks.State K U
local notation "PanicHooks" => Panic.Hooks K U C O
local notation "Helpers" => FunctionCalls.Hooks P S C E O X FnABI ArgABI
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Errors" => StepError → State → Prop
local notation "Value" => RvalueImmTy Provenance

private def invalidGenericError : StepError :=
  .invalidProgram "Instance::mono called on type/const generic panic item"

private def genericArgsPre (post : Array GenericArg → S → Prop) (onError : StepError → S → Prop) :
    List MainGenericParameter → Array GenericArg → S → Prop
  | [], args, state => post args state
  | .lifetime :: rest, args, state => genericArgsPre post onError rest (args.push (.Lifetime .Erased)) state
  | _ :: _, _, state => onError invalidGenericError state

private theorem genericArgsPre_eq (params : List MainGenericParameter) (args : Array GenericArg)
    (post : Array GenericArg → S → Prop) (onError : StepError → S → Prop) :
    genericArgsPre post onError params args =
      actionPre (forIn params args (fun parameter current =>
        match parameter with
        | .lifetime => pure (.yield (current.push (.Lifetime .Erased)))
        | .typeParameter | .constParameter => do
          throw invalidGenericError
          pure (.yield current))) post onError := by
  induction params generalizing args with
  | nil => rfl
  | cons param rest ih =>
    cases param
    · simpa only [genericArgsPre, List.forIn_cons, pure_bind] using ih (args.push (.Lifetime .Erased))
    · rfl
    · rfl

/-- Resolve the language item and erase lifetime generics before invoking its
instance. Type and const generics fail in the state of the query. -/
def callPre (hooks : PanicHooks) (choice : C) (item : Panic.LangItem)
    (args : Array Value) (unwind : UnwindAction) (post : State → Prop) (onError : Errors) :
    State → Prop :=
  actionPre (hooks.langItem choice item) (fun
    | none => onError (.invalidProgram "missing panic language item")
    | some definition =>
      actionPre (hooks.genericParameters choice definition) (fun parameters =>
        genericArgsPre
          (fun generics => actionPre (hooks.itemInstance choice definition generics) (fun instanceId =>
            actionPre (hooks.driver.callFunction choice instanceId args (.goto none unwind))
              (fun _ => post) onError) onError) onError parameters.toList #[]) onError) onError

private def monoAction (hooks : PanicHooks) (choice : C) (item : Panic.LangItem) :
    MachineHooks.M K U CallInstance := do
  let some definition ← hooks.langItem choice item
    | throw (.invalidProgram "missing panic language item")
  let mut args := #[]
  for parameter in ← hooks.genericParameters choice definition do
    match parameter with
    | .lifetime => args := args.push (.Lifetime .Erased)
    | .typeParameter | .constParameter => throw invalidGenericError
  hooks.itemInstance choice definition args

private def callAction (hooks : PanicHooks) (choice : C) (item : Panic.LangItem)
    (args : Array Value) (unwind : UnwindAction) : MachineHooks.M K U Unit := do
  let instanceId ← monoAction hooks choice item
  hooks.driver.callFunction choice instanceId args (.goto none unwind)

private theorem callPre_eq (hooks : PanicHooks) (choice : C) (item : Panic.LangItem)
    (args : Array Value) (unwind : UnwindAction) (post : State → Prop) (onError : Errors) :
    callPre hooks choice item args unwind post onError =
      actionPre (callAction hooks choice item args unwind) (fun _ => post) onError := by
  simp only [callPre, callAction, monoAction, actionPre_bind_fun]
  congr 1
  funext definition
  cases definition
  · rfl
  · simp only [actionPre_bind_fun, ← Array.forIn_toList, genericArgsPre_eq]

private def diagnosticPre (hooks : PanicHooks) (choice : C) (operand : Operand)
    (post : Value → State → Prop) (onError : Errors) : State → Prop :=
  actionPre (hooks.evalOperand choice operand) (fun value =>
    actionPre (hooks.driver.readImmediate choice value) post onError) onError

private def ordinaryPre (hooks : PanicHooks) (choice : C) (message : AssertKind)
    (unwind : UnwindAction) (post : State → Prop) (onError : Errors) : State → Prop :=
  RvalueWP.scalarCheckPre (Panic.assertLangItem message)
    (fun item => callPre hooks choice item #[] unwind post onError) onError

/-- Bounds checks read index then length, and alignment checks read required
then found. Other assertions select a language item without diagnostic reads. -/
def panicPre (hooks : PanicHooks) (choice : C) (message : AssertKind)
    (unwind : UnwindAction) (post : State → Prop) (onError : Errors) : State → Prop :=
  let readPair first second item :=
    diagnosticPre hooks choice first (fun left =>
      diagnosticPre hooks choice second (fun right =>
        callPre hooks choice item #[left, right] unwind post onError) onError) onError
  match message with
  | .BoundsCheck len index => readPair index len .PanicBoundsCheck
  | .MisalignedPointerDereference required found => readPair required found .PanicMisalignedPointerDereference
  | _ => ordinaryPre hooks choice message unwind post onError

private theorem ordinaryPre_eq (hooks : PanicHooks) (choice : C) (message : AssertKind)
    (unwind : UnwindAction) (post : State → Prop) (onError : Errors) :
    ordinaryPre hooks choice message unwind post onError =
      actionPre (match Panic.assertLangItem message with
        | .ok item => pure item >>= fun selected => callAction hooks choice selected #[] unwind
        | .error error => throw error >>= fun selected => callAction hooks choice selected #[] unwind)
        (fun _ => post) onError := by
  unfold ordinaryPre RvalueWP.scalarCheckPre
  cases Panic.assertLangItem message
  · rfl
  · simp only [pure_bind, callPre_eq]

theorem actionPre_assertPanic (hooks : PanicHooks) (choice : C) (message : AssertKind)
    (unwind : UnwindAction) (post : State → Prop) (onError : Errors) :
    actionPre (Panic.assertPanic hooks choice message unwind) (fun _ => post) onError =
      panicPre hooks choice message unwind post onError := by
  cases message <;>
    simp only [Panic.assertPanic, panicPre, diagnosticPre, actionPre_bind_fun, callPre_eq] <;>
    first
    | rfl
    | rw [ordinaryPre_eq]
      split <;> simp_all only [] <;> rfl

/-- Load the MIR, construct the ZST destination and caller ABI, and enter the
ordinary frame initialization with the selected unwind action. -/
def internalCallPre (hooks : Helpers) (choice : C)
    (instanceId : CallInstance) (args : Array (RvalueImmTy P)) (continuation : ReturnContinuation)
    (post : S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  actionPre (hooks.loadMir choice instanceId) (fun body =>
    RvalueWP.scalarCheckPre (FunctionCalls.fakeAllocZst hooks.unitLayout) (fun dest =>
      actionPre (hooks.call.requiresCallerLocation instanceId) (fun location =>
        let inputs := args.map (fun arg => arg.layout.ty)
        let withInputs inputs := actionPre (hooks.fnAbiOfSignature choice
          ⟨inputs, dest.layout.ty, hooks.call.rustAbi, .Safe, false, false⟩) (fun abi =>
            CallWP.initStackFramePre hooks.call choice instanceId body abi
              (args.map (fun arg => FnArg.Copy ⟨.immediate arg.imm, arg.layout⟩)) location
              (.memory dest) continuation post onError) onError
        if location then actionPre hooks.callerLocationType
          (fun ty => withInputs (inputs.push ty)) onError
        else withInputs inputs) onError) onError) onError

theorem actionPre_internalCall (hooks : Helpers) (choice : C)
    (instanceId : CallInstance) (args : Array (RvalueImmTy P)) (continuation : ReturnContinuation)
    (post : S → Prop) (onError : StepError → S → Prop) :
    actionPre (FunctionCalls.callFunction hooks choice instanceId hooks.call.rustAbi
      args none continuation) (fun _ => post) onError =
      internalCallPre hooks choice instanceId args continuation post onError := by
  simp only [FunctionCalls.callFunction, internalCallPre, actionPre_bind_fun]
  congr 1
  funext body
  cases FunctionCalls.fakeAllocZst (P := P) hooks.unitLayout with
  | error => rfl
  | ok dest =>
    simp only [pure_bind, actionPre_bind_fun]
    congr 1
    funext location
    cases location <;>
      simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun,
        CallWP.initStackFramePre_eq_wp, ← actionPre_eq_wp]

section Canonical

variable [DecidableEq K]

/-- The same panic hooks installed by the canonical terminator machine. -/
def canonicalHooks (config : Config) (limits : ExecutionMachine.Limits) : PanicHooks :=
  let checked := ExecutionMachine.withValidation config limits
  let call := ExecutionMachine.callHooks checked limits
  { checked.panic with
    evalOperand := fun c op => OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) c op none
    driver := FunctionCalls.bindUnwind checked.panic.driver (ExecutionCalls.helpers checked.helpers call) }

theorem canonicalCallPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (instanceId : CallInstance) (args : Array Value) (continuation : ReturnContinuation)
    (post : State → Prop) (onError : Errors) :
    actionPre ((canonicalHooks config limits).driver.callFunction choice instanceId args continuation)
        (fun _ => post) onError =
      let checked := ExecutionMachine.withValidation config limits
      internalCallPre (ExecutionCalls.helpers checked.helpers (ExecutionMachine.callHooks checked limits))
        choice instanceId args continuation post onError :=
  actionPre_internalCall _ _ _ _ _ _ _

theorem wp_panic (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (message : AssertKind) (unwind : UnwindAction)
    (post : State → Prop) (onError : Errors) :
    wp (CanonicalStepWP.assertPanicEffect config limits choice message unwind) (fun _ => post) onError =
      panicPre (canonicalHooks config limits) choice message unwind post onError := by
  rw [← actionPre_eq_wp]
  exact actionPre_assertPanic _ _ _ _ _ _

/-- A matching or ignored assertion jumps after reading the condition.
A mismatch enters the exact panic precondition in the state left by the read. -/
theorem selectedAssert_eq (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (info : SourceInfo) (condition : Operand) (expected : Bool)
    (message : AssertKind) (target : BasicBlockId) (unwind : UnwindAction)
    (post : State → Prop) (onError : Errors) (before : State) :
    CanonicalStepWP.selectedTerminatorPre config limits choice
      ⟨info, .Assert condition expected message target unwind⟩ post onError before =
    let hooks := ExecutionMachine.terminatorHooks config limits
    let ignored := hooks.ignoreOptionalOverflowChecks before && ControlFlow.isOptionalOverflowCheck message
    wp (CanonicalStepWP.assertConditionEffect config limits choice condition) (fun actual after =>
      if ignored || expected == actual then InstructionWP.jumpPre target post onError after
      else panicPre (canonicalHooks config limits) choice message unwind post onError after)
      onError before := by
  simp only [CanonicalStepWP.selectedTerminatorPre, wp_panic]

/-- Resolve the unwind-termination lang item, then call it with the Rust ABI,
an empty argument list and an unreachable unwind continuation. -/
def unwindTerminatePre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (reason : UnwindTerminateReason) (post : State → Prop) (onError : Errors) :
    State → Prop :=
  let checked := ExecutionMachine.withValidation config limits
  let helpers := ExecutionCalls.helpers checked.helpers (ExecutionMachine.callHooks checked limits)
  actionPre (checked.unwindTerminateFunction choice reason) (fun callee =>
    internalCallPre helpers choice callee #[] (.goto none .Unreachable) post onError) onError

theorem selectedUnwindTerminate_eq (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (info : SourceInfo) (reason : UnwindTerminateReason)
    (post : State → Prop) (onError : Errors) (before : State) :
    CanonicalStepWP.selectedTerminatorPre config limits choice
      ⟨info, .UnwindTerminate reason⟩ post onError before =
        unwindTerminatePre config limits choice reason post onError before := by
  let checked := ExecutionMachine.withValidation config limits
  let helpers := ExecutionCalls.helpers checked.helpers (ExecutionMachine.callHooks checked limits)
  apply propext
  change InstructionWP.resultPre (fun _ => post) onError (runRvalue (do
    let callee ← checked.unwindTerminateFunction choice reason
    FunctionCalls.callFunction helpers choice callee helpers.call.rustAbi #[] none
      (.goto none .Unreachable)) before) ↔ _
  rw [← RvalueWP.actionPre_run]
  simp only [actionPre_bind_fun, actionPre_internalCall, unwindTerminatePre, checked, helpers]

end Canonical

macro "miri_assert_panic_wp" : tactic =>
  `(tactic| simp only [selectedAssert_eq, selectedUnwindTerminate_eq, unwindTerminatePre,
    wp_panic, panicPre, diagnosticPre, ordinaryPre, callPre,
    canonicalCallPre, internalCallPre, genericArgsPre])

end Miri.Verification.AssertPanicWP

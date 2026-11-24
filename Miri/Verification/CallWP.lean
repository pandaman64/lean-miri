import Miri.Verification.RvalueWP

/-! Exact continuations for call dispatch and tail-call frame replacement. -/
namespace Miri.Verification.CallWP

open Miri.Interpreter Miri.MIR Miri.Memory RvalueWP Std.WP

variable {P S C E Other Extern FnABI ArgABI : Type}
local notation "Hooks" => CallHooks P S C E Other Extern FnABI ArgABI
local notation "Request" => CallRequest P Other Extern FnABI
local notation "Evaluated" => EvaluatedCall P Other Extern FnABI
local notation "Errors" => StepError → S → Prop

/-- Check argument ABI before touching the destination. A successful copy of an
in-place argument still needs to protect the source allocation. -/
def passArgumentPre (hooks : Hooks) (choice : C) (caller : FnArg P) (callerAbi calleeAbi : ArgABI)
    (calleeIndex : Nat) (dest : Place) (calleeTy : TyId) (alreadyLive : Bool)
    (post : S → Prop) (onError : Errors) (before : S) : Prop :=
  if calleeTy != (hooks.argLayout calleeAbi).ty then
    onError (.invalidProgram "callee type does not match ABI") before
  else if caller.layout.layout != (hooks.argLayout callerAbi).layout then
    onError (.invalidProgram "caller layout does not match ABI") before
  else actionPre (hooks.checkArgumentCompat choice callerAbi calleeAbi) (fun compatible checked =>
    if !compatible then onError (.undefinedBehavior s!"AbiMismatchArgument {calleeIndex}") checked
    else
      let copied := caller.copyFnArg
      let write := actionPre (hooks.evalPlace choice dest false) (fun dest =>
        actionPre (hooks.copyAllowTransmute choice copied dest) (fun _ =>
          match caller with
          | .Copy _ => post
          | .InPlace place => actionPre (hooks.protectArgument choice place) (fun _ => post) onError)
          onError) onError
      if alreadyLive then write checked
      else if !dest.projection.isEmpty then
        onError (.invalidProgram "nonlocal destination in storage_live_dyn") checked
      else if copied.metadata.hasMeta && copied.layout.ty != calleeTy then
        onError (.invalidProgram "argument metadata type mismatch") checked
      else actionPre (hooks.storageLiveDyn choice dest.localId copied.metadata) (fun _ => write) onError checked)
    onError before

theorem passArgumentPre_eq_wp (hooks : Hooks) (choice : C) (caller : FnArg P)
    (callerAbi calleeAbi : ArgABI) (calleeIndex : Nat) (dest : Place) (calleeTy : TyId) (alreadyLive : Bool)
    (post : S → Prop) (onError : Errors) :
    passArgumentPre hooks choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive post onError =
      wp (Call.passArgument hooks choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive)
        (fun _ => post) onError := by
  rw [← actionPre_eq_wp]
  funext before
  simp only [passArgumentPre, Call.passArgument, Call.require_eq, actionPre_bind_fun,
    actionPre_ite]
  cases checkedTy : (calleeTy == (hooks.argLayout calleeAbi).ty) <;>
    simp only [bne, checkedTy, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> try rfl
  cases (caller.layout.layout == (hooks.argLayout callerAbi).layout) <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> try rfl
  simp only [actionPre_pure]
  congr 1
  funext compatible checked
  cases compatible <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> try rfl
  cases alreadyLive <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  · cases dest.projection.isEmpty <;> simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> try rfl
    by_cases metadata : caller.copyFnArg.metadata.hasMeta = true
    · by_cases ty : (caller.copyFnArg.layout.ty == calleeTy) = true
      · simp only [metadata, ty, Bool.not_true, Bool.and_false, Bool.false_or,
          Bool.false_eq_true, ↓reduceIte]
        cases caller <;> rfl
      · have mismatch : (caller.copyFnArg.layout.ty == calleeTy) = false := Bool.eq_false_iff.mpr ty
        simp only [metadata, mismatch, Bool.not_true, Bool.not_false, Bool.and_true,
          Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        rfl
    · have noMeta := Bool.eq_false_iff.mpr metadata
      simp only [noMeta, Bool.not_false, Bool.false_and, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
      cases caller <;> rfl
  · cases caller <;> rfl

@[spec high] theorem spec_passArgument (hooks : Hooks) (choice : C) (caller : FnArg P)
    (callerAbi calleeAbi : ArgABI) (calleeIndex : Nat) (dest : Place) (calleeTy : TyId) (alreadyLive : Bool)
    (post : Unit → S → Prop) (onError : Errors) :
    Triple (Call.passArgument hooks choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive)
      (passArgumentPre hooks choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive (post ()) onError)
      post onError := by
  apply Triple.iff.mpr
  intro before checked
  have wpPass := congrFun
    (passArgumentPre_eq_wp hooks choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive
      (post ()) onError) before
  rw [wpPass] at checked
  simp only [wp, WP.wpTrans] at checked ⊢
  cases ran : Call.passArgument hooks choice caller callerAbi calleeAbi calleeIndex dest calleeTy alreadyLive before with
  | error => simpa only [ran] using checked
  | ok value => cases value; simpa only [ran] using checked

/-- A successful dispatch can complete the call or provide a request for the
next dispatch at its updated state. A failed dispatch reports its own state. -/
def dispatchPre (hooks : Hooks) (choice : C) (post : S → Prop) (onError : Errors) :
    Nat → Request → S → Prop
  | 0, _, before => onError (.resourceExhaustion "call dispatch budget exhausted") before
  | budget + 1, request, before =>
    actionPre (Call.initFnCallStep hooks choice request) (fun
      | none => post
      | some next => dispatchPre hooks choice post onError budget next) onError before

theorem dispatchPre_eq_wp (hooks : Hooks) (choice : C) (budget : Nat) (request : Request)
    (post : S → Prop) (onError : Errors) :
    dispatchPre hooks choice post onError budget request =
      wp (Call.initFnCall hooks choice budget request) (fun _ => post) onError := by
  rw [← actionPre_eq_wp]
  induction budget generalizing request with
  | zero => rfl
  | succ budget ih =>
    funext before
    simp only [dispatchPre, Call.initFnCall, actionPre_bind]
    unfold actionPre
    cases ran : Call.initFnCallStep hooks choice request before with
    | error => rfl
    | ok next after =>
      cases next with
      | none => rfl
      | some next => exact congrFun (ih next) after

/-- Resolve an empty-argument direct call from the selected MIR operand and
compiler queries. The callee request carries the ABI returned by the compiler. -/
theorem evalNoArgsItem (hooks : Hooks) (choice : C) (func : Operand) (dest : Place)
    (before afterOperand afterSignature afterKind afterResolve afterInstance afterAbi ready : S)
    (operand : OpTy P) (abi : Extern) (definition : DefId) (genericArgs : Array GenericArg)
    (instanceId : CallInstance) (itemDef : DefId) (fnAbi : FnABI) (withCallerLocation : Bool)
    (read : hooks.evalOperand choice func before = .ok operand afterOperand)
    (signature : hooks.functionSignature choice operand.layout afterOperand = .ok (0, abi) afterSignature)
    (kind : hooks.functionKind operand.layout.ty afterSignature = .ok (.FnDef definition genericArgs) afterKind)
    (resolved : hooks.resolve choice definition genericArgs afterKind = .ok instanceId afterResolve)
    (item : hooks.instanceKind instanceId afterResolve = .ok (.Item itemDef) afterInstance)
    (computed : hooks.fnAbiOfInstance choice instanceId #[] afterInstance = .ok fnAbi afterAbi)
    (location : hooks.requiresCallerLocation instanceId afterAbi = .ok withCallerLocation ready) :
    Call.evalCalleeAndArgs hooks choice func #[] dest before =
      .ok ⟨.Instance instanceId, #[], abi, some fnAbi, withCallerLocation⟩ ready := by
  simp only [Call.evalCalleeAndArgs, Call.require_eq, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Array.size_empty, Nat.sub_self, Nat.zero_add, Nat.div_one,
    List.range'_zero, List.forIn_nil,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, read, signature, kind, resolved,
    item, computed, location, Nat.zero_le, decide_true, ↓reduceIte, Array.extract_empty, Array.map_empty]

/-- After source resolution of a non-RustCall item, the remaining WP is
callee frame initialization. The unwind action still respects the caller ABI. -/
theorem dispatchPre_item (hooks : Hooks) (choice : C) (remaining : Nat)
    (request : Request) (post : S → Prop) (onError : Errors)
    (before resolved ready : S) (fnInstance loadedInstance : CallInstance)
    (itemDef : DefId) (body : LoadedBody) (abi : FnABI)
    (callee : request.callee = .Instance fnInstance)
    (callerAbi : request.callerFnAbi = some abi)
    (kind : hooks.instanceKind fnInstance before = .ok (.Item itemDef) resolved)
    (ordinary : hooks.isRustCall request.callerAbi = false)
    (found : hooks.findMirOrEvalFn choice fnInstance abi request.args request.destination request.target
      (if hooks.abiCanUnwind abi then request.unwind else .Unreachable) resolved =
        .ok (some (body, loadedInstance)) ready) :
    dispatchPre hooks choice post onError (remaining + 1) request before =
      actionPre (Call.initStackFrame hooks choice loadedInstance body abi request.args request.withCallerLocation
        request.destination (.goto request.target
          (if hooks.abiCanUnwind abi then request.unwind else .Unreachable)))
        (fun _ => post) onError ready := by
  cases canUnwind : hooks.abiCanUnwind abi <;>
    simp only [canUnwind, Bool.false_eq_true, ↓reduceIte] at found ⊢
  all_goals
    simp only [dispatchPre, actionPre, Call.initFnCallStep, callee, callerAbi, Option.any_some, kind,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, canUnwind, found, ordinary,
      Bool.not_false, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  all_goals
    generalize Call.initStackFrame hooks choice loadedInstance body abi request.args request.withCallerLocation
      request.destination _ ready = outcome
    cases outcome <;> rfl

attribute [spec] Call.require_eq Call.initFnCallStep Call.initStackFrame

/-- Tail-call dispatch follows removal of the caller, and cleanup follows a
successful dispatch. The removed frame supplies both return and unwind targets. -/
def tailDispatchPre (hooks : Hooks) (choice : C) (budget : Nat)
    (evaluated : Evaluated) (post : S → Prop) (onError : Errors) (before : S) : Prop :=
  actionPre (hooks.popRaw choice) (fun frame afterPop =>
    match frame.returnContinuation with
    | .stop _ => onError (.invalidProgram "cannot tailcall as root of stack") afterPop
    | .goto target unwind =>
      let args := evaluated.args.map fun arg => FnArg.Copy arg.copyFnArg
      let request : Request := ⟨evaluated.callee, evaluated.callerAbi, evaluated.fnAbi, args,
        evaluated.withCallerLocation, frame.returnPlace, target, unwind⟩
      dispatchPre hooks choice (fun afterDispatch =>
        actionPre (hooks.cleanup choice false frame) (fun action afterCleanup =>
          if action == .normal then post afterCleanup
          else onError (.invalidProgram "tailcall cleanup must return Normal") afterCleanup)
          onError afterDispatch) onError budget request afterPop) onError before

theorem tailDispatchPre_eq_wp (hooks : Hooks) (choice : C) (budget : Nat)
    (evaluated : Evaluated) (post : S → Prop) (onError : Errors) :
    tailDispatchPre hooks choice budget evaluated post onError =
      wp (Call.initFnTailCall hooks choice budget evaluated) (fun _ => post) onError := by
  rw [← actionPre_eq_wp]
  funext before
  simp only [tailDispatchPre, Call.initFnTailCall, actionPre_bind_fun]
  cases ran : hooks.popRaw choice before with
  | error => simp only [actionPre, ran]
  | ok frame afterPop =>
    simp only [actionPre_ok ran]
    cases frame.returnContinuation with
    | stop => simp only [actionPre_bind_fun, actionPre_throw]
    | goto target unwind =>
      simp only [actionPre_bind_fun, actionPre_pure, dispatchPre_eq_wp, ← actionPre_eq_wp]
      congr 1
      funext value afterDispatch
      cases value
      congr 1
      funext action afterCleanup
      cases action <;> rfl

/-- Ordinary calls check their original location after dispatch, using the
state returned by each stack query. -/
def callPre (hooks : Hooks) (choice : C) (budget : Nat) (term : Terminator)
    (post : S → Prop) (onError : Errors) (before : S) : Prop :=
  match term.kind with
  | .Call func args dest target unwind .. =>
    actionPre hooks.frameIndex (fun oldIndex =>
      actionPre hooks.getFrame (fun oldFrame =>
        actionPre (hooks.evalPlace choice dest false) (fun destPlace =>
          actionPre (Call.evalCalleeAndArgs hooks choice func args dest) (fun evaluated =>
            let request : Request := ⟨evaluated.callee, evaluated.callerAbi, evaluated.fnAbi,
              evaluated.args, evaluated.withCallerLocation, destPlace, target,
              if evaluated.fnAbi.any hooks.abiCanUnwind then unwind else .Unreachable⟩
            dispatchPre hooks choice
              (actionPre hooks.stackIsEmpty (fun empty afterEmpty =>
                if empty then post afterEmpty
                else actionPre hooks.frameIndex (fun index afterIndex =>
                  if index == oldIndex then
                    actionPre hooks.getFrame (fun frame afterFrame =>
                      if frame.location == oldFrame.location then
                        onError (.invalidProgram "evaluating this call made no progress") afterFrame
                      else post afterFrame) onError afterIndex
                  else post afterIndex) onError afterEmpty) onError)
              onError budget request) onError) onError) onError) onError before
  | _ => onError (.invalidProgram "call hook received a non-Call terminator") before

theorem callPre_eq_wp (hooks : Hooks) (choice : C) (budget : Nat) (term : Terminator)
    (post : S → Prop) (onError : Errors) :
    callPre hooks choice budget term post onError =
      wp (Call.evalCallTerminator hooks choice budget term) (fun _ => post) onError := by
  rw [← actionPre_eq_wp]
  funext before
  rcases term with ⟨info, kind⟩
  cases kind <;> try rfl
  simp only [callPre, Call.evalCallTerminator, actionPre_bind_fun, dispatchPre_eq_wp, ← actionPre_eq_wp]
  congr 1
  funext oldIndex
  congr 1
  funext oldFrame
  congr 1
  funext destPlace
  congr 1
  funext evaluated
  congr 1
  funext value
  cases value
  congr 1
  funext empty state
  cases empty <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_pure]
  rw [actionPre_bind]
  congr 1
  funext index afterIndex
  split
  · rw [actionPre_bind]
    congr 1
    funext frame afterFrame
    split <;> rfl
  · rfl

/-- The frame-index check is performed after the caller's cleanup. -/
def tailCallPre (hooks : Hooks) (choice : C) (budget : Nat) (term : Terminator)
    (post : S → Prop) (onError : Errors) (before : S) : Prop :=
  match term.kind with
  | .TailCall func args _ =>
    actionPre hooks.frameIndex (fun oldIndex =>
      actionPre (Call.evalCalleeAndArgs hooks choice func args ⟨0, #[]⟩) (fun evaluated =>
        tailDispatchPre hooks choice budget evaluated
          (actionPre hooks.frameIndex (fun index after =>
            if index == oldIndex then post after
            else onError (.invalidProgram "evaluating this tail call pushed a new stack frame") after)
            onError) onError) onError) onError before
  | _ => onError (.invalidProgram "tailCall hook received a non-TailCall terminator") before

theorem tailCallPre_eq_wp (hooks : Hooks) (choice : C) (budget : Nat) (term : Terminator)
    (post : S → Prop) (onError : Errors) :
    tailCallPre hooks choice budget term post onError =
      wp (Call.evalTailCallTerminator hooks choice budget term) (fun _ => post) onError := by
  rw [← actionPre_eq_wp]
  funext before
  rcases term with ⟨info, kind⟩
  cases kind <;> try rfl
  simp only [tailCallPre, Call.evalTailCallTerminator, actionPre_bind_fun,
    tailDispatchPre_eq_wp, ← actionPre_eq_wp]
  congr 1
  funext oldIndex
  congr 1
  funext evaluated
  congr 1
  funext value
  cases value
  congr 1
  funext index after
  cases (index == oldIndex) <;> rfl

end Miri.Verification.CallWP

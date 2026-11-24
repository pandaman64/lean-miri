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

private theorem actionPre_pure_fun {A : Type} (value : A) (post : A → S → Prop) (onError : Errors) :
    actionPre (pure value) post onError = post value := rfl

private theorem actionPre_throw_fun {A : Type} (error : StepError) (post : A → S → Prop)
    (onError : Errors) : actionPre (throw error) post onError = onError error := rfl

/-- Select one ordinary argument in the same order as frame initialization. -/
def ordinaryArgumentPre (hooks : Hooks) (choice : C) (args : Array (FnArg P))
    (callerAbis calleeAbis : Array ArgABI) (callerIndex calleeIndex : Nat)
    (dest : Place) (ty : TyId) (post : S → Prop) (onError : Errors) : S → Prop :=
  match calleeAbis[calleeIndex]? with
  | none => onError (.invalidProgram "missing callee ABI")
  | some calleeAbi =>
    match args[callerIndex]? with
    | none => onError (.undefinedBehavior "calling a function with fewer arguments than it requires")
    | some arg =>
      match callerAbis[callerIndex]? with
      | none => onError (.invalidProgram "missing caller ABI")
      | some callerAbi =>
        passArgumentPre hooks choice arg callerAbi calleeAbi calleeIndex dest ty false post onError

theorem ordinaryArgumentPre_eq_wp (hooks : Hooks) (choice : C) (args : Array (FnArg P))
    (callerAbis calleeAbis : Array ArgABI) (callerIndex calleeIndex : Nat)
    (dest : Place) (ty : TyId) (post : S → Prop) (onError : Errors) :
    ordinaryArgumentPre hooks choice args callerAbis calleeAbis callerIndex calleeIndex dest ty post onError =
      wp (Call.initOrdinaryArgument hooks choice args callerAbis calleeAbis callerIndex calleeIndex dest ty)
        (fun _ => post) onError := by
  rw [← actionPre_eq_wp]
  cases callee : calleeAbis[calleeIndex]? <;>
    cases arg : args[callerIndex]? <;> cases caller : callerAbis[callerIndex]? <;>
    simp [ordinaryArgumentPre, Call.initOrdinaryArgument, Call.at?, callee, arg, caller,
      actionPre_bind_fun, actionPre_throw_fun, passArgumentPre_eq_wp, ← actionPre_eq_wp]

/-- The empty traversal still enters the scoped function-entry retag action. -/
theorem initFrameArguments_empty (hooks : Hooks) (choice : C) (body : Body) (nonCapturing : Bool)
    (vaListArg : Option LocalId) (args : Array (FnArg P)) (callerAbis calleeAbis : Array ArgABI)
    (count : body.argumentCount = 0) :
    Call.initFrameArguments hooks choice body nonCapturing vaListArg args callerAbis calleeAbis =
      hooks.withRetagMode choice .FnEntry (pure (0, 0)) := by
  simp [Call.initFrameArguments, Call.initFrameArgumentsBody, count]

/-- A single ordinary argument sets its span and queries its local layout
before checking the ABI/argument arrays. Both cursors advance after the copy. -/
theorem initFrameArguments_single (hooks : Hooks) (choice : C) (body : Body)
    (args : Array (FnArg P)) (callerAbis calleeAbis : Array ArgABI)
    (count : body.argumentCount = 1) (ordinary : body.spreadArgument ≠ some 1) :
    Call.initFrameArguments hooks choice body false none args callerAbis calleeAbis =
      hooks.withRetagMode choice .FnEntry (do
        let span ← hooks.localSpan body 1
        Call.setSpan hooks span
        let layout ← hooks.localLayout choice 1
        Call.initOrdinaryArgument hooks choice args callerAbis calleeAbis 0 0 ⟨1, #[]⟩ layout.ty
        pure (1, 1)) := by
  simp [Call.initFrameArguments, Call.initFrameArgumentsBody, Call.initFrameArgumentStep, count, ordinary, bind_assoc, -bind_pure_comp]

/-- Set the diagnostic span on the current frame before continuing. -/
def setSpanPre (hooks : Hooks) (span : SpanRef) (post : S → Prop) (onError : Errors) : S → Prop :=
  actionPre hooks.getFrame (fun frame =>
    actionPre (hooks.setFrame { frame with location := .unwinding span }) (fun _ => post) onError) onError

theorem setSpanPre_eq_actionPre (hooks : Hooks) (span : SpanRef)
    (post : S → Prop) (onError : Errors) :
    setSpanPre hooks span post onError = actionPre (Call.setSpan hooks span) (fun _ => post) onError := by
  simp only [setSpanPre, Call.setSpan, actionPre_bind_fun]

/-- Compose successful argument initialization with the next local. On error
the traversal reports the state returned by the failing argument action. -/
def ordinaryArgumentsPre (hooks : Hooks) (choice : C) (body : Body) (args : Array (FnArg P))
    (callerAbis calleeAbis : Array ArgABI) (post : (Nat × Nat) → S → Prop) (onError : Errors) :
    List Nat → (Nat × Nat) → S → Prop
  | [], indices => post indices
  | zeroIndex :: rest, indices =>
    let localId := zeroIndex + 1
    actionPre (hooks.localSpan body localId) (fun span =>
      setSpanPre hooks span
        (actionPre (hooks.localLayout choice localId) (fun layout =>
          ordinaryArgumentPre hooks choice args callerAbis calleeAbis indices.1 indices.2
            ⟨localId, #[]⟩ layout.ty
            (ordinaryArgumentsPre hooks choice body args callerAbis calleeAbis post onError rest
              (indices.1 + 1, indices.2 + 1)) onError) onError) onError) onError

theorem ordinaryArgumentsPre_eq_actionPre (hooks : Hooks) (choice : C) (body : Body)
    (args : Array (FnArg P)) (callerAbis calleeAbis : Array ArgABI)
    (post : (Nat × Nat) → S → Prop) (onError : Errors) (locals : List Nat) (indices : Nat × Nat)
    (ordinary : body.spreadArgument = none) :
    ordinaryArgumentsPre hooks choice body args callerAbis calleeAbis post onError locals indices =
      actionPre (forIn locals indices
        (Call.initFrameArgumentStep hooks choice body false none args callerAbis calleeAbis)) post onError := by
  induction locals generalizing indices with
  | nil => rfl
  | cons localId rest ih =>
    rw [List.forIn_cons]
    simp [ordinaryArgumentsPre, Call.initFrameArgumentStep, ordinary, actionPre_bind_fun,
      actionPre_pure_fun, setSpanPre_eq_actionPre, ordinaryArgumentPre_eq_wp, ← actionPre_eq_wp,
      map_eq_pure_bind, -bind_pure_comp]
    congr 1
    funext span
    congr 1
    funext completed
    congr 1
    funext layout
    congr 1
    funext completed
    exact ih _

/-- Pull back both continuations through a list of argument initialization
steps. Each step supplies the next pair of ABI cursors. -/
def frameArgumentsFoldPre
    (step : Nat → (Nat × Nat) → CallM S (ForInStep (Nat × Nat)))
    (post : (Nat × Nat) → S → Prop) (onError : Errors) :
    List Nat → (Nat × Nat) → S → Prop
  | [], indices => post indices
  | zeroIndex :: rest, indices =>
    actionPre (step zeroIndex indices) (fun
      | .done next => post next
      | .yield next => frameArgumentsFoldPre step post onError rest next) onError

private theorem frameArgumentsFoldPre_eq_actionPre
    (step : Nat → (Nat × Nat) → CallM S (ForInStep (Nat × Nat)))
    (post : (Nat × Nat) → S → Prop) (onError : Errors)
    (locals : List Nat) (indices : Nat × Nat) :
    frameArgumentsFoldPre step post onError locals indices =
      actionPre (forIn locals indices step) post onError := by
  induction locals generalizing indices with
  | nil => rfl
  | cons zeroIndex rest ih =>
    simp only [frameArgumentsFoldPre, List.forIn_cons, actionPre_bind_fun]
    congr 1
    funext result
    cases result with
    | done => rfl
    | yield next => exact ih next

/-- The traversal's actual argument step handles ordinary, closure self,
variadic, and spread locals. This equation exposes the full iteration
independently of which argument arm each local selects. -/
theorem frameArgumentsBodyPre_eq_actionPre (hooks : Hooks) (choice : C) (body : Body)
    (nonCapturing : Bool) (vaListArg : Option LocalId) (args : Array (FnArg P))
    (callerAbis calleeAbis : Array ArgABI) (post : (Nat × Nat) → S → Prop) (onError : Errors) :
    frameArgumentsFoldPre
      (Call.initFrameArgumentStep hooks choice body nonCapturing vaListArg args callerAbis calleeAbis)
      post onError (List.range' 0 body.argumentCount) (0, 0) =
    actionPre (Call.initFrameArgumentsBody hooks choice body nonCapturing vaListArg args callerAbis calleeAbis)
      post onError := by
  rw [frameArgumentsFoldPre_eq_actionPre]
  have noChange : (fun indices : Nat × Nat => (pure (indices.1, indices.2) : CallM S (Nat × Nat))) =
      pure := by
    funext indices
    cases indices
    rfl
  simp [Call.initFrameArgumentsBody, noChange, -bind_pure_comp]

/-- The canonical call hook exposes the retag restoration continuations for
every argument traversal, including closure self, variadic, and spread locals. -/
theorem canonicalFrameArgumentsPre {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (body : Body) (nonCapturing : Bool) (vaListArg : Option LocalId)
    (args : Array (FnArg Provenance)) (callerAbis calleeAbis : Array (Miri.ABI.ArgAbi TyId))
    (post : (Nat × Nat) → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) :
    let hooks := ExecutionMachine.callHooks config limits
    actionPre (Call.initFrameArguments hooks choice body nonCapturing vaListArg args callerAbis calleeAbis)
      post onError =
    retagModePre .FnEntry
      (Call.initFrameArgumentsBody hooks choice body nonCapturing vaListArg args callerAbis calleeAbis)
      post onError := by
  funext before
  apply actionPre_withRetagMode

/-- Complete the frame after argument initialization. Return ABI rejection
precedes protection of an indirect return place and restoration of the preamble span. -/
def finishFramePre (hooks : Hooks) (choice : C) (body : Body) (callerFnAbi calleeFnAbi : FnABI)
    (args : Array (FnArg P)) (requiresLocation : Bool) (calleeAbis : Array ArgABI)
    (destination : OpTy P) (preamble : SpanRef) (indices : Nat × Nat)
    (post : S → Prop) (onError : Errors) : S → Prop :=
  let finish := setSpanPre hooks preamble (fun restored =>
    if requiresLocation && calleeAbis[indices.2]?.isNone then
      onError (.invalidProgram "missing implicit caller location ABI") restored
    else if indices.2 + (if requiresLocation then 1 else 0) != calleeAbis.size then
      onError (.invalidProgram "mismatch between callee ABI and callee body arguments") restored
    else if indices.1 < args.size then
      onError (.undefinedBehavior "calling a function with more arguments than it expected") restored
    else actionPre (hooks.afterFrameInit choice) (fun _ =>
      actionPre (hooks.pushDone choice) (fun _ => post) onError) onError restored) onError
  actionPre (hooks.localSpan body 0) (fun span =>
    setSpanPre hooks span
      (actionPre (hooks.checkArgumentCompat choice (hooks.abiReturn callerFnAbi)
        (hooks.abiReturn calleeFnAbi)) (fun compatible checked =>
          if compatible then
            match destination.op with
            | .immediate _ => finish checked
            | .indirect place => actionPre (hooks.protectArgument choice ⟨place, destination.layout⟩)
                (fun _ => finish) onError checked
          else onError (.undefinedBehavior "AbiMismatchReturn") checked) onError) onError) onError

theorem finishFramePre_eq_actionPre (hooks : Hooks) (choice : C) (body : Body)
    (callerFnAbi calleeFnAbi : FnABI) (args : Array (FnArg P)) (requiresLocation : Bool)
    (calleeAbis : Array ArgABI) (destination : OpTy P) (preamble : SpanRef) (indices : Nat × Nat)
    (post : S → Prop) (onError : Errors) :
    finishFramePre hooks choice body callerFnAbi calleeFnAbi args requiresLocation calleeAbis
      destination preamble indices post onError =
    actionPre (Call.finishFrameInit hooks choice body callerFnAbi calleeFnAbi args requiresLocation
      calleeAbis destination preamble indices) (fun _ => post) onError := by
  rcases indices with ⟨callerIndex, calleeIndex⟩
  simp only [finishFramePre, Call.finishFrameInit, setSpanPre_eq_actionPre, actionPre_bind_fun,
    actionPre_ite, actionPre_pure_fun, actionPre_throw_fun, Call.require_eq]
  congr 1
  funext span
  congr 1
  funext completed
  cases completed
  congr 1
  funext compatible checked
  cases compatible <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    try rfl
  cases destination.op <;>
    simp only [actionPre_bind_fun, actionPre_ite, actionPre_pure_fun, actionPre_throw_fun, Call.require_eq]
  all_goals
    repeat' (first | congr 1; funext _ | rfl)
  all_goals
    cases requiresLocation <;> cases implicitArg : calleeAbis[calleeIndex]? <;>
      simp [implicitArg, Call.at?, actionPre_pure_fun, actionPre_throw_fun] <;>
      split <;> (first | rfl | split <;> rfl)

/-- Frame preflight, raw push, argument initialization, and frame completion.
The traversal retains its scoped retag action, including the state it returns on failure. -/
def initStackFramePre (hooks : Hooks) (choice : C) (fnInstance : CallInstance) (loadedBody : LoadedBody)
    (callerFnAbi : FnABI) (args : Array (FnArg P)) (withCallerLocation : Bool)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation)
    (post : S → Prop) (onError : Errors) : S → Prop :=
  let enter (requiresLocation : Bool) (callerLocation : Option SpanRef) :=
    actionPre (hooks.fnAbiOfInstance choice fnInstance #[]) (fun calleeFnAbi computed =>
      if !hooks.sameConvention callerFnAbi calleeFnAbi then
        onError (.undefinedBehavior "caller/callee calling convention mismatch") computed
      else if hooks.abiVariadic callerFnAbi != hooks.abiVariadic calleeFnAbi then
        onError (.undefinedBehavior "CVariadicMismatch") computed
      else if hooks.abiVariadic callerFnAbi && hooks.abiFixedCount callerFnAbi != hooks.abiFixedCount calleeFnAbi then
        onError (.undefinedBehavior "CVariadicFixedCountMismatch") computed
      else
        let cont := if hooks.abiCanUnwind calleeFnAbi then cont else
          match cont with
          | .stop _ => cont
          | .goto ret _ => .goto ret .Unreachable
        let body := loadedBody.body
        let callerAbis := hooks.abiArgs callerFnAbi
        let calleeAbis := hooks.abiArgs calleeFnAbi
        let vaListArg := if hooks.abiVariadic calleeFnAbi then some body.argumentCount else none
        actionPre (hooks.checkTargetFeatures choice fnInstance) (fun _ =>
          actionPre (hooks.placeToOp choice destination) (fun destinationOp =>
            actionPre (hooks.pushRaw choice fnInstance loadedBody destination cont) (fun _ =>
              actionPre hooks.getFrame (fun frame afterFrame =>
                match frame.location with
                | .mir _ => onError (.invalidProgram "raw frame does not have preamble location") afterFrame
                | .unwinding preamble =>
                  actionPre (hooks.setFrame { frame with trackCallerArg := callerLocation }) (fun _ =>
                    actionPre (hooks.nonCapturingClosure choice fnInstance calleeFnAbi) (fun nonCapturing afterClosure =>
                      if args.size + (if withCallerLocation then 1 else 0) != callerAbis.size then
                        onError (.invalidProgram "mismatch between caller ABI and arguments") afterClosure
                      else actionPre (Call.initFrameArguments hooks choice body nonCapturing vaListArg
                        args callerAbis calleeAbis)
                        (fun indices => finishFramePre hooks choice body callerFnAbi calleeFnAbi args
                          requiresLocation calleeAbis destinationOp preamble indices post onError)
                        onError afterClosure) onError) onError afterFrame) onError) onError) onError) onError
          computed) onError
  actionPre (hooks.requiresCallerLocation fnInstance) (fun requiresLocation queried =>
    if requiresLocation != withCallerLocation then
      onError (.undefinedBehavior "caller/callee #[track_caller] mismatch") queried
    else if withCallerLocation then
      actionPre hooks.callerLocation (fun span => enter requiresLocation (some span)) onError queried
    else enter requiresLocation none queried) onError

theorem initStackFramePre_eq_wp (hooks : Hooks) (choice : C) (fnInstance : CallInstance)
    (loadedBody : LoadedBody) (callerFnAbi : FnABI) (args : Array (FnArg P)) (withCallerLocation : Bool)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation)
    (post : S → Prop) (onError : Errors) :
    initStackFramePre hooks choice fnInstance loadedBody callerFnAbi args withCallerLocation destination cont
      post onError =
    wp (Call.initStackFrame hooks choice fnInstance loadedBody callerFnAbi args withCallerLocation
      destination cont) (fun _ => post) onError := by
  rw [← actionPre_eq_wp]
  simp only [initStackFramePre, Call.initStackFrame, actionPre_bind_fun, actionPre_ite,
    actionPre_pure_fun, actionPre_throw_fun, Call.require_eq, finishFramePre_eq_actionPre]
  congr 1
  funext required queried
  cases required <;> cases withCallerLocation <;>
    simp only [bne, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, Bool.not_false, ↓reduceIte,
      actionPre_bind_fun, actionPre_pure_fun, actionPre_throw_fun] <;> try rfl
  case' true.true =>
    congr 1
    funext span
  all_goals
    congr 1
    funext abi computed
    cases convention : hooks.sameConvention callerFnAbi abi <;>
      simp only [convention, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    all_goals
      cases variadic : (hooks.abiVariadic callerFnAbi == hooks.abiVariadic abi) <;>
        simp only [variadic, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split <;> try rfl
      congr 1
      funext features
      congr 1
      funext destOp
      congr 1
      funext pushed
      congr 1
      funext frame afterFrame
      cases frame.location <;> simp only [actionPre_bind_fun, actionPre_ite, actionPre_pure_fun,
        actionPre_throw_fun]
      congr 1
      funext tracked
      congr 1
      funext nonCapturing afterClosure
      cases arity : (_ == (hooks.abiArgs callerFnAbi).size) <;>
        simp only [arity, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[spec high] theorem spec_initStackFrame (hooks : Hooks) (choice : C) (fnInstance : CallInstance)
    (loadedBody : LoadedBody) (callerFnAbi : FnABI) (args : Array (FnArg P)) (withCallerLocation : Bool)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation)
    (post : Unit → S → Prop) (onError : Errors) :
    Triple (Call.initStackFrame hooks choice fnInstance loadedBody callerFnAbi args withCallerLocation
      destination cont)
      (initStackFramePre hooks choice fnInstance loadedBody callerFnAbi args withCallerLocation
        destination cont (post ()) onError) post onError := by
  apply Triple.iff.mpr
  intro before checked
  rw [initStackFramePre_eq_wp] at checked
  rw [show (fun _ : Unit => post ()) = post from by funext value; cases value; rfl] at checked
  exact checked

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

attribute [spec] Call.require_eq Call.initFnCallStep

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

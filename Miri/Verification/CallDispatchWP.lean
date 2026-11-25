import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.DeadlineMachine
import Miri.Verification.CallWP

/-! Exact continuations for concrete call routing. Compiler queries and the
configured foreign scope enter at their actual intermediate states. -/
namespace Miri.Verification.CallDispatchWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR RvalueWP Std.WP

variable {S C D MD Ptr B I Other K U E P : Type}
local notation "Errors" => StepError → S → Prop

private theorem purePre {A : Type} (value : A) (post : A → S → Prop) (onError : Errors) :
    actionPre (pure value) post onError = post value := rfl

private theorem errorPre {A : Type} (error : StepError) (post : A → S → Prop) (onError : Errors) :
    actionPre (throw error) post onError = onError error := rfl

/-- The shim's disposition selects the return or unwind action. A body resolved
by symbol lookup returns to the ordinary MIR dispatch continuation. -/
def foreignPre (h : ForeignItems.Hooks P S D MD Ptr B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : D) (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Option (B × I) → S → Prop) (onError : Errors) : S → Prop :=
  actionPre (h.allocatorSymbol name) (fun
    | some (.redirect symbol) => actionPre (h.lookupFunction symbol) (fun
      | some handler => post (some handler)
      | none => onError (.invalidProgram "missing alloc error handler symbol")) onError
    | some (.special method) =>
      actionPre (ForeignItems.specialAllocator h method name abi args dest) (fun _ =>
        actionPre (h.returnToBlock ret) (fun _ => post none) onError) onError
    | none => actionPre (h.forceAllocation dest) (fun allocated =>
      actionPre (ForeignItems.inner h name abi args allocated) (fun
        | .NeedsReturn => actionPre (h.returnToBlock ret) (fun _ => post none) onError
        | .NeedsUnwind => actionPre (h.unwindToBlock unwind) (fun _ => post none) onError
        | .AlreadyJumped => post none
        | .NotSupported => actionPre (h.lookupFunction name) (fun
          | some body => post (some body)
          | none => onError (.machineStop s!"can't call foreign function `{name}` on OS `{h.os}`")) onError)
        onError) onError) onError

theorem foreignPre_eq_wp (h : ForeignItems.Hooks P S D MD Ptr B I) (name : String)
    (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : D) (ret : Option BasicBlockId)
    (unwind : UnwindAction) (post : Option (B × I) → S → Prop) (onError : Errors) :
    foreignPre h name abi args dest ret unwind post onError =
      wp (ForeignItems.emulate h name abi args dest ret unwind) post onError := by
  rw [← actionPre_eq_wp]
  simp only [foreignPre, ForeignItems.emulate, actionPre_bind_fun]
  congr 1
  funext allocator
  cases allocator with
  | some allocator =>
    cases allocator <;> simp only [actionPre_bind_fun, purePre]
    congr 1
    funext handler
    cases handler <;> rfl
  | none =>
    simp only [actionPre_bind_fun]
    congr 1
    funext destination
    congr 1
    funext result
    cases result <;> simp only [actionPre_bind_fun, purePre]
    congr 1
    funext body
    cases body <;> rfl

/-- A dynamic symbol must finish inside its shim. An attempted MIR delegation
reports an error at the state returned by the foreign dispatch. -/
theorem dynSymPre_eq_wp (h : ForeignItems.Hooks P S D MD Ptr B I) (name : String)
    (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : D) (ret : Option BasicBlockId)
    (unwind : UnwindAction) (post : Unit → S → Prop) (onError : Errors) :
    foreignPre h name abi args dest ret unwind (fun
      | none => post ()
      | some _ => onError (.invalidProgram "DynSyms that delegate are not supported")) onError =
      wp (ForeignItems.emulateDynSym h name abi args dest ret unwind) post onError := by
  rw [foreignPre_eq_wp, ← actionPre_eq_wp, ← actionPre_eq_wp]
  simp only [ForeignItems.emulateDynSym, actionPre_bind_fun]
  congr 1
  funext body
  cases body <;> rfl

/-- Body lookup checks the backend after the foreign classification query.
Foreign calls enter the configured scope only after resolving the symbol. -/
def findMirPre (h : CallDispatchMachine.Hooks S C Other) (choice : C) (callee : CallInstance)
    (abi : FnAbi TyId) (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop) (onError : Errors) : S → Prop :=
  actionPre (h.isForeignItem callee) (fun foreign classified =>
    if foreign then actionPre (h.symbolName callee) (fun name =>
      match h.foreign with
      | none => onError (.unsupported s!"foreign call requires complete source platform input: {name}")
      | some setup => actionPre (h.foreignScope do
          let hooks ← setup
          ForeignItems.emulate hooks name abi (args.map FnArg.copyFnArg)
            destination.toRuntimePlace ret unwind) post onError) onError classified
    else match h.backend.selection classified with
      | .ok _ => actionPre (h.loadMir choice callee) (fun body => post (some (body, callee))) onError classified
      | .error error => onError error classified) onError

theorem findMirPre_eq_wp (h : CallDispatchMachine.Hooks S C Other) (choice : C) (callee : CallInstance)
    (abi : FnAbi TyId) (args : Array (FnArg Provenance)) (destination : RuntimeStackPlace Provenance)
    (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Option (LoadedBody × CallInstance) → S → Prop) (onError : Errors) :
    findMirPre h choice callee abi args destination ret unwind post onError =
      wp (CallDispatchMachine.findMirOrEvalFn h choice callee abi args destination ret unwind) post onError := by
  rw [← actionPre_eq_wp]
  simp only [findMirPre, CallDispatchMachine.findMirOrEvalFn, actionPre_bind_fun]
  congr 1
  funext foreign classified
  cases foreign
  · simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind]
    have getResult : (get : EStateM StepError S S) classified = .ok classified classified := rfl
    rw [actionPre_ok getResult]
    cases h.backend.selection classified <;>
      simp only [actionPre_bind_fun, purePre, errorPre]
  · simp only [↓reduceIte, actionPre_bind_fun]
    congr 1
    funext name
    cases h.foreign <;> simp only [errorPre, actionPre_bind_fun]

/-- Pointer lookup rejects a nonzero allocation offset before consulting the
function registry. The registry can return either kind of callable value. -/
def getPtrFnPre (h : FunctionPointers.Hooks K U Other) (pointer : Pointer (Option Provenance))
    (post : FnVal Other → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) : MachineHooks.State K U → Prop :=
  actionPre (FunctionPointers.allocation h pointer) (fun (id, offset) resolved =>
    if offset != .ZERO then onError (.undefinedBehavior "InvalidFunctionPointer") resolved
    else actionPre (FunctionPointers.getFnAlloc h id) (fun
      | some value => post value
      | none => onError (.undefinedBehavior "InvalidFunctionPointer")) onError resolved) onError

theorem getPtrFnPre_eq_wp (h : FunctionPointers.Hooks K U Other)
    (pointer : Pointer (Option Provenance)) (post : FnVal Other → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) :
    getPtrFnPre h pointer post onError = wp (FunctionPointers.getPtrFn h pointer) post onError := by
  rw [← actionPre_eq_wp]
  simp only [getPtrFnPre, FunctionPointers.getPtrFn, actionPre_bind_fun]
  congr 1
  funext result resolved
  obtain ⟨id, offset⟩ := result
  by_cases guard : (offset != Size.ZERO) = true <;>
    simp only [guard, Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun, actionPre_throw]
  congr 1
  funext result
  cases result <;> rfl

/-- Deadline suppression is entered before the action. Its exit can replace
a success with a deadline error, while an action error retains its own error
even if leaving suppression also fails. -/
theorem actionPre_pruneSuppressed {Host System A : Type}
    (registry : U → DeadlineMachine.Registry Host System)
    (setRegistry : DeadlineMachine.Registry Host System → U → U)
    (action : MachineHooks.M K U A) (post : A → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) :
    actionPre (DeadlineMachine.withPruneSuppressed registry setRegistry action) post onError before =
      let entered := { before with machine := { before.machine with
        user := setRegistry (registry before.machine.user).enterPruneSuppression before.machine.user } }
      actionPre action (fun value after =>
        let current := registry after.machine.user
        let live := if current.pruneDepth == 1 then DeadlineMachine.liveTokens after.machine.threads else {}
        match current.leavePruneSuppression live with
        | .ok updated => post value { after with machine := { after.machine with
            user := setRegistry updated after.machine.user } }
        | .error error => onError error after) (fun error after =>
          match (registry after.machine.user).leavePruneSuppressionOnError with
          | .ok updated => onError error { after with machine := { after.machine with
              user := setRegistry updated after.machine.user } }
          | .error _ => onError error after) entered := by
  simp only [actionPre, DeadlineMachine.withPruneSuppressed, EStateM.run, Id.run,
    pure, Pure.pure]
  let entered := { before with machine := { before.machine with
    user := setRegistry (registry before.machine.user).enterPruneSuppression before.machine.user } }
  cases action entered with
  | ok value after =>
    dsimp only
    cases (registry after.machine.user).leavePruneSuppression
      (if (registry after.machine.user).pruneDepth == 1 then DeadlineMachine.liveTokens after.machine.threads else {}) <;> rfl
  | error error after =>
    dsimp only
    cases (registry after.machine.user).leavePruneSuppressionOnError <;> rfl

/-- Setup is inside the scope. This equation is the continuation used by the
identity scope and by the deadline scope once its continuations are installed. -/
theorem actionPre_foreignSetup
    (setup : EStateM StepError S (ForeignItems.Hooks P S D MD Ptr B I))
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : D)
    (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Option (B × I) → S → Prop) (onError : Errors) :
    actionPre (do ForeignItems.emulate (← setup) name abi args dest ret unwind) post onError =
      actionPre setup (fun h => foreignPre h name abi args dest ret unwind post onError) onError := by
  simp only [foreignPre_eq_wp, ← actionPre_eq_wp, actionPre_bind_fun]

theorem actionPre_dynSymSetup
    (setup : EStateM StepError S (ForeignItems.Hooks P S D MD Ptr B I))
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : D)
    (ret : Option BasicBlockId) (unwind : UnwindAction) (post : Unit → S → Prop) (onError : Errors) :
    actionPre (do ForeignItems.emulateDynSym (← setup) name abi args dest ret unwind) post onError =
      actionPre setup (fun h => foreignPre h name abi args dest ret unwind (fun
        | none => post ()
        | some _ => onError (.invalidProgram "DynSyms that delegate are not supported")) onError) onError := by
  simp only [dynSymPre_eq_wp, ← actionPre_eq_wp, actionPre_bind_fun]

/-- Dynamic extra calls have their own missing-platform error and use the
same scoped setup as foreign items. -/
theorem callExtraPre_eq_wp (h : CallDispatchMachine.Hooks S C Other) (choice : C)
    (symbol : Other) (abi : FnAbi TyId) (args : Array (FnArg Provenance))
    (destination : RuntimeStackPlace Provenance) (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Unit → S → Prop) (onError : Errors) :
    (match h.foreign with
    | none => onError (.unsupported "dynamic foreign call requires complete source platform input")
    | some setup => actionPre (h.foreignScope do
        let hooks ← setup
        ForeignItems.emulateDynSym hooks (h.dynSymName symbol) abi
          (args.map FnArg.copyFnArg) destination.toRuntimePlace ret unwind) post onError) =
      wp (CallDispatchMachine.callExtra h choice symbol abi args destination ret unwind) post onError := by
  cases setup : h.foreign <;> simp only [CallDispatchMachine.callExtra, setup, ← actionPre_eq_wp, errorPre]

/-- Backend selection is checked on atomic names before evaluation. Ordinary
intrinsics never consult this gate. -/
theorem intrinsicBackendPre_eq_wp (backend : IntrinsicBackend.Dispatcher S C D)
    (h : IntrinsicHooks Provenance S C D) (choice : C) (name : String) (types : Array TyId)
    (args : Array (OpTy Provenance)) (dest : D) (ret : Option BasicBlockId)
    (post : Bool → S → Prop) (onError : Errors) :
    (fun before => if name.startsWith "atomic_" then
      match backend.selection before with
      | .ok _ => actionPre (IntrinsicAtomic.eval h.atomicHooks choice name args dest ret) post onError before
      | .error error => onError error before
    else actionPre (Intrinsics.eval h choice name types args dest ret) post onError before) =
      wp (IntrinsicBackend.eval backend h choice name types args dest ret) post onError := by
  rw [← actionPre_eq_wp]
  funext before
  simp only [IntrinsicBackend.eval]
  split
  · rw [actionPre_bind]
    have getResult : (get : EStateM StepError S S) before = .ok before before := rfl
    rw [actionPre_ok getResult]
    cases backend.selection before <;> simp only [actionPre_bind, purePre, errorPre]
  · rfl


theorem actionPre_intrinsicBackend (backend : IntrinsicBackend.Dispatcher S C D)
    (h : IntrinsicHooks Provenance S C D) (choice : C) (name : String) (types : Array TyId)
    (args : Array (OpTy Provenance)) (dest : D) (ret : Option BasicBlockId)
    (post : Bool → S → Prop) (onError : Errors) :
    actionPre (IntrinsicBackend.eval backend h choice name types args dest ret) post onError =
      fun before => if name.startsWith "atomic_" then
        match backend.selection before with
        | .ok _ => actionPre (IntrinsicAtomic.eval h.atomicHooks choice name args dest ret) post onError before
        | .error error => onError error before
      else actionPre (Intrinsics.eval h choice name types args dest ret) post onError before := by
  rw [actionPre_eq_wp]
  exact (intrinsicBackendPre_eq_wp backend h choice name types args dest ret post onError).symm

section Dispatch

variable {Extern FnABI ArgABI : Type}
local notation "Hooks" => CallHooks P S C E Other Extern FnABI ArgABI
local notation "Request" => CallRequest P Other Extern FnABI

def untuplePre (h : Hooks) (choice : C) (request : Request)
    (post : Array (FnArg P) → S → Prop) (onError : Errors) : S → Prop :=
  if h.isRustCall request.callerAbi && !request.args.isEmpty then
    match request.args[request.args.size - 1]? with
    | none => onError (.invalidProgram "missing RustCall tuple")
    | some last => actionPre (h.tupleFields last.layout.ty) (fun fields =>
      actionPre (forIn [:fields.size] request.args.pop fun idx args => do
        return .yield (args.push (← h.projectFnArg choice last idx))) post onError) onError
  else post request.args

/-- Continue a dispatch with either a completed call or a request from
intrinsic fallback or virtual resolution. Every guard keeps the state
immediately after its preceding successful operation. -/
def dispatchStepPre (h : Hooks) (choice : C) (request : Request)
    (post : Option Request → S → Prop) (onError : Errors)
    (scope : CallWP.RetagPullback h choice := CallWP.abstractRetagPullback h choice) : S → Prop :=
  let request := { request with unwind :=
    if (request.callerFnAbi.any (fun abi => !h.abiCanUnwind abi)) then .Unreachable else request.unwind }
  let withAbi (next : FnABI → S → Prop) :=
    match request.callerFnAbi with
    | some abi => next abi
    | none => onError (.invalidProgram "FnAbi should have been computed for this call")
  match request.callee with
  | .Other extra => withAbi fun abi =>
      actionPre (h.callExtra choice extra abi request.args request.destination request.target request.unwind)
        (fun _ => post none) onError
  | .Instance callee =>
    actionPre (h.instanceKind callee) (fun
      | .Intrinsic _ => fun state =>
        if request.withCallerLocation then onError (.invalidProgram "intrinsic received caller location") state
        else actionPre (h.callIntrinsic choice callee (request.args.map FnArg.copyFnArg)
            request.destination request.target request.unwind) (fun
          | none => post none
          | some fallback => actionPre (h.instanceKind fallback) (fun
            | .Item _ => actionPre (h.requiresCallerLocation fallback) (fun withLocation =>
              post (some { request with callee := .Instance fallback, withCallerLocation := withLocation }))
              onError
            | _ => onError (.invalidProgram "intrinsic fallback must be Item")) onError) onError state
      | .LlvmIntrinsic _ =>
        actionPre (h.callLlvmIntrinsic choice callee (request.args.map FnArg.copyFnArg)
          request.destination request.target) (fun _ => post none) onError
      | .Virtual definition slot => withAbi fun abi state =>
        if request.args.isEmpty then onError (.invalidProgram "virtual call missing receiver") state
        else actionPre (h.resolveVirtual choice callee definition slot abi request.args)
          (fun (concrete, abi, args) =>
            post (some { request with callee := .Instance concrete, callerFnAbi := some abi, args }))
          onError state
      | .Item _ | .Shim _ => withAbi fun abi =>
        actionPre (h.findMirOrEvalFn choice callee abi request.args request.destination request.target request.unwind)
          (fun | none => post none
               | some (body, concrete) =>
                 untuplePre h choice request (fun args =>
                   CallWP.initStackFramePre h choice concrete body abi args request.withCallerLocation
                     request.destination (.goto request.target request.unwind) (post none) onError scope) onError) onError)
      onError

set_option maxHeartbeats 600000 in
theorem actionPre_dispatchStep (h : Hooks) (choice : C) (request : Request)
    (post : Option Request → S → Prop) (onError : Errors)
    (scope : CallWP.RetagPullback h choice := CallWP.abstractRetagPullback h choice) :
    actionPre (Call.initFnCallStep h choice request) post onError =
      dispatchStepPre h choice request post onError scope := by
  simp only [Call.initFnCallStep, dispatchStepPre]
  cases request.callee with
  | Other extra =>
    cases request.callerFnAbi <;> simp only [actionPre_bind_fun, purePre, errorPre]
  | Instance callee =>
    simp only [actionPre_bind_fun]
    congr 1
    funext kind
    cases kind with
    | Intrinsic definition =>
      simp only [Call.require_eq, actionPre_ite, actionPre_bind_fun, purePre, errorPre]
      cases request.withCallerLocation <;>
        simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      congr 1
      funext fallback
      cases fallback with
      | none => rfl
      | some fallback =>
        simp only [actionPre_bind_fun]
        congr 1
        funext kind
        cases kind <;> simp only [actionPre_bind_fun, purePre, errorPre]
    | LlvmIntrinsic definition =>
      simp only [actionPre_bind_fun, purePre]
    | Virtual definition slot =>
      cases request.callerFnAbi <;>
        simp only [Call.require_eq, actionPre_ite, actionPre_bind_fun, purePre, errorPre]
      funext state
      cases request.args.isEmpty <;>
        simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    | Item definition | Shim _ =>
      all_goals try (rename_i shim; cases shim)
      all_goals
        cases request.callerFnAbi <;> simp only [actionPre_bind_fun, purePre, errorPre]
        congr 1
        funext loaded
        cases loaded with
        | none => rfl
        | some loaded =>
          obtain ⟨body, concrete⟩ := loaded
          simp only [untuplePre, actionPre_ite, actionPre_bind_fun, purePre,
            CallWP.initStackFramePre_eq_wp, ← actionPre_eq_wp, Call.at?]
          split <;> try rfl
          cases request.args[request.args.size - 1]? <;>
            simp only [purePre, errorPre]

/-- Open one iteration of the same budgeted precondition used by CallWP. -/
theorem dispatchPre_succ (h : Hooks) (choice : C) (budget : Nat) (request : Request)
    (post : S → Prop) (onError : Errors) (before : S)
    (scope : CallWP.RetagPullback h choice := CallWP.abstractRetagPullback h choice) :
    CallWP.dispatchPre h choice post onError (budget + 1) request before =
      dispatchStepPre h choice request (fun
        | none => post
        | some next => CallWP.dispatchPre h choice post onError budget next) onError scope before := by
  exact congrFun (actionPre_dispatchStep h choice request _ onError scope) before

end Dispatch


/-- A reference or raw-pointer receiver reads its immediate value. A dynamic
receiver supplies an existing indirect place. Newtype projection recurses
through the next receiver with the remaining traversal budget. -/
def receiverPre (h : VirtualCalls.Hooks P S C E) (choice : C)
    (post : MPlaceTy P → S → Prop) (onError : Errors) : Nat → OpTy P → S → Prop
  | 0, _ => onError (.resourceExhaustion "virtual receiver newtype traversal")
  | budget + 1, receiver =>
    actionPre (h.compiler.classifyReceiver receiver.layout.ty) (fun
      | .reference | .rawPointer => actionPre (h.readImmediate choice receiver) (fun immediate =>
          actionPre (h.immPtrToMPlace choice immediate) post onError) onError
      | .dynamic => match receiver.op with
        | .indirect place => post ⟨place, receiver.layout⟩
        | .immediate _ => onError (.invalidProgram "dynamic receiver must be indirect")
      | .other => actionPre (VirtualCalls.nonOneZstField h.compiler receiver.layout) (fun
        | none => onError (.invalidProgram "DispatchFromDyn receiver does not have exactly one non-1-ZST field")
        | some index => actionPre (h.projectField choice receiver index)
          (receiverPre h choice post onError budget) onError) onError) onError

theorem receiverPre_eq_actionPre (h : VirtualCalls.Hooks P S C E) (choice : C)
    (post : MPlaceTy P → S → Prop) (onError : Errors) (budget : Nat) (receiver : OpTy P) :
    receiverPre h choice post onError budget receiver =
      actionPre (VirtualCalls.receiverPlace h choice budget receiver) post onError := by
  induction budget generalizing receiver with
  | zero => rfl
  | succ budget ih =>
    simp only [receiverPre, VirtualCalls.receiverPlace, actionPre_bind_fun]
    congr 1
    funext kind
    cases kind <;> simp only [actionPre_bind_fun]
    · cases receiver.op <;> rfl
    · congr 1
      funext index
      cases index <;> simp only [actionPre_bind_fun, ← ih]
      rfl

/-- Pass a pure decoding result to the selected continuation at the same state. -/
def exceptPre {Err A : Type} (result : Except Err A) (convert : Err → StepError)
    (next : A → S → Prop) (onError : Errors) : S → Prop :=
  match result with
  | .ok value => next value
  | .error error => onError (convert error)

/-- Inspect dyn-tail metadata and the symbolic vtable, then check the full
compiler instance before replacing the receiver and its ABI type. -/
def resolveVirtualPre [PointerProvenance P] (h : VirtualCalls.Hooks P S C E) (choice : C)
    (budget : Nat) (callee : CallInstance) (method : DefId) (slot : Nat)
    (abi : FnAbi TyId) (args : Array (FnArg P))
    (post : CallInstance × FnAbi TyId × Array (FnArg P) → S → Prop) (onError : Errors) : S → Prop :=
  let finish (concrete : CallInstance) (receiverTy : TyId) (scalar : Scalar P)
      (layout : LocalLayout) (state : S) :=
    let receiver : FnArg P := .Copy ⟨.immediate (.scalar scalar), layout⟩
    if bound : 0 < args.size then
      let args := args.set 0 receiver bound
      match abi.args[0]? with
      | none => onError (.invalidProgram "virtual call ABI missing receiver") state
      | some firstAbi =>
        let firstAbi := { firstAbi with layout := { firstAbi.layout with ty := receiverTy } }
        if bound : 0 < abi.args.size then
          post (concrete, { abi with args := abi.args.set 0 firstAbi bound }, args) state
        else onError (.invalidProgram "virtual ABI receiver disappeared") state
    else onError (.invalidProgram "virtual receiver disappeared") state
  match args[0]? with
  | none => onError (.invalidProgram "virtual call missing receiver")
  | some first => receiverPre h choice (fun place =>
    actionPre (h.compiler.structTailForCodegen place.layout.ty) (fun tail =>
      actionPre (h.compiler.dynamicData tail) (fun
        | none => onError (.invalidProgram "dynamic call on non-dyn tail")
        | some data => fun state =>
          if place.layout.layout.isSized then onError (.invalidProgram "virtual receiver place is sized") state
          else exceptPre place.mplace.metadata.unwrapMeta (fun error => .invalidProgram (reprStr error))
            (fun metadata => exceptPre (metadata.toPointer h.target) ScalarOps.scalarError (fun vptr =>
              actionPre (VTable.getPtrVTableType h.vtable choice vptr (some data.predicates)) (fun dynTy =>
                actionPre (h.vtable.entries choice data.principal dynTy) (fun entries =>
                  match entries[slot]? with
                  | some (.method concrete) =>
                    actionPre (VirtualCalls.assertConcrete h.compiler choice dynTy method callee concrete)
                      (fun _ => actionPre (h.compiler.mutPointerType dynTy) (fun receiverTy =>
                        exceptPre (Scalar.fromMaybePointer h.target place.mplace.ptr) ScalarOps.scalarError
                          (fun scalar => actionPre (h.compiler.layoutOf receiverTy)
                            (finish concrete receiverTy scalar) onError) onError) onError) onError
                  | _ => onError (.undefinedBehavior "dyn call trying to call something that is not a method"))
                  onError) onError) onError) onError state) onError) onError) onError budget first.copyFnArg

set_option maxHeartbeats 600000 in
theorem resolveVirtualPre_eq_wp [PointerProvenance P] (h : VirtualCalls.Hooks P S C E) (choice : C)
    (budget : Nat) (callee : CallInstance) (method : DefId) (slot : Nat)
    (abi : FnAbi TyId) (args : Array (FnArg P))
    (post : CallInstance × FnAbi TyId × Array (FnArg P) → S → Prop) (onError : Errors) :
    resolveVirtualPre h choice budget callee method slot abi args post onError =
      wp (VirtualCalls.resolveVirtual h choice budget callee method slot abi args) post onError := by
  rw [← actionPre_eq_wp]
  simp only [resolveVirtualPre, VirtualCalls.resolveVirtual, receiverPre_eq_actionPre]
  cases args[0]? with
  | none => rfl
  | some first =>
    simp only [actionPre_bind_fun]
    congr 1
    funext place
    congr 1
    funext tail
    congr 1
    funext data
    cases data with
    | none => rfl
    | some data =>
      funext state
      simp only [actionPre_ite]
      split
      · rfl
      · simp only [VirtualCalls.scalarError_eq, exceptPre]
        cases place.mplace.metadata.unwrapMeta with
        | error => rfl
        | ok metadata =>
          simp only [actionPre_bind_fun, purePre]
          cases metadata.toPointer h.target with
          | error => rfl
          | ok vptr =>
            simp only [actionPre_bind_fun, purePre]
            congr 1
            funext dynTy
            congr 1
            funext entries
            cases entries[slot]? with
            | none => rfl
            | some entry =>
              cases entry <;> try rfl
              simp only [actionPre_bind_fun]
              congr 1
              funext checked
              congr 1
              funext receiverTy
              cases Scalar.fromMaybePointer h.target place.mplace.ptr <;> try rfl
              simp only [actionPre_bind_fun, purePre]
              congr 1
              funext layout after
              split
              · simp only [actionPre_bind, purePre]
                cases abi.args[0]? with
                | none => rfl
                | some firstAbi =>
                  by_cases bound : 0 < abi.args.size <;>
                    simp only [bound, dite_true, dite_false, actionPre_bind, purePre] <;> rfl
              · rfl


section Canonical

open MachineHooks (State)

variable {Extern Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C Other Extern Host
local notation "MachineErrors" => StepError → State K U → Prop

/-- Expose the actual body/foreign rule for a canonical call continuation. -/
theorem canonicalFindMirPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (callee : CallInstance) (abi : FnAbi TyId) (args : Array (FnArg Provenance))
    (dest : RuntimeStackPlace Provenance) (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Option (LoadedBody × CallInstance) → State K U → Prop) (onError : MachineErrors) :
    actionPre ((ExecutionMachine.callHooks config limits).findMirOrEvalFn choice callee abi args dest ret unwind)
      post onError =
    findMirPre config.calls.dispatch choice callee abi args dest ret unwind post onError := by
  rw [actionPre_eq_wp]
  exact (findMirPre_eq_wp config.calls.dispatch choice callee abi args dest ret unwind post onError).symm

/-- Resolve a function pointer through the canonical allocation and function dictionaries. -/
theorem canonicalPtrFnPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (pointer : Pointer (Option Provenance)) (post : FnVal Other → State K U → Prop)
    (onError : MachineErrors) :
    actionPre ((ExecutionMachine.callHooks config limits).getPtrFn choice pointer) post onError =
      getPtrFnPre config.functions pointer post onError := by
  rw [actionPre_eq_wp]
  exact (getPtrFnPre_eq_wp config.functions pointer post onError).symm

/-- Scalar and pointer decoding follow the actual immediate read, preserving
its effects on alignment, provenance, and race checks. -/
theorem canonicalReadPointerPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : OpTy Provenance)
    (post : Pointer (Option Provenance) → State K U → Prop) (onError : MachineErrors) :
    actionPre ((ExecutionMachine.callHooks config limits).readPointer choice operand) post onError =
      actionPre (PlaceMachine.readImmediate config.access operand) (fun value =>
        exceptPre value.imm.toScalar ScalarOps.immediateError (fun scalar =>
          exceptPre (scalar.toPointer config.access.runtime.base) ScalarOps.scalarError post onError)
          onError) onError := by
  simp only [ExecutionMachine.callHooks, ExecutionCalls.make, actionPre_bind_fun]
  congr 1
  funext value
  simp only [exceptPre, Except.mapError]
  cases value.imm.toScalar with
  | error => rfl
  | ok scalar =>
    change actionPre (pure scalar : CallM (State K U) (Scalar Provenance)) _ onError = _
    rw [purePre]
    have base : (ExecutionMachine.withValidation config limits).access.runtime.base =
        config.access.runtime.base := rfl
    simp only [base]
    cases scalar.toPointer config.access.runtime.base <;> rfl

/-- A handled intrinsic completes in its current state. An unhandled name must
pass both fallback policy checks before the compiler item is constructed. -/
def canonicalIntrinsicPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (callee : CallInstance) (args : Array (OpTy Provenance))
    (dest : RuntimeStackPlace Provenance) (ret : Option BasicBlockId)
    (post : Option CallInstance → State K U → Prop) (onError : MachineErrors) :
    State K U → Prop :=
  actionPre (config.intrinsicName callee) (fun name =>
    actionPre (config.calls.compiler.instanceArgs callee) (fun genericArgs =>
      let types := genericArgs.filterMap fun arg => match arg with | .Type ty => some ty | _ => none
      let context := ExecutionMachine.intrinsicHooks (ExecutionMachine.withValidation config limits)
        limits (config.intrinsics callee)
      actionPre (IntrinsicBackend.eval config.backend context choice name types args dest.toRuntimePlace ret)
        (fun handled handledState =>
          if handled then post none handledState
          else actionPre (config.intrinsicMustOverride callee) (fun override checked =>
            if override then onError (.unsupported s!"unimplemented intrinsic: {name}") checked
            else actionPre (config.intrinsicFallbackIsSpec callee) (fun isSpec resolved =>
              if isSpec then actionPre (config.calls.compiler.instanceKind callee) (fun kind =>
                actionPre (config.calls.compiler.itemInstance kind.defId genericArgs)
                  (fun fallback => post (some fallback)) onError) onError resolved
              else onError (.unsupported s!"intrinsic fallback is not a specification: {name}") resolved)
              onError checked) onError handledState) onError) onError) onError

set_option maxHeartbeats 500000 in
theorem actionPre_canonicalIntrinsic (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (callee : CallInstance) (args : Array (OpTy Provenance))
    (dest : RuntimeStackPlace Provenance) (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Option CallInstance → State K U → Prop) (onError : MachineErrors) :
    actionPre ((ExecutionMachine.callHooks config limits).callIntrinsic choice callee args dest ret unwind)
      post onError = canonicalIntrinsicPre config limits choice callee args dest ret post onError := by
  simp only [ExecutionMachine.callHooks, ExecutionCalls.make, canonicalIntrinsicPre, actionPre_bind_fun]
  congr 1
  funext name
  congr 1
  funext genericArgs
  congr 1
  funext handled handledState
  cases handled <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind, actionPre_pure]
  congr 1
  funext override checked
  cases override <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind, actionPre_throw]
  congr 1
  funext isSpec resolved
  cases isSpec <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind,
    actionPre_bind_fun, purePre, actionPre_throw]
  rfl

/-- LLVM dispatch resolves the compiler link name and builds its live dispatch
dictionary before materializing the destination inside the architecture rule. -/
theorem actionPre_canonicalLlvm (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (callee : CallInstance) (args : Array (OpTy Provenance))
    (dest : RuntimeStackPlace Provenance) (ret : Option BasicBlockId)
    (post : Unit → State K U → Prop) (onError : MachineErrors) :
    actionPre ((ExecutionMachine.callHooks config limits).callLlvmIntrinsic choice callee args dest ret)
      post onError =
    actionPre (config.calls.compiler.llvmLinkName callee) (fun name =>
      actionPre (config.calls.llvm callee) (fun llvm =>
        actionPre (IntrinsicArchitecture.callLlvm llvm choice name args dest.toRuntimePlace ret)
          post onError) onError) onError := by
  simp only [ExecutionMachine.callHooks, ExecutionCalls.make, actionPre_bind_fun]
  rfl

/-- Exact virtual resolver installed by the canonical call dictionary. -/
theorem canonicalVirtualPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (callee : CallInstance) (method : DefId) (slot : Nat)
    (abi : FnAbi TyId) (args : Array (FnArg Provenance))
    (post : CallInstance × FnAbi TyId × Array (FnArg Provenance) → State K U → Prop)
    (onError : MachineErrors) :
    let validated := ExecutionMachine.withValidation config limits
    let virtual := ExecutionCalls.virtualHooks validated.virtual validated.access
      (ExecutionMachine.operandHooks validated) validated.compiler.debugAssertions
    actionPre ((ExecutionMachine.callHooks config limits).resolveVirtual choice callee method slot abi args)
      post onError =
      resolveVirtualPre virtual choice limits.callDispatch callee method slot abi args post onError := by
  dsimp only
  rw [actionPre_eq_wp]
  exact (resolveVirtualPre_eq_wp ..).symm

/-- The dynamic extra-function projection uses the same foreign dictionary
as ordinary item dispatch. -/
theorem canonicalExtraPre (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (symbol : Other) (abi : FnAbi TyId) (args : Array (FnArg Provenance))
    (dest : RuntimeStackPlace Provenance) (ret : Option BasicBlockId) (unwind : UnwindAction)
    (post : Unit → State K U → Prop) (onError : MachineErrors) :
    actionPre ((ExecutionMachine.callHooks config limits).callExtra choice symbol abi args dest ret unwind)
      post onError =
      match config.calls.dispatch.foreign with
      | none => onError (.unsupported "dynamic foreign call requires complete source platform input")
      | some setup => actionPre (config.calls.dispatch.foreignScope do
          let hooks ← setup
          ForeignItems.emulateDynSym hooks (config.calls.dispatch.dynSymName symbol) abi
            (args.map FnArg.copyFnArg) dest.toRuntimePlace ret unwind) post onError := by
  have dispatch : (ExecutionMachine.withValidation config limits).calls.dispatch = config.calls.dispatch := rfl
  simp only [ExecutionMachine.callHooks, ExecutionCalls.make, dispatch]
  cases configured : config.calls.dispatch.foreign <;>
    simp only [CallDispatchMachine.callExtra, configured, errorPre]

/-- Use the concrete retag scope when opening a canonical frame continuation. -/
theorem canonicalDispatchPre_succ (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (budget : Nat) (request : CallRequest Provenance Other Extern (FnAbi TyId))
    (post : State K U → Prop) (onError : MachineErrors) (before : State K U) :
    let hooks := ExecutionMachine.callHooks config limits
    CallWP.dispatchPre hooks choice post onError (budget + 1) request before =
      dispatchStepPre hooks choice request (fun
        | none => post
        | some next => CallWP.dispatchPre hooks choice post onError budget next) onError
        (CallWP.canonicalRetagPullback config limits choice) before :=
  dispatchPre_succ (ExecutionMachine.callHooks config limits) choice budget request post onError before
    (CallWP.canonicalRetagPullback config limits choice)


end Canonical

/-- Copy and constant inputs are evaluated normally. Moves preserve the
source place when indirect, forcing allocation when disjointness is unknown. -/
def evalFnCallArgumentPre {Extern FnABI ArgABI : Type}
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (operand : Operand) (disjoint : Bool) (post : FnArg P → S → Prop) (onError : Errors) : S → Prop :=
  match operand with
  | .Copy _ | .Constant _ | .RuntimeChecks _ =>
    actionPre (h.evalOperand choice operand) (fun value => post (.Copy value)) onError
  | .Move place => actionPre (h.evalPlace choice place true) (fun place =>
    if disjoint then actionPre (h.placeToOp choice place) (fun value =>
      match value.op with
      | .indirect memory => post (.InPlace ⟨memory, value.layout⟩)
      | .immediate _ => post (.Copy value)) onError
    else actionPre (h.forceAllocation choice place) (fun memory => post (.InPlace memory)) onError)
    onError

theorem actionPre_evalFnCallArgument {Extern FnABI ArgABI : Type}
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (operand : Operand) (disjoint : Bool) (post : FnArg P → S → Prop) (onError : Errors) :
    actionPre (Call.evalFnCallArgument h choice operand disjoint) post onError =
      evalFnCallArgumentPre h choice operand disjoint post onError := by
  cases operand <;> simp only [Call.evalFnCallArgument, evalFnCallArgumentPre, actionPre_bind_fun, purePre]
  congr 1
  funext place
  cases disjoint <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun, purePre]
  congr 1
  funext value
  cases value.op <;> rfl

section CalleeEvaluation

variable {Extern FnABI ArgABI : Type}
local notation "Hooks" => CallHooks P S C E Other Extern FnABI ArgABI
local notation "Evaluated" => EvaluatedCall P Other Extern FnABI

/-- The normalized signature supplies the ABI and determines the extra
arguments. Function pointers read their operand and check its provenance
before querying the pointer ABI. An intrinsic's ABI comes from its item. -/
def evaluatedCalleePre (h : Hooks) (choice : C) (func : OpTy P) (args : Array (FnArg P))
    (post : Evaluated → S → Prop) (onError : Errors) : S → Prop :=
  actionPre (h.functionSignature choice func.layout) (fun (inputs, externAbi) state =>
    if inputs ≤ args.size then
      let extra := (args.extract inputs args.size).map fun arg => arg.layout.ty
      actionPre (h.functionKind func.layout.ty) (fun
        | .invalid => onError (.invalidProgram "invalid callee type")
        | .FnPtr => actionPre (h.readPointer choice func) (fun pointer =>
            actionPre (h.getPtrFn choice pointer) (fun value =>
              actionPre (h.fnAbiOfFnPtr choice func.layout extra) (fun abi =>
                post ⟨value, args, externAbi, some abi, false⟩) onError) onError) onError
        | .FnDef definition generics =>
          actionPre (h.resolve choice definition generics) (fun callee =>
            let finish (abi : Option FnABI) := actionPre (h.requiresCallerLocation callee)
              (fun withLocation => post ⟨.Instance callee, args, externAbi, abi, withLocation⟩) onError
            actionPre (h.instanceKind callee) (fun
              | .LlvmIntrinsic _ => finish none
              | .Intrinsic definition =>
                actionPre (h.instanceArgs callee) (fun generics =>
                  actionPre (h.itemInstance definition generics) (fun item =>
                    actionPre (h.fnAbiOfInstance choice item extra) (fun abi => finish (some abi))
                      onError) onError) onError
              | _ => actionPre (h.fnAbiOfInstance choice callee extra) (fun abi => finish (some abi))
                onError) onError) onError) onError state
    else onError (.invalidProgram "call has fewer args than normalized signature") state)
    onError

/-- Expose argument evaluation and normalized callee resolution separately.
The argument loop records the actual state of a failed projected argument. -/
theorem actionPre_evalCalleeAndArgs (h : Hooks) (choice : C) (func : Operand)
    (args : Array SpannedOperand) (dest : Place) (post : Evaluated → S → Prop) (onError : Errors) :
    actionPre (Call.evalCalleeAndArgs h choice func args dest) post onError =
      actionPre (h.evalOperand choice func) (fun operand =>
        actionPre (forIn [:args.size] #[] fun index evaluated => do
          let some arg := args[index]? | throw (.invalidProgram "missing source call argument")
          return .yield (evaluated.push (← Call.evalFnCallArgument h choice arg.operand
            (Call.moveDefinitelyDisjoint args dest))))
          (fun args => evaluatedCalleePre h choice operand args post onError) onError) onError := by
  simp only [Call.evalCalleeAndArgs, evaluatedCalleePre, actionPre_bind_fun]
  congr 1
  funext operand
  congr 1
  funext evaluated
  congr 1
  funext signature state
  obtain ⟨count, externAbi⟩ := signature
  simp only [Call.require_eq, actionPre_ite, purePre, errorPre]
  by_cases arity : count ≤ evaluated.size <;> simp only [arity, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  congr 1
  funext kind
  cases kind <;> simp only [actionPre_bind_fun, purePre, errorPre]
  congr 1
  funext callee
  congr 1
  funext dispatched
  cases dispatched <;> simp only [actionPre_bind_fun, purePre]

end CalleeEvaluation

/-- Open one canonical dispatch iteration and normalize its concrete
continuations. Repeat after settling a fallback or virtual request. -/
macro "miri_call_dispatch_wp" : tactic =>
  `(tactic|
    (simp (config := { failIfUnchanged := false }) only
       [CallWP.callPre, CallWP.tailCallPre, CallWP.tailDispatchPre] <;>
     simp (config := { failIfUnchanged := false, singlePass := true }) only [canonicalDispatchPre_succ] <;>
     simp (config := { failIfUnchanged := false }) only
       [dispatchStepPre, untuplePre, canonicalFindMirPre, findMirPre, canonicalPtrFnPre, exceptPre,
        getPtrFnPre, canonicalReadPointerPre, actionPre_canonicalIntrinsic, canonicalIntrinsicPre,
        actionPre_canonicalLlvm, canonicalVirtualPre, resolveVirtualPre, canonicalExtraPre,
        actionPre_intrinsicBackend, actionPre_evalCalleeAndArgs,
        evalFnCallArgumentPre, evaluatedCalleePre, actionPre_evalFnCallArgument, actionPre_foreignSetup,
        actionPre_dynSymSetup, foreignPre, actionPre_pruneSuppressed]))

end Miri.Verification.CallDispatchWP

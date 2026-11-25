import Miri.Verification.CallDispatchWP

namespace MiriTests.Verification.CallDispatchWP

open Miri.ABI Miri.Interpreter Miri.MIR Miri.Memory
open Miri.Verification.CallDispatchWP Miri.Verification.RvalueWP
open Miri.Verification Std.WP

variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "State" => MachineHooks.State K U

/-- One iteration of the canonical call WP rejects a backend error at the
state produced by classification, independently of the normal continuation. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (request : CallRequest Provenance O X (FnAbi TyId)) (instanceId : CallInstance)
    (definition : DefId) (abi : FnAbi TyId) (before resolved classified : State)
    (failure : StepError) (post : State → Prop) (onError : StepError → State → Prop)
    (callee : request.callee = .Instance instanceId) (computed : request.callerFnAbi = some abi)
    (kind : (ExecutionMachine.callHooks config limits).instanceKind instanceId before =
      .ok (.Item definition) resolved)
    (classify : config.calls.dispatch.isForeignItem instanceId resolved = .ok false classified)
    (backend : config.calls.dispatch.backend.selection classified = .error failure) :
    CallWP.dispatchPre (ExecutionMachine.callHooks config limits) () post onError 1 request before =
      onError failure classified := by
  miri_call_dispatch_wp
  simp only [callee, computed, actionPre_ok kind, actionPre_ok classify, Bool.false_eq_true,
    ↓reduceIte, backend]

/-- A pointer with nonzero offset fails before function registry lookup. -/
example (config : Config) (limits : ExecutionMachine.Limits) (pointer : Pointer (Option Provenance))
    (before resolved : State) (id : AllocId) (offset : Size)
    (post : FnVal O → State → Prop) (onError : StepError → State → Prop)
    (allocation : FunctionPointers.allocation config.functions pointer before = .ok (id, offset) resolved)
    (invalid : (offset != Size.ZERO) = true) :
    wp ((ExecutionMachine.callHooks config limits).getPtrFn () pointer) post onError before =
      onError (.undefinedBehavior "InvalidFunctionPointer") resolved := by
  rw [← actionPre_eq_wp, canonicalPtrFnPre]
  simp only [getPtrFnPre, actionPre_ok allocation, invalid, ↓reduceIte]

/-- A successful shim unwind routes to the unwind continuation without
looking up MIR. The error conditional is checked at the same state. -/
example {P S D MD Ptr B I : Type} (h : ForeignItems.Hooks P S D MD Ptr B I)
    (name : String) (abi : FnAbi TyId) (args : Array (OpTy P)) (dest : D) (allocated : MD)
    (ret : Option BasicBlockId) (unwind : UnwindAction) (before classified ready shimState : S)
    (post : Option (B × I) → S → Prop) (onError : StepError → S → Prop)
    (allocator : h.allocatorSymbol name before = .ok none classified)
    (allocate : h.forceAllocation dest classified = .ok allocated ready)
    (shim : ForeignItems.inner h name abi args allocated ready = .ok .NeedsUnwind shimState) :
    wp (ForeignItems.emulate h name abi args dest ret unwind) post onError before =
      actionPre (h.unwindToBlock unwind) (fun _ => post none) onError shimState := by
  rw [← foreignPre_eq_wp]
  simp only [foreignPre, actionPre_ok allocator, actionPre_ok allocate, actionPre_ok shim]

end MiriTests.Verification.CallDispatchWP

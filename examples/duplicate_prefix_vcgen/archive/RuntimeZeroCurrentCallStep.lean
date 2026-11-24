import duplicate_prefix.RuntimeZeroCurrentInstalled
import duplicate_prefix.RuntimeZeroEntry
import duplicate_prefix.RuntimeZeroDispatch
import duplicate_prefix.RuntimeCallQueries
import duplicate_prefix.CallEntryLocals

/-! The actual checkLanguage MIR call terminator which enters the zero-argument
    language-runtime helper.  Operand resolution, destination evaluation,
    dispatch and `initStackFrame` are all the production hooks. -/
namespace DuplicatePrefix.RuntimeZeroCurrentCallStep
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def function : Operand := .Constant RuntimeFunctionConstant.constant
def destination (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  (LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout).stackView
theorem call_terminator
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : caller.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : caller.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : caller.location = .mir ⟨0,3⟩)
    (callerSize : 1 < caller.locals.size)
    (callerLive : caller.locals[1].value = .live (.immediate .uninit))
    (callerCached : caller.locals[1].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack.frames[threadIndex]? = some current)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    Call.evalCallTerminator
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () limits.callDispatch
      (CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (RuntimeZeroCurrentInstalled.frame options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller))
        (RuntimeZeroEntry.pushedMachine options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller) current)) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks config limits
  let state := Storage.withCurrent frames caller machine
  let dest := destination frames caller
  let block := CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let terminator := block.terminator
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have termKind : terminator.kind =
      .Call function #[] ⟨1,#[]⟩ (some 1) .Unreachable .Misc ⟨208⟩ := by
    with_unfolding_all rfl
  have blockAt : caller.body.basicBlocks[0]? = some block := by
    rw [body]
    with_unfolding_all rfl
  have noStatement : block.statements[3]? = none := by
    with_unfolding_all rfl
  have functionEval : h.evalOperand ()  function state =
      .ok ⟨.immediate .uninit,RuntimeCallQueries.functionLayout⟩ state := by
    change OperandMachine.evalOperand (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      ()  function none state = _
    rw [function]
    exact RuntimeFunctionConstant.function_operand options limits (remaining+1) span source debugOff
      frames caller machine (congrArg (·.index) identity) location callee
  have signature : h.functionSignature () RuntimeCallQueries.functionLayout =
      pure (0,ABI.ExternAbi.Rust) := by
    change config.calls.compiler.functionSignature () _ = _
    rw [fields.callCompiler]
    simp only [CompilerCallConstruction.compiler,CompilerExecutionCallLeaves.make]
    rw [RuntimeCallQueries.functionLayout_shape.1,RuntimeCallQueries.function_signature_query]
    simp only [bind,Except.bind,pure,Except.pure]
    with_unfolding_all rfl
  have kind : h.functionKind RuntimeCallQueries.functionLayout.ty =
      pure (.FnDef 43 #[]) := by
    change config.calls.compiler.functionKind _ = _
    rw [fields.callCompiler]
    with_unfolding_all change (match CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions
      RuntimeCallQueries.functionLayout.ty with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) = _
    rw [RuntimeCallQueries.functionLayout_shape.1,RuntimeCallQueries.function_kind]
    with_unfolding_all rfl
  have resolve : h.resolve () 43 #[] state = .ok GuardCompilerFacts.runtimeCall.callee state := by
    change config.calls.compiler.resolve () 43 #[] state = _
    rw [fields.callCompiler]
    exact RuntimeCallQueries.resolve_current frames caller machine body identity callee location
  have itemKind : h.instanceKind GuardCompilerFacts.runtimeCall.callee = pure (.Item 43) := by
    change config.calls.compiler.instanceKind _ = _
    rw [fields.callCompiler]
    dsimp only [CompilerCallConstruction.compiler,CompilerExecutionCallLeaves.make]
    unfold_internal ".CompilerExecutionCallLeaves.lift"
    with_unfolding_all rfl
  have fnAbi : h.fnAbiOfInstance () GuardCompilerFacts.runtimeCall.callee #[] = pure GuardCompilerFacts.runtimeAbi := by
    funext st
    exact GuardCompilerFacts.actual_runtime_abi options () (remaining+1) span st
  have callerLocation : h.requiresCallerLocation GuardCompilerFacts.runtimeCall.callee = pure false := by
    funext st
    exact GuardCompilerFacts.actual_runtime_caller_location options () (remaining+1) span limits st
  have calleeEval := GenericCallStages.eval_callee_zero h () function ⟨1,#[]⟩
    ⟨.immediate .uninit,RuntimeCallQueries.functionLayout⟩ state state .Rust 43 #[]
    GuardCompilerFacts.runtimeCall.callee 43 GuardCompilerFacts.runtimeAbi false
    functionEval signature kind resolve itemKind fnAbi callerLocation
  have destinationEval := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff
    frames caller machine 1 RootCompilerFacts.boolLayout callerSize callerCached (by decide +kernel)
  have destEq : dest = RuntimeZeroEntry.destination frames caller := by rfl
  have destinationEval' : h.evalPlace () ⟨1,#[]⟩ false state = .ok dest state := by
    exact destinationEval
  let call : EvaluatedCall Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.runtimeCall.callee,#[],.Rust,some GuardCompilerFacts.runtimeAbi,false⟩
  have calleeEval' : Call.evalCalleeAndArgs h () function #[] ⟨1,#[]⟩ state = .ok call state := by
    simpa [call,dest,destination] using calleeEval
  let after := Storage.withCurrent (frames.push caller)
    (RuntimeZeroDone.doneFrame (RuntimeZeroEntry.rawFrame options state (RuntimeZeroEntry.destination frames caller)))
    (RuntimeZeroEntry.pushedMachine options state (RuntimeZeroEntry.destination frames caller) current)
  let request : CallRequest Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.runtimeCall.callee,.Rust,some GuardCompilerFacts.runtimeAbi,#[],false,
      RuntimeZeroEntry.destination frames caller,some 1,.Unreachable⟩
  have find := RuntimeZeroDispatch.find_mir options limits (remaining+1) span state #[]
    (RuntimeZeroEntry.destination frames caller) (some 1) .Unreachable backend noRace
  have canUnwind : h.abiCanUnwind GuardCompilerFacts.runtimeAbi = false := by
    change GuardCompilerFacts.runtimeAbi.canUnwind = false
    exact congrArg (fun x => x.2.2.2.2.2) GuardCompilerFacts.runtime_abi_shape
  have abiEq : GuardCompilerFacts.languageAbi = GuardCompilerFacts.runtimeAbi := by decide +kernel
  have rustCall : h.isRustCall ABI.ExternAbi.Rust = false := by
    change config.calls.compiler.isRustCall .Rust = false
    rw [fields.callCompiler]
    rfl
  have dispatchStep : Call.initFnCallStep h () request state = .ok none after := by
    have item := CallItemDispatch.item_step_nounwind (unwind := .Unreachable) h GuardCompilerFacts.runtimeCall.callee 43 GuardCompilerFacts.runtimeAbi
      #[] false (RuntimeZeroEntry.destination frames caller) (some 1) .Rust itemKind canUnwind rustCall
    rw [item]
    simp only [CallItemDispatch.itemStage, bind, EStateM.bind]
    have find' := find
    change h.findMirOrEvalFn () GuardCompilerFacts.runtimeCall.callee GuardCompilerFacts.runtimeAbi #[]
      (RuntimeZeroEntry.destination frames caller) (some 1) .Unreachable state = _ at find'
    rw [find']
    simp only [bind, EStateM.bind, pure, EStateM.pure]
    have enter := RuntimeZeroEntry.actual_entry options limits remaining span debugOff frames caller machine
      callerSize callerLive callerCached callerNoClocks noRace ghost tracker tracked thread threadIndex current active top present
    have enter' : Call.initStackFrame h () GuardCompilerFacts.runtimeCall.callee
        CopyPreconditions.Bodies.languageRuntime.loaded GuardCompilerFacts.runtimeAbi #[] false
        (RuntimeZeroEntry.destination frames caller) (.goto (some 1) .Unreachable)
        (Storage.withCurrent frames caller machine) = .ok ()
        (Storage.withCurrent (frames.push caller)
          (RuntimeZeroDone.doneFrame (RuntimeZeroEntry.rawFrame options
            (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)))
          (RuntimeZeroEntry.pushedMachine options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller) current)) := by
      rw [← abiEq]
      exact enter
    rw [enter']
  have init : Call.initFnCall h () limits.callDispatch request state = .ok () after := by
    have step := CallItemDispatch.dispatch_one h request state after budget dispatchStep
    simpa [dispatchFuel] using step
  have init' : Call.initFnCall h () limits.callDispatch
      ⟨call.callee,call.callerAbi,call.fnAbi,call.args,call.withCallerLocation,
        RuntimeZeroEntry.destination frames caller,some 1,
        if call.fnAbi.any h.abiCanUnwind then .Unreachable else .Unreachable⟩ state = .ok () after := by
    simpa [request,call] using init
  have getFrame : h.getFrame state = .ok caller state := by
    exact CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine
  have oldIndex : h.frameIndex state = .ok frames.size state := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) state = _
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have progress : frames.size + 1 ≠ frames.size := by omega
  apply GenericCallStages.call_terminator h () limits.callDispatch block.terminator function #[] ⟨1,#[]⟩
    1 .Unreachable .Misc ⟨208⟩ state state state after caller frames.size (frames.size+1)
    (RuntimeZeroEntry.destination frames caller) call termKind getFrame oldIndex
    (by simpa [destEq] using destinationEval') calleeEval' init' ?_ newIndex progress
  change (return (← get).stack.frames.isEmpty : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) after = _
  simp [after,Storage.withCurrent,Array.isEmpty_push,bind,EStateM.bind,get,getThe,
    MonadStateOf.get,EStateM.get,pure,EStateM.pure]

end
end DuplicatePrefix.RuntimeZeroCurrentCallStep
#print axioms DuplicatePrefix.RuntimeZeroCurrentCallStep.call_terminator

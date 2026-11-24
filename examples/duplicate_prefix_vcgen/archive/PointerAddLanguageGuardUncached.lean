import duplicate_prefix.PointerAddLanguageGuardFacts
import duplicate_prefix.LanguageGuardEntryAt
import duplicate_prefix.LanguageZeroDispatch
import duplicate_prefix.LanguageZeroFunctionFacts
import duplicate_prefix.CallEntryLocals
import duplicate_prefix.GenericCallStages
import duplicate_prefix.CallUncachedLocal
namespace DuplicatePrefix.PointerAddLanguageGuardUncached
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def function : Operand := .Constant PointerAddLanguageGuardFacts.constant
noncomputable def destination (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame) :=
  (LocalPlaces.localRuntimePlace frames.size caller 4 RootCompilerFacts.boolLayout).stackView
noncomputable def cachedCaller (caller : CompilerFrameContext.ActualFrame) (valid : 4 < caller.locals.size) :=
  LocalPlaces.cachePlaceLayout caller 4 RootCompilerFacts.boolLayout valid
theorem compute_local4 (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = PointerAddCurrentFacts.body.body) (identity : caller.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : caller.functionInstance = PointerAddCurrentFacts.call.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 4 (Storage.withCurrent frames caller machine) =
      .ok RootCompilerFacts.boolLayout (Storage.withCurrent frames caller machine) := by
  have normalized : CompilerFrameContext.localType PreparedReflection.actual.compiler caller 4 = .ok 0 := by
    unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
    rw [body,identity,callee]
    with_unfolding_all rfl
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  unfold_frame_query_lift
  simp only [pure,EStateM.pure]
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 0 = .ok RootCompilerFacts.boolLayout :=
    RootCompilerFacts.bool_layout_eq
  simp [lookup,Except.mapError,EStateM.pure]

theorem call_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (original : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : original.body = PointerAddCurrentFacts.body.body)
    (identity : original.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : original.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : original.location = .mir ⟨0,2⟩)
    (originalSize : 4 < original.locals.size)
    (originalLive : original.locals[4].value = .live (.immediate .uninit))
    (originalUncached : original.locals[4].layout = none)
    (originalNoClocks : original.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) machine) (LanguageGuardEntryAt.destination frames original 4)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) machine) (LanguageGuardEntryAt.destination frames original 4)).stack.frames[threadIndex]? = some current)
 :
    Call.evalCallTerminator
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () limits.callDispatch
      (PointerAddCurrentFacts.body.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator
      (Storage.withCurrent frames original machine) =
      .ok () (Storage.withCurrent (frames.push (cachedCaller original originalSize))
        (LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options (Storage.withCurrent frames (cachedCaller original originalSize) machine)
          (LanguageGuardEntryAt.destination frames original 4)))
        (LanguageZeroEntry.pushedMachine options (Storage.withCurrent frames (cachedCaller original originalSize) machine)
          (LanguageGuardEntryAt.destination frames original 4) current)) := by
  let caller := cachedCaller original originalSize
  have callerSize : 4 < caller.locals.size := by simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout] using originalSize
  have callerLive : caller.locals[4].value = .live (.immediate .uninit) := by simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using originalLive
  have callerCached : caller.locals[4].layout = some RootCompilerFacts.boolLayout := by simp [caller,cachedCaller,LocalPlaces.cachePlaceLayout]
  have body : caller.body = PointerAddCurrentFacts.body.body := body
  have identity := identity
  have callee := callee
  have location := location
  have callerNoClocks := originalNoClocks
  let originalState := Storage.withCurrent frames original machine
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks config limits
  let state := Storage.withCurrent frames caller machine
  let dest := destination frames caller
  let block := PointerAddCurrentFacts.body.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let terminator := block.terminator
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have termKind : terminator.kind =
      .Call function #[] ⟨4,#[]⟩ (some 1) .Unreachable .Normal ⟨86⟩ := by
    with_unfolding_all rfl
  have blockAt : caller.body.basicBlocks[0]? = some block := by
    rw [body]
    with_unfolding_all rfl
  have noStatement : block.statements[2]? = none := by
    with_unfolding_all rfl
  have functionEval : h.evalOperand ()  function state =
      .ok ⟨.immediate .uninit,LanguageZeroFunctionFacts.functionLayout⟩ state := by
    change OperandMachine.evalOperand (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      ()  function none state = _
    rw [function]
    exact PointerAddLanguageGuardFacts.function_operand options limits (remaining+1) span source debugOff
      frames caller machine (congrArg (·.index) identity) location callee
  have signature : h.functionSignature () LanguageZeroFunctionFacts.functionLayout =
      pure (0,ABI.ExternAbi.Rust) := by
    change config.calls.compiler.functionSignature () _ = _
    rw [fields.callCompiler]
    simp only [CompilerCallConstruction.compiler,CompilerExecutionCallLeaves.make]
    rw [LanguageZeroFunctionFacts.functionLayout_shape.1,LanguageZeroFunctionFacts.function_signature_query]
    simp only [bind,Except.bind,pure,Except.pure]
    with_unfolding_all rfl
  have kind : h.functionKind LanguageZeroFunctionFacts.functionLayout.ty =
      pure (.FnDef 27 #[]) := by
    change config.calls.compiler.functionKind _ = _
    rw [fields.callCompiler]
    with_unfolding_all change (match CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions
      LanguageZeroFunctionFacts.functionLayout.ty with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) = _
    rw [LanguageZeroFunctionFacts.functionLayout_shape.1,LanguageZeroFunctionFacts.function_kind]
    with_unfolding_all rfl
  have resolve : h.resolve () 27 #[] state = .ok GuardCompilerFacts.languageCall.callee state := by
    change config.calls.compiler.resolve () 27 #[] state = _
    rw [fields.callCompiler]
    exact PointerAddLanguageGuardFacts.resolve_current frames caller machine body identity callee location
  have itemKind : h.instanceKind GuardCompilerFacts.languageCall.callee = pure (.Item 27) := by
    change config.calls.compiler.instanceKind _ = _
    rw [fields.callCompiler]
    dsimp only [CompilerCallConstruction.compiler,CompilerExecutionCallLeaves.make]
    unfold_internal ".CompilerExecutionCallLeaves.lift"
    with_unfolding_all rfl
  have fnAbi : h.fnAbiOfInstance () GuardCompilerFacts.languageCall.callee #[] = pure GuardCompilerFacts.languageAbi := by
    funext st
    exact GuardCompilerFacts.actual_language_abi options () (remaining+1) span st
  have callerLocation : h.requiresCallerLocation GuardCompilerFacts.languageCall.callee = pure false := by
    funext st
    exact GuardCompilerFacts.actual_language_caller_location options () (remaining+1) span limits st
  have calleeEval := GenericCallStages.eval_callee_zero h () function ⟨4,#[]⟩
    ⟨.immediate .uninit,LanguageZeroFunctionFacts.functionLayout⟩ state state .Rust 27 #[]
    GuardCompilerFacts.languageCall.callee 27 GuardCompilerFacts.languageAbi false
    functionEval signature kind resolve itemKind fnAbi callerLocation
  have destinationEval := CallUncachedLocal.uncached options limits (remaining+1) span debugOff
    frames original machine 4 RootCompilerFacts.boolLayout originalSize originalUncached (by decide +kernel)
    (compute_local4 frames original machine body identity callee)
  have destEq : dest = LanguageGuardEntryAt.destination frames caller 4 := by rfl
  have destinationEval' : h.evalPlace () ⟨4,#[]⟩ false originalState = .ok dest state := by
    exact destinationEval
  let call : EvaluatedCall Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.languageCall.callee,#[],.Rust,some GuardCompilerFacts.languageAbi,false⟩
  have calleeEval' : Call.evalCalleeAndArgs h () function #[] ⟨4,#[]⟩ state = .ok call state := by
    simpa [call,dest,destination] using calleeEval
  let after := Storage.withCurrent (frames.push caller)
    (LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options state (LanguageGuardEntryAt.destination frames caller 4)))
    (LanguageZeroEntry.pushedMachine options state (LanguageGuardEntryAt.destination frames caller 4) current)
  let request : CallRequest Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.languageCall.callee,.Rust,some GuardCompilerFacts.languageAbi,#[],false,
      LanguageGuardEntryAt.destination frames caller 4,some 1,.Unreachable⟩
  have find := LanguageZeroDispatch.find_mir options limits (remaining+1) span state #[]
    (LanguageGuardEntryAt.destination frames caller 4) (some 1) .Unreachable backend noRace
  have canUnwind : h.abiCanUnwind GuardCompilerFacts.languageAbi = false := by
    change GuardCompilerFacts.languageAbi.canUnwind = false
    exact congrArg (fun x => x.2.2.2.2.2) GuardCompilerFacts.language_abi_shape
  have abiEq : GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi := by rfl
  have rustCall : h.isRustCall ABI.ExternAbi.Rust = false := by
    change config.calls.compiler.isRustCall .Rust = false
    rw [fields.callCompiler]
    rfl
  have dispatchStep : Call.initFnCallStep h () request state = .ok none after := by
    have item := CallItemDispatch.item_step_nounwind (unwind := .Unreachable) h GuardCompilerFacts.languageCall.callee 27 GuardCompilerFacts.languageAbi
      #[] false (LanguageGuardEntryAt.destination frames caller 4) (some 1) .Rust itemKind canUnwind rustCall
    rw [item]
    simp only [CallItemDispatch.itemStage, bind, EStateM.bind]
    have find' := find
    change h.findMirOrEvalFn () GuardCompilerFacts.languageCall.callee GuardCompilerFacts.languageAbi #[]
      (LanguageGuardEntryAt.destination frames caller 4) (some 1) .Unreachable state = _ at find'
    rw [find']
    simp only [bind, EStateM.bind, pure, EStateM.pure]
    have enter := LanguageGuardEntryAt.actual_entry options limits remaining span debugOff frames caller machine 4
      callerSize callerLive callerCached callerNoClocks noRace ghost tracker tracked thread threadIndex current active top present
    have enter' : Call.initStackFrame h () GuardCompilerFacts.languageCall.callee
        CopyPreconditions.Bodies.checkLanguage.loaded GuardCompilerFacts.languageAbi #[] false
        (LanguageGuardEntryAt.destination frames caller 4) (.goto (some 1) .Unreachable)
        (Storage.withCurrent frames caller machine) = .ok ()
        (Storage.withCurrent (frames.push caller)
          (LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options
            (Storage.withCurrent frames caller machine) (LanguageGuardEntryAt.destination frames caller 4)))
          (LanguageZeroEntry.pushedMachine options (Storage.withCurrent frames caller machine)
            (LanguageGuardEntryAt.destination frames caller 4) current)) := by
      rw [← abiEq]
      exact enter
    rw [enter']
  have init : Call.initFnCall h () limits.callDispatch request state = .ok () after := by
    have step := CallItemDispatch.dispatch_one h request state after budget dispatchStep
    simpa [dispatchFuel] using step
  have init' : Call.initFnCall h () limits.callDispatch
      ⟨call.callee,call.callerAbi,call.fnAbi,call.args,call.withCallerLocation,
        LanguageGuardEntryAt.destination frames caller 4,some 1,
        if call.fnAbi.any h.abiCanUnwind then .Unreachable else .Unreachable⟩ state = .ok () after := by
    simpa [request,call] using init
  have getFrame : h.getFrame originalState = .ok original originalState := by
    exact CallEntryLocals.get_frame options limits (remaining+1) span frames original machine
  have oldIndex : h.frameIndex originalState = .ok frames.size originalState := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) originalState = _
    simp [originalState,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have progress : frames.size + 1 ≠ frames.size := by omega
  apply GenericCallStages.call_terminator h () limits.callDispatch block.terminator function #[] ⟨4,#[]⟩
    1 .Unreachable .Normal ⟨86⟩ originalState state state after original frames.size (frames.size+1)
    (LanguageGuardEntryAt.destination frames caller 4) call termKind getFrame oldIndex
    (by simpa [destEq] using destinationEval') calleeEval' init' ?_ newIndex progress
  change (return (← get).stack.frames.isEmpty : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) after = _
  simp [after,Storage.withCurrent,Array.isEmpty_push,bind,EStateM.bind,get,getThe,
    MonadStateOf.get,EStateM.get,pure,EStateM.pure]


end DuplicatePrefix.PointerAddLanguageGuardUncached

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.PointerAddLanguageGuardUncached.compute_local4, ``DuplicatePrefix.PointerAddLanguageGuardUncached.call_uncached] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved language cache dependency {dependency}"

import Representative
import Miri.Input.CompilerLifecycle
import Miri.Input.CompilerFunctionFacts
import Lean

namespace DuplicatePrefix.LanguageGuardCall

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR

set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

/-- The pinned runtime guard is an actual zero-argument, one-local body. -/
theorem runtimeGuardShape :
    (GeneratedBodySafety.input.document.bodies[19]?.map
      fun body => (body.instanceId, body.mir.argumentCount, body.mir.locals)) =
      some (21, 0, #[0]) := by
  rfl

/-- Exact source ABI evidence for the current retained callee. A resolver
must still use this row to construct its Rust ABI. -/
theorem runtimeGuardABI :
    (do
      let material ← GeneratedBodySafety.input.document.sourceAbi
      let entry ← material.definitions[21]?.join
      return (entry.instanceId, entry.signature.inputs, entry.signature.output,
        entry.signature.abi, entry.signature.cVariadic, entry.callerLocation)) =
      some (21, #[], 0, .Rust, false, none) := by
  rfl

/-- The retained function operand is the exported zero-argument Rust item.
These are the actual production compiler kind and signature lookups. -/
theorem runtimeGuardFunctionFacts (prepared : Miri.Input.CompilerFunctionFacts.Prepared)
    (source : prepared.runtime.source = GeneratedBodySafety.input.document) :
    Miri.Input.CompilerFunctionFacts.kind prepared 111 = .ok (.FnDef 43 #[]) ∧
    Miri.Input.CompilerFunctionFacts.signature prepared 111 = .ok (0, .Rust) := by
  rcases prepared with ⟨⟨document, target⟩, program⟩
  change document = _ at source
  subst document
  exact ⟨rfl, rfl⟩

variable {P S C E O X F A : Type}
local notation "Hooks" => CallHooks P S C E O X F A

private def requireGuard (condition : Bool) (message : String) : CallM S Unit :=
  unless condition do throw (.invalidProgram message)

private def setupNoArguments (hooks : Hooks) (choice : C) (fnInstance : CallInstance)
    (code : LoadedBody) (abi : F) (destination : RuntimeStackPlace P)
    (cont : ReturnContinuation) : CallM S Unit := do
  let operand ← hooks.placeToOp choice destination
  let memory := match operand.op with
    | .indirect place => some (MPlaceTy.mk place operand.layout)
    | .immediate _ => none
  hooks.pushRaw choice fnInstance code destination cont
  let frame ← hooks.getFrame
  let span ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  hooks.setFrame {frame with trackCallerArg := none}
  let (_, index) ← hooks.withRetagMode choice .FnEntry (pure (0, 0))
  let localSpan ← hooks.localSpan code.body 0
  let frame ← hooks.getFrame
  hooks.setFrame {frame with location := .unwinding localSpan}
  unless ← hooks.checkArgumentCompat choice (hooks.abiReturn abi) (hooks.abiReturn abi) do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some place := memory then hooks.protectArgument choice place
  let frame ← hooks.getFrame
  hooks.setFrame {frame with location := .unwinding span}
  requireGuard (index == (hooks.abiArgs abi).size)
    "mismatch between callee ABI and callee body arguments"
  hooks.afterFrameInit choice
  hooks.pushDone choice

open Lean Elab Tactic in
elab "unfold_call_helper " suffix:str : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".Call." ++ suffix.getString) then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one call helper named {suffix.getString}"

/-- Pull back the real call initializer for a zero-argument Rust ABI. Raw
frame initialization, protection, and storage-live effects remain actual
operations in the resulting clear order. -/
theorem initRuntimeGuard
    (hooks : Hooks) (choice : C) (fnInstance : CallInstance) (code : LoadedBody) (abi : F)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation)
    (arity : code.body.argumentCount = 0)
    (requires : hooks.requiresCallerLocation fnInstance = pure false)
    (calleeABI : hooks.fnAbiOfInstance choice fnInstance #[] = pure abi)
    (feature : hooks.checkTargetFeatures choice fnInstance = pure ())
    (closure : hooks.nonCapturingClosure choice fnInstance abi = pure false)
    (nonvariadic : hooks.abiVariadic abi = false)
    (convention : hooks.sameConvention abi abi = true)
    (noABIArguments : (hooks.abiArgs abi).size = 0) :
    Call.initStackFrame hooks choice fnInstance code abi #[] false destination cont =
      setupNoArguments hooks choice fnInstance code abi destination
        (if hooks.abiCanUnwind abi then cont else
          match cont with
          | .stop _ => cont
          | .goto target _ => .goto target .Unreachable) := by
  unfold Call.initStackFrame setupNoArguments
  unfold_call_helper "require"
  unfold_call_helper "at?"
  unfold_call_helper "setSpan"
  simp [requires, calleeABI, feature, closure, nonvariadic, convention,
    requireGuard, noABIArguments, arity, bind_assoc]
  congr 1

abbrev GuardFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra

private def withFrame (older : Array GuardFrame) (frame : GuardFrame)
    (machine : MachineHooks.MachineState K U) : MachineHooks.State K U :=
  ⟨⟨older.push frame⟩, machine⟩

private def liveResult (frame : GuardFrame) : GuardFrame :=
  {frame with locals := #[⟨.live (.immediate .uninit), none⟩]}

/-- The actual storage transition of the zero-input guard initializes only
its Boolean return local and reaches the first MIR statement. -/
theorem pushDoneRuntimeGuard (lifecycle : CallMachine.Lifecycle K U C)
    (older : Array GuardFrame) (frame : GuardFrame) (machine : MachineHooks.MachineState K U)
    (source : GeneratedBodySafety.input.document.bodies[19]?.map (·.mir) = some frame.body)
    (locals : frame.locals = #[⟨.dead, none⟩]) (noClocks : frame.extra.dataRace = none)
    (trivial : lifecycle.storage.veryTriviallySized 0 = .ok true) :
    CallMachine.pushDone lifecycle (withFrame older frame machine) =
      .ok () (withFrame older {liveResult frame with location := .mir .start} machine) := by
  have typed : frame.body.locals = #[0] := by
    have fact := congrArg (fun code : Option Body => code.map (·.locals)) source
    exact Option.some.inj fact.symm
  have storage : MachineHooks.storageLiveDyn lifecycle.storage 0 .none (withFrame older frame machine) =
      .ok () (withFrame older (liveResult frame) machine) := by
    simp [MachineHooks.storageLiveDyn, MachineHooks.currentFrame, MachineHooks.setCurrentFrame,
      MachineHooks.afterLocalWrite, withFrame, Stack.currentFrame?, Frame.getLocal,
      Frame.replaceLocalValue, locals, typed, trivial, noClocks, MemPlaceMeta.hasMeta,
      bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      set, MonadStateOf.set, EStateM.set, pure, Pure.pure, Except.pure, EStateM.pure,
      liveResult]
  have current : MachineHooks.currentFrame (withFrame older (liveResult frame) machine) =
      .ok (liveResult frame) (withFrame older (liveResult frame) machine) := by
    simp [MachineHooks.currentFrame, withFrame, Stack.currentFrame?,
      bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, Pure.pure, EStateM.pure]
  have always : CallMachine.alwaysLiveVarsAndTemps (liveResult frame).body = .ok #[] := by
    have fact := congrArg (fun code : Option Body => code.map CallMachine.alwaysLiveVarsAndTemps) source
    exact Option.some.inj fact.symm
  have hasBlock : 0 < frame.body.basicBlocks.size := by
    have fact := congrArg (fun code : Option Body => code.map (·.basicBlocks.size)) source
    have size : frame.body.basicBlocks.size = 1 := Option.some.inj fact.symm
    omega
  have start : (liveResult frame).setLocation (.mir .start) =
      .ok {liveResult frame with location := .mir .start} := by
    simp [Frame.setLocation, Location.start, liveResult, hasBlock, pure, Pure.pure, Except.pure]
  unfold CallMachine.pushDone
  simp only [bind, EStateM.bind]
  rw [storage]
  simp only
  rw [current]
  simp only
  rw [always]
  simp [← Array.forIn_toList, bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, withFrame, Stack.updateCurrentLocation,
    start, set, MonadStateOf.set, EStateM.set, Except.pure, Except.bind, Array.set_push]

/-- A zero-argument call executes an empty FnEntry scope. The actual mode
wrapper restores the old tracking state, including enabled Tree Borrows. -/
theorem emptyArgumentScope (before : MachineHooks.State K U) :
    MachineHooks.withRetagMode .FnEntry
      (pure (0, 0) : MachineHooks.M K U (Nat × Nat)) before = .ok (0, 0) before := by
  rcases before with ⟨stack, machine⟩
  cases machine with
  | mk memory borrow race threads allocations spans user =>
    cases borrow with
    | none => rfl
    | some tracker =>
      cases tracker
      rfl

private def runtimeFrame (body : LoadedBody) (fnInstance : CallInstance)
    (dest : RuntimeStackPlace Provenance) (cont : ReturnContinuation)
    (span : SpanRef) (identity : LocalsIdentity)
    (machine : MachineHooks.MachineState K U) (userRelevance : UInt8) : GuardFrame :=
  Frame.create body fnInstance
    {borrowTracker := machine.borrowTracker.map fun _ => {},
     catchUnwind := none, userRelevance, dataRace := machine.dataRace.map fun _ => {}}
    cont dest span identity

/-- The production raw-push path constructs the retained runtime-guard
frame and updates the relevance cache. Its compiler premises are row and
query identities, not a successful push assumption. -/
theorem pushRawRuntimeGuard
    (prepared : Miri.Input.CompilerLifecycle.Prepared) (lifecycle : CallMachine.Lifecycle K U C)
    (code : LoadedBody) (actual : Miri.Input.LoweredBody) (fnInstance : CallInstance)
    (destination : RuntimeStackPlace Provenance) (continuation : ReturnContinuation)
    (span : SpanRef) (identity : LocalsIdentity)
    (older : Array GuardFrame) (before fresh : MachineHooks.MachineState K U)
    (relevance : UInt8) (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (previous : GuardFrame)
    (freshId : lifecycle.freshLocalsIdentity before = (fresh, identity))
    (row : prepared.program.bundle.bodies[code.identity.index]? = some actual)
    (contents : actual.body = code.body)
    (evidence : prepared.entries[code.identity.index]? = some ⟨.ok span, .ok fnInstance⟩)
    (compilerRelevance : FrameMetadata.userRelevance lifecycle.compiler
      (Frame.create code fnInstance () continuation destination span identity)
      ⟨⟨older⟩, fresh⟩ = .ok relevance ⟨⟨older⟩, fresh⟩)
    (active : fresh.threads.activeThread? = some thread)
    (cached : FrameRelevance.top
      ⟨older.push (runtimeFrame code fnInstance destination continuation span identity fresh relevance)⟩
      thread.topUserRelevantFrame = some index)
    (selected : (older.push (runtimeFrame code fnInstance destination continuation span identity fresh relevance))[index]? =
      some previous) :
    let frame := runtimeFrame code fnInstance destination continuation span identity fresh relevance
    CallMachine.pushRaw (Miri.Input.CompilerLifecycle.hooks prepared lifecycle) false
      fnInstance code destination continuation (⟨⟨older⟩, before⟩ : MachineHooks.State K U) =
      .ok () (withFrame older frame (FrameRelevance.pushedMachine older frame previous fresh)) := by
  let frame := runtimeFrame code fnInstance destination continuation span identity fresh relevance
  have spanQuery := Miri.Input.CompilerLifecycle.preamble_known (K := K) (U := U)
    prepared code actual span fnInstance row contents evidence
  have constants := Miri.Input.CompilerLifecycle.required_empty prepared code actual span fnInstance
    row contents evidence older frame fresh (by rfl) (by rfl)
  have cache := FrameRelevance.afterPush_known older frame previous fresh thread index active cached selected
  change _ = EStateM.Result.ok () (withFrame older frame (FrameRelevance.pushedMachine older frame previous fresh))
  unfold CallMachine.pushRaw
  simp only [Miri.Input.CompilerLifecycle.hooks, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, freshId, spanQuery, MachineHooks.initFrame,
    compilerRelevance, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  simp only [withFrame, frame, runtimeFrame, Frame.create] at constants cache ⊢
  rw [constants]
  exact cache

/-- Compose the initializer's source stack operations on a prepared local
destination. Compiler return compatibility and local span queries remain
explicit. The initialized frame and its empty argument scope are derived. -/
theorem setupCanonicalRuntimeGuard
    {O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (fnInstance : CallInstance) (code : LoadedBody)
    (abi : FnAbi TyId) (dest : RuntimeStackPlace Provenance) (cont : ReturnContinuation)
    (before : MachineHooks.State K U)
    (older : Array GuardFrame) (frame : GuardFrame) (machine : MachineHooks.MachineState K U)
    (span localSpan : SpanRef) (operand : Immediate Provenance) (layout : LocalLayout)
    (locals : frame.locals = #[⟨.dead, none⟩]) (noClocks : frame.extra.dataRace = none)
    (location : frame.location = .unwinding span)
    (noCallerLocation : frame.trackCallerArg = none)
    (source : GeneratedBodySafety.input.document.bodies[19]?.map (·.mir) = some frame.body)
    (trivial : config.lifecycle.storage.veryTriviallySized 0 = .ok true)
    (args : abi.args.size = 0)
    (lookedUp : (ExecutionMachine.callHooks config limits).placeToOp choice dest before =
      .ok ⟨.immediate operand, layout⟩ before)
    (pushed : (ExecutionMachine.callHooks config limits).pushRaw choice fnInstance code dest cont before =
      .ok () (withFrame older frame machine))
    (locationQuery : (ExecutionMachine.callHooks config limits).localSpan code.body 0
      (withFrame older frame machine) = .ok localSpan (withFrame older frame machine))
    (returnABI : (ExecutionMachine.callHooks config limits).checkArgumentCompat choice abi.ret abi.ret
      (withFrame older {frame with location := .unwinding localSpan} machine) =
      .ok true (withFrame older {frame with location := .unwinding localSpan} machine)) :
    setupNoArguments (ExecutionMachine.callHooks config limits) choice fnInstance code abi dest cont before =
      .ok () (withFrame older {liveResult frame with location := .mir .start} machine) := by
  let hooks := ExecutionMachine.callHooks config limits
  have getEq : hooks.getFrame = MachineHooks.currentFrame := rfl
  have setEq : hooks.setFrame = MachineHooks.setCurrentFrame := rfl
  have retagEq : hooks.withRetagMode choice .FnEntry
      (pure (0, 0) : MachineHooks.M K U (Nat × Nat)) =
      pure (0, 0) := funext emptyArgumentScope
  have doneEq : hooks.pushDone choice = CallMachine.pushDone config.lifecycle := rfl
  have afterEq : hooks.afterFrameInit choice = pure () := rfl
  have retEq : hooks.abiReturn abi = abi.ret := rfl
  have argsEq : (hooks.abiArgs abi).size = 0 := args
  have ready := pushDoneRuntimeGuard config.lifecycle older frame machine source locals noClocks trivial
  have restored : {frame with location := .unwinding span} = frame := by rw [←location]
  have sameTrack : {frame with trackCallerArg := none} = frame := by rw [←noCallerLocation]
  change setupNoArguments hooks choice fnInstance code abi dest cont before = _
  change hooks.placeToOp choice dest before = _ at lookedUp
  change hooks.pushRaw choice fnInstance code dest cont before = _ at pushed
  change hooks.localSpan code.body 0 (withFrame older frame machine) = _ at locationQuery
  change hooks.checkArgumentCompat choice abi.ret abi.ret _ = _ at returnABI
  generalize hooks = driver at lookedUp pushed locationQuery returnABI getEq setEq retagEq doneEq afterEq retEq argsEq ⊢
  unfold setupNoArguments
  simp only [bind, Bind.bind, EStateM.bind, lookedUp, pushed,
    getEq, setEq, retagEq, retEq, doneEq, afterEq]
  rcases frame with ⟨body, identity, callee, extra, continuation, returnPlace, localsId,
    localSlots, vaList, track, pc⟩
  cases location
  cases noCallerLocation
  simp only [withFrame] at locationQuery returnABI ready
  simp [MachineHooks.currentFrame, MachineHooks.setCurrentFrame, withFrame, Stack.currentFrame?,
    get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    locationQuery, returnABI, ready, argsEq, requireGuard]

/-- Start the current retained guard through the actual call initializer.
All frame updates are derived from compiler evidence, the already evaluated
caller destination, and the machine's readonly control facts. -/
theorem enterCanonicalRuntimeGuard
    {O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (prepared : Miri.Input.CompilerLifecycle.Prepared) (lifecycle : CallMachine.Lifecycle K U C)
    (life : config.lifecycle = Miri.Input.CompilerLifecycle.hooks prepared lifecycle)
    (debug : config.compiler.debugAssertions = false)
    (choice : C) (fnInstance : CallInstance) (code : LoadedBody) (actual : Miri.Input.LoweredBody)
    (abi : FnAbi TyId) (dest : RuntimeStackPlace Provenance) (target : BasicBlockId)
    (older : Array GuardFrame) (before fresh : MachineHooks.MachineState K U)
    (preamble localSpan : SpanRef) (identity : LocalsIdentity) (relevance : UInt8)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (previous : GuardFrame)
    (operand : Immediate Provenance) (layout : LocalLayout)
    (source : GeneratedBodySafety.input.document.bodies[19]?.map (·.mir) = some code.body)
    (trivial : lifecycle.storage.veryTriviallySized 0 = .ok true)
    (noClocks : fresh.dataRace = none)
    (abiArgs : abi.args.size = 0) (variadic : abi.cVariadic = false)
    (lookedUp : (ExecutionMachine.callHooks config limits).placeToOp choice dest ⟨⟨older⟩, before⟩ =
      .ok ⟨.immediate operand, layout⟩ ⟨⟨older⟩, before⟩)
    (freshId : lifecycle.freshLocalsIdentity before = (fresh, identity))
    (row : prepared.program.bundle.bodies[code.identity.index]? = some actual)
    (contents : actual.body = code.body)
    (evidence : prepared.entries[code.identity.index]? = some ⟨.ok preamble, .ok fnInstance⟩)
    (compilerRelevance : FrameMetadata.userRelevance lifecycle.compiler
      (Frame.create code fnInstance () (.goto (some target) .Unreachable) dest preamble identity)
      ⟨⟨older⟩, fresh⟩ = .ok relevance ⟨⟨older⟩, fresh⟩)
    (active : fresh.threads.activeThread? = some thread) :
    let cont := ReturnContinuation.goto (some target) .Unreachable
    let frame := runtimeFrame code fnInstance dest cont preamble identity fresh relevance
    let machine := FrameRelevance.pushedMachine older frame previous fresh
    FrameRelevance.top ⟨older.push frame⟩ thread.topUserRelevantFrame = some index →
    (older.push frame)[index]? = some previous →
    (ExecutionMachine.callHooks config limits).requiresCallerLocation fnInstance = pure false →
    (ExecutionMachine.callHooks config limits).fnAbiOfInstance choice fnInstance #[] = pure abi →
    (ExecutionMachine.callHooks config limits).checkTargetFeatures choice fnInstance = pure () →
    (ExecutionMachine.callHooks config limits).nonCapturingClosure choice fnInstance abi = pure false →
    (ExecutionMachine.callHooks config limits).localSpan code.body 0 (withFrame older frame machine) =
      .ok localSpan (withFrame older frame machine) →
    (ExecutionMachine.callHooks config limits).checkArgumentCompat choice abi.ret abi.ret
      (withFrame older {frame with location := .unwinding localSpan} machine) =
      .ok true (withFrame older {frame with location := .unwinding localSpan} machine) →
    Call.initStackFrame (ExecutionMachine.callHooks config limits) choice fnInstance code abi #[]
      false dest cont (⟨⟨older⟩, before⟩ : MachineHooks.State K U) =
      .ok () (withFrame older {liveResult frame with location := .mir .start} machine) := by
  intro cont frame machine cached selected requires abiQuery feature closure spanQuery returnABI
  have noArgs : code.body.argumentCount = 0 := by
    have eq := congrArg (fun op : Option Body => op.map (·.argumentCount)) source
    exact Option.some.inj eq.symm
  have oneLocal : code.body.locals.size = 1 := by
    have eq := congrArg (fun op : Option Body => op.map (·.locals.size)) source
    exact Option.some.inj eq.symm
  have frameLocals : frame.locals = #[⟨.dead, none⟩] := by
    simp [frame, runtimeFrame, Frame.create, oneLocal]
  have frameClocks : frame.extra.dataRace = none := by simp [frame, runtimeFrame, Frame.create, noClocks]
  have pushed := pushRawRuntimeGuard prepared lifecycle code actual fnInstance dest cont preamble identity
    older before fresh relevance thread index previous freshId row contents evidence
    compilerRelevance active cached selected
  have canonicalPush : (ExecutionMachine.callHooks config limits).pushRaw choice fnInstance code dest cont
        ⟨⟨older⟩, before⟩ = .ok () (withFrame older frame machine) := by
    change CallMachine.pushRaw config.lifecycle config.compiler.debugAssertions fnInstance code dest cont
      ⟨⟨older⟩, before⟩ = _
    rw [life, debug]
    exact pushed
  have convention : (ExecutionMachine.callHooks config limits).sameConvention abi abi = true := by
    change (abi.conv == abi.conv) = true
    simp
  rw [initRuntimeGuard _ choice fnInstance code abi dest cont noArgs requires abiQuery feature closure
    variadic convention abiArgs]
  have normalized : (if (ExecutionMachine.callHooks config limits).abiCanUnwind abi then cont
      else match cont with
        | .stop _ => cont
        | .goto target _ => .goto target .Unreachable) = cont := by simp [cont]
  rw [normalized]
  have canonicalTrivial : config.lifecycle.storage.veryTriviallySized 0 = .ok true := by
    rw [life]
    exact trivial
  exact setupCanonicalRuntimeGuard config limits choice fnInstance code abi dest cont _ older frame machine
    preamble localSpan operand layout frameLocals frameClocks rfl rfl source canonicalTrivial
    abiArgs lookedUp canonicalPush spanQuery returnABI

/-- A resolved empty-argument Item takes one actual dispatch round.
The effect retains the selected loaded body and proceeds to the source
initializer. Panic-abort mismatch normalization is preserved. -/
theorem dispatchRuntimeGuard
    (hooks : Hooks) (choice : C) (fnInstance : CallInstance) (definition : DefId)
    (callerAbi : X) (abi : F) (destination : RuntimeStackPlace P) (target : BasicBlockId)
    (dispatchBudget : Nat) (before after : S)
    (code : LoadedBody)
    (kind : hooks.instanceKind fnInstance = pure (.Item definition))
    (resolved : hooks.findMirOrEvalFn choice fnInstance abi #[] destination (some target)
      .Unreachable before = .ok (some (code, fnInstance)) before)
    (initialized : Call.initStackFrame hooks choice fnInstance code abi #[] false destination
      (.goto (some target) .Unreachable) before = .ok () after) :
    Call.initFnCall hooks choice (dispatchBudget + 1)
      ⟨.Instance fnInstance, callerAbi, some abi, #[], false, destination, some target, .Unreachable⟩
      before = .ok () after := by
  unfold Call.initFnCall Call.initFnCallStep
  simp [kind, resolved, initialized, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

private def runtimeCallOperand : Miri.MIR.Operand :=
  .Constant ⟨⟨209⟩, none, .Val .ZeroSized 111⟩

private def runtimeCallDestination : Place := ⟨1, #[]⟩

/-- The actual retained helper call moves only its Boolean result slot. -/
theorem runtimeGuardCallCode :
    (do
      let body ← GeneratedBodySafety.input.document.bodies[9]?
      let block ← body.mir.basicBlocks[0]?
      pure block.terminator.kind) =
      some (.Call runtimeCallOperand #[] runtimeCallDestination (some 1)
        .Unreachable .Misc ⟨208⟩) := by
  rfl

/-- Connect the exported helper Call to the actual item dispatch. The
post-dispatch progress check observes the pushed frame rather than assuming
an accepted terminator. -/
theorem callRuntimeGuardTerminator
    {O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (term : Terminator) (fnInstance : CallInstance) (definition : DefId)
    (callerAbi : X) (abi : FnAbi TyId) (code : LoadedBody) (destination : RuntimeStackPlace Provenance)
    (budget : Nat) (before after : MachineHooks.State K U)
    (source : term.kind = .Call runtimeCallOperand #[] runtimeCallDestination (some 1)
      .Unreachable .Misc ⟨208⟩)
    (notEmpty : 0 < before.stack.frames.size)
    (depth : after.stack.frames.size = before.stack.frames.size + 1)
    (dest : (ExecutionMachine.callHooks config limits).evalPlace choice runtimeCallDestination false before =
      .ok destination before)
    (evaluation : Call.evalCalleeAndArgs (ExecutionMachine.callHooks config limits) choice
        runtimeCallOperand #[] runtimeCallDestination before =
      .ok ⟨.Instance fnInstance, #[], callerAbi, some abi, false⟩ before)
    (kind : (ExecutionMachine.callHooks config limits).instanceKind fnInstance = pure (.Item definition))
    (resolved : (ExecutionMachine.callHooks config limits).findMirOrEvalFn choice fnInstance abi #[]
      destination (some 1) .Unreachable before = .ok (some (code, fnInstance)) before)
    (initialized : Call.initStackFrame (ExecutionMachine.callHooks config limits) choice fnInstance
      code abi #[] false destination (.goto (some 1) .Unreachable) before = .ok () after) :
    Call.evalCallTerminator (ExecutionMachine.callHooks config limits) choice (budget+1) term before =
      .ok () after := by
  let hooks := ExecutionMachine.callHooks config limits
  have dispatched := dispatchRuntimeGuard hooks choice fnInstance definition callerAbi abi destination
    1 budget before after code kind resolved initialized
  have frameIndex : hooks.frameIndex = (do
      match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error)) := rfl
  have empty : hooks.stackIsEmpty = (return (← get).stack.frames.isEmpty) := rfl
  have frame : hooks.getFrame = MachineHooks.currentFrame := rfl
  have afterNonempty : 0 < after.stack.frames.size := by omega
  have beforeNonempty : before.stack.frames ≠ #[] := by
    intro h
    simp [h] at notEmpty
  have afterNonempty' : after.stack.frames ≠ #[] := by
    intro h
    simp [h] at afterNonempty
  have notEmpty' : before.stack.frames.isEmpty = false := by simp [beforeNonempty]
  have afterNotEmpty : after.stack.frames.isEmpty = false := by simp [afterNonempty']
  have distinct : after.stack.frames.size - 1 ≠ before.stack.frames.size - 1 := by omega
  obtain ⟨caller, callerEq⟩ : ∃ caller, before.stack.currentFrame? = some caller := by
    cases present : before.stack.currentFrame? with
    | some caller => exact ⟨caller, rfl⟩
    | none =>
      simp [Stack.currentFrame?, Array.back?_eq_none_iff, beforeNonempty] at present
  change Call.evalCallTerminator hooks choice (budget+1) term before = _
  change hooks.evalPlace choice runtimeCallDestination false before = _ at dest
  change Call.evalCalleeAndArgs hooks choice runtimeCallOperand #[] runtimeCallDestination before = _ at evaluation
  generalize hooks = driver at dispatched frameIndex empty frame dest evaluation ⊢
  simp [Call.evalCallTerminator, source, frameIndex, empty, frame, Stack.frameIndex,
    MachineHooks.currentFrame, callerEq, notEmpty', afterNotEmpty, afterNonempty', distinct,
    dest, evaluation, dispatched, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
    Except.pure, Except.bind]

/-- Operand, function-kind, and ABI queries are the only leaves of the
actual evaluation of the retained zero-argument function item. -/
theorem evalRuntimeGuardCallee
    (hooks : Hooks) (choice : C) (layout : LocalLayout)
    (fnInstance : CallInstance) (abi : F) (callerAbi : X)
    (operand : hooks.evalOperand choice runtimeCallOperand = pure ⟨.immediate .uninit, layout⟩)
    (signature : hooks.functionSignature choice layout = pure (0, callerAbi))
    (kind : hooks.functionKind layout.ty = pure (.FnDef 43 #[]))
    (resolved : hooks.resolve choice 43 #[] = pure fnInstance)
    (instanceKind : hooks.instanceKind fnInstance = pure (.Item 43))
    (calleeAbi : hooks.fnAbiOfInstance choice fnInstance #[] = pure abi)
    (track : hooks.requiresCallerLocation fnInstance = pure false) :
    Call.evalCalleeAndArgs hooks choice runtimeCallOperand #[] runtimeCallDestination =
      pure ⟨.Instance fnInstance, #[], callerAbi, some abi, false⟩ := by
  unfold Call.evalCalleeAndArgs
  unfold_call_helper "require"
  simp [operand, signature, kind, resolved, instanceKind, calleeAbi, track]

end DuplicatePrefix.LanguageGuardCall

#print axioms DuplicatePrefix.LanguageGuardCall.initRuntimeGuard
#print axioms DuplicatePrefix.LanguageGuardCall.pushDoneRuntimeGuard
#print axioms DuplicatePrefix.LanguageGuardCall.pushRawRuntimeGuard

#print axioms DuplicatePrefix.LanguageGuardCall.setupCanonicalRuntimeGuard

#print axioms DuplicatePrefix.LanguageGuardCall.enterCanonicalRuntimeGuard

#print axioms DuplicatePrefix.LanguageGuardCall.dispatchRuntimeGuard

#print axioms DuplicatePrefix.LanguageGuardCall.callRuntimeGuardTerminator

#print axioms DuplicatePrefix.LanguageGuardCall.runtimeGuardFunctionFacts
#print axioms DuplicatePrefix.LanguageGuardCall.evalRuntimeGuardCallee

import Representative
import Miri.Input.CompilerLifecycle
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

end DuplicatePrefix.LanguageGuardCall

#print axioms DuplicatePrefix.LanguageGuardCall.initRuntimeGuard
#print axioms DuplicatePrefix.LanguageGuardCall.pushDoneRuntimeGuard
#print axioms DuplicatePrefix.LanguageGuardCall.pushRawRuntimeGuard

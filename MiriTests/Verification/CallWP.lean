import Miri.Verification.CanonicalStepWP

namespace MiriTests.Verification.CallWP

open Miri.Interpreter Miri.MIR Miri.Memory Miri.Verification Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "State" => MachineHooks.State K U
local notation "MachineFrame" => Frame Provenance LocalLayout MachineHooks.FrameExtra

private abbrev calls (config : Config) (limits : ExecutionMachine.Limits) :=
  ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits

private theorem stepOfSelected (config : Config) (limits : ExecutionMachine.Limits)
    (before : State) (frame : MachineFrame) (loc : Location) (block : BasicBlock)
    (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (pc : frame.location = .mir loc) (selected : frame.body.basicBlocks[loc.block]? = some block)
    (slot : block.statements[loc.statementIndex]? = none)
    (prepared : let checked := ExecutionMachine.withValidation config limits
      TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()) before =
        .ok () before)
    (checked : CanonicalStepWP.selectedTerminatorPre config limits () block.terminator
      (post true) onError before) :
    Triple (StepWP.OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits)
      (allowed := fun _ _ => True)) (· = before) post onError := by
  vcgen
  rename_i state atEntry
  subst state
  intro choice _
  cases choice
  simpa only [CanonicalStepWP.choicePre, StepWP.driverChoicePreWith, current, pc, selected, slot,
    CanonicalStepWP.terminatorPre, ← RvalueWP.actionPre_eq_wp, RvalueWP.actionPre_ok prepared] using checked

/-- A failed return-place computation ends the call before callee evaluation.
The error continuation observes the state left by that computation. -/
theorem callDestinationFailure (config : Config) (limits : ExecutionMachine.Limits)
    (before failed : State) (frame : MachineFrame) (loc : Location) (block : BasicBlock)
    (func : Operand) (args : Array SpannedOperand) (dest : Place) (span : SpanRef)
    (error : StepError) (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (pc : frame.location = .mir loc) (selected : frame.body.basicBlocks[loc.block]? = some block)
    (slot : block.statements[loc.statementIndex]? = none)
    (opcode : block.terminator.kind = .Call func args dest (some 1) .Continue .Normal span)
    (prepared : let checked := ExecutionMachine.withValidation config limits
      TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()) before =
        .ok () before)
    (indexed : (calls config limits).frameIndex before = .ok (before.stack.frames.size - 1) before)
    (active : (calls config limits).getFrame before = .ok frame before)
    (rejected : (calls config limits).evalPlace () dest false before = .error error failed)
    (classified : onError error failed) :
    Triple (StepWP.OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits)
      (allowed := fun _ _ => True)) (· = before) post onError := by
  apply stepOfSelected config limits before frame loc block post onError current pc selected slot prepared
  simp only [CanonicalStepWP.selectedTerminatorPre, opcode, CallWP.callPre,
    RvalueWP.actionPre_ok indexed, RvalueWP.actionPre_ok active]
  simpa only [RvalueWP.actionPre, rejected] using classified

/-- The call budget is charged only once destination and callee evaluation
have completed. The exhaustion continuation sees their final state. -/
theorem callDispatchExhaustion (config : Config) (limits : ExecutionMachine.Limits)
    (before afterDest ready : State) (frame : MachineFrame) (loc : Location) (block : BasicBlock)
    (func : Operand) (args : Array SpannedOperand) (dest : Place) (span : SpanRef)
    (destination : RuntimeStackPlace Provenance) (evaluated : EvaluatedCall Provenance O X (Miri.ABI.FnAbi TyId))
    (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (pc : frame.location = .mir loc) (selected : frame.body.basicBlocks[loc.block]? = some block)
    (slot : block.statements[loc.statementIndex]? = none)
    (opcode : block.terminator.kind = .Call func args dest (some 1) .Continue .Normal span)
    (prepared : let checked := ExecutionMachine.withValidation config limits
      TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()) before =
        .ok () before)
    (indexed : (calls config limits).frameIndex before = .ok (before.stack.frames.size - 1) before)
    (active : (calls config limits).getFrame before = .ok frame before)
    (place : (calls config limits).evalPlace () dest false before = .ok destination afterDest)
    (read : Call.evalCalleeAndArgs (calls config limits) () func args dest afterDest = .ok evaluated ready)
    (budget : limits.callDispatch = 0)
    (classified : onError (.resourceExhaustion "call dispatch budget exhausted") ready) :
    Triple (StepWP.OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits)
      (allowed := fun _ _ => True)) (· = before) post onError := by
  apply stepOfSelected config limits before frame loc block post onError current pc selected slot prepared
  simpa only [CanonicalStepWP.selectedTerminatorPre, opcode, CallWP.callPre,
    RvalueWP.actionPre_ok indexed, RvalueWP.actionPre_ok active, RvalueWP.actionPre_ok place,
    RvalueWP.actionPre_ok read, budget, CallWP.dispatchPre] using classified

/-- A root tail call rejects after the raw pop. Dispatch and detached-frame
cleanup are skipped, and the error handler receives the state after the pop. -/
theorem tailCallRootFailure (config : Config) (limits : ExecutionMachine.Limits)
    (before ready afterPop : State) (frame : MachineFrame) (loc : Location) (block : BasicBlock)
    (func : Operand) (args : Array SpannedOperand) (span : SpanRef) (cleanup : Bool)
    (evaluated : EvaluatedCall Provenance O X (Miri.ABI.FnAbi TyId))
    (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (pc : frame.location = .mir loc) (selected : frame.body.basicBlocks[loc.block]? = some block)
    (slot : block.statements[loc.statementIndex]? = none)
    (opcode : block.terminator.kind = .TailCall func args span)
    (prepared : let checked := ExecutionMachine.withValidation config limits
      TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()) before =
        .ok () before)
    (indexed : (calls config limits).frameIndex before = .ok (before.stack.frames.size - 1) before)
    (read : Call.evalCalleeAndArgs (calls config limits) () func args ⟨0, #[]⟩ before = .ok evaluated ready)
    (popped : (calls config limits).popRaw () ready = .ok frame afterPop)
    (root : frame.returnContinuation = .stop cleanup)
    (classified : onError (.invalidProgram "cannot tailcall as root of stack") afterPop) :
    Triple (StepWP.OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits)
      (allowed := fun _ _ => True)) (· = before) post onError := by
  apply stepOfSelected config limits before frame loc block post onError current pc selected slot prepared
  simpa only [CanonicalStepWP.selectedTerminatorPre, opcode, CallWP.tailCallPre, CallWP.tailDispatchPre,
    RvalueWP.actionPre_ok indexed, RvalueWP.actionPre_ok read, RvalueWP.actionPre_ok popped, root] using classified

/-- A direct item call with no arguments resolves its operand and compiler
queries, prepares the callee frame, and passes the progress guard. -/
theorem callDirectItem (config : Config) (limits : ExecutionMachine.Limits)
    (before ready entered : State) (frame : MachineFrame) (loc : Location) (block : BasicBlock)
    (func : Operand) (dest : Place) (span : SpanRef) (remaining : Nat)
    (destination : RuntimeStackPlace Provenance) (operand : OpTy Provenance)
    (definition itemDef : DefId) (genericArgs : Array GenericArg) (fnInstance loadedInstance : CallInstance)
    (externAbi : X) (abi : Miri.ABI.FnAbi TyId) (body : LoadedBody)
    (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (pc : frame.location = .mir loc) (selected : frame.body.basicBlocks[loc.block]? = some block)
    (slot : block.statements[loc.statementIndex]? = none)
    (opcode : block.terminator.kind = .Call func #[] dest (some 1) .Unreachable .Normal span)
    (prepared : let checked := ExecutionMachine.withValidation config limits
      TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice ()) before =
        .ok () before)
    (indexed : (calls config limits).frameIndex before = .ok (before.stack.frames.size - 1) before)
    (active : (calls config limits).getFrame before = .ok frame before)
    (place : (calls config limits).evalPlace () dest false before = .ok destination ready)
    (read : (calls config limits).evalOperand () func ready = .ok operand ready)
    (signature : (calls config limits).functionSignature () operand.layout ready = .ok (0, externAbi) ready)
    (kind : (calls config limits).functionKind operand.layout.ty ready =
      .ok (.FnDef definition genericArgs) ready)
    (resolved : (calls config limits).resolve () definition genericArgs ready = .ok fnInstance ready)
    (item : (calls config limits).instanceKind fnInstance ready = .ok (.Item itemDef) ready)
    (computed : (calls config limits).fnAbiOfInstance () fnInstance #[] ready = .ok abi ready)
    (location : (calls config limits).requiresCallerLocation fnInstance ready = .ok false ready)
    (ordinary : (calls config limits).isRustCall externAbi = false)
    (found : (calls config limits).findMirOrEvalFn () fnInstance abi #[] destination (some 1) .Unreachable ready =
      .ok (some (body, loadedInstance)) ready)
    (initialized : Call.initStackFrame (calls config limits) () loadedInstance body abi #[] false destination
      (.goto (some 1) .Unreachable) ready = .ok () entered)
    (notEmpty : (calls config limits).stackIsEmpty entered = .ok false entered)
    (nextIndex : (calls config limits).frameIndex entered = .ok before.stack.frames.size entered)
    (advanced : entered.stack.frames.size = before.stack.frames.size + 1)
    (positive : 0 < before.stack.frames.size)
    (budget : limits.callDispatch = remaining + 1)
    (success : post true entered) :
    Triple (StepWP.OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits)
      (allowed := fun _ _ => True)) (· = before) post onError := by
  apply stepOfSelected config limits before frame loc block post onError current pc selected slot prepared
  have evaluated := CallWP.evalNoArgsItem (calls config limits) () func dest ready ready ready ready ready ready ready
    ready operand externAbi definition genericArgs fnInstance itemDef abi false read signature kind resolved
    item computed location
  simp only [CanonicalStepWP.selectedTerminatorPre, opcode, CallWP.callPre,
    RvalueWP.actionPre_ok indexed, RvalueWP.actionPre_ok active, RvalueWP.actionPre_ok place,
    RvalueWP.actionPre_ok evaluated, budget, ite_self]
  let request : CallRequest Provenance O X (Miri.ABI.FnAbi TyId) :=
    ⟨.Instance fnInstance, externAbi, some abi, #[], false, destination, some 1, .Unreachable⟩
  have direct (finish : State → Prop) :=
    CallWP.dispatchPre_item (calls config limits) () remaining request finish onError ready ready ready
      fnInstance loadedInstance itemDef body abi rfl rfl item ordinary (by simpa only [request, ite_self] using found)
  rw [direct]
  have progress : (before.stack.frames.size == before.stack.frames.size - 1) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  have moved : (entered.stack.frames.size == before.stack.frames.size) = false :=
    beq_eq_false_iff_ne.mpr (by omega)
  simp only [request, ite_self, RvalueWP.actionPre_ok initialized, RvalueWP.actionPre_ok notEmpty,
    RvalueWP.actionPre_ok nextIndex, Bool.false_eq_true, ↓reduceIte, progress, moved,
    Option.isSome_some, Bool.true_and, Bool.false_and]
  exact success

/-- The ordinary by-value arm checks ABI compatibility, allocates the local
if needed, and copies the argument to the resolved destination. -/
theorem passArgumentCopy (config : Config) (limits : ExecutionMachine.Limits)
    (source : OpTy Provenance) (callerAbi calleeAbi : Miri.ABI.ArgAbi TyId) (calleeIndex : Nat)
    (localId : LocalId) (calleeTy : TyId) (dest : RuntimeStackPlace Provenance)
    (before checked live projected after : State) (post : Unit → State → Prop)
    (onError : StepError → State → Prop)
    (calleeLayout : (calleeTy == ((calls config limits).argLayout calleeAbi).ty) = true)
    (callerLayout : (source.layout.layout == ((calls config limits).argLayout callerAbi).layout) = true)
    (compatible : (calls config limits).checkArgumentCompat () callerAbi calleeAbi before = .ok true checked)
    (metadata : source.metadata.hasMeta = false)
    (storage : (calls config limits).storageLiveDyn () localId source.metadata checked = .ok () live)
    (place : (calls config limits).evalPlace () ⟨localId, #[]⟩ false live = .ok dest projected)
    (copied : (calls config limits).copyAllowTransmute () source dest projected = .ok () after)
    (success : post () after) :
    Triple (Call.passArgument (calls config limits) () (.Copy source) callerAbi calleeAbi
      calleeIndex ⟨localId, #[]⟩ calleeTy false) (· = before) post onError := by
  vcgen
  subst_vars
  simpa only [CallWP.passArgumentPre, FnArg.layout, FnArg.copyFnArg, bne, calleeLayout, callerLayout,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Array.isEmpty_empty, metadata, Bool.false_and,
    RvalueWP.actionPre_ok compatible, RvalueWP.actionPre_ok storage, RvalueWP.actionPre_ok place,
    RvalueWP.actionPre_ok copied] using success

/-- ABI rejection uses the state left by the compatibility query, before
allocating or writing the argument destination. -/
theorem passArgumentAbiMismatch (config : Config) (limits : ExecutionMachine.Limits)
    (caller : FnArg Provenance) (callerAbi calleeAbi : Miri.ABI.ArgAbi TyId) (calleeIndex : Nat)
    (dest : Place) (calleeTy : TyId) (alreadyLive : Bool) (before checked : State)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (calleeLayout : (calleeTy == ((calls config limits).argLayout calleeAbi).ty) = true)
    (callerLayout : (caller.layout.layout == ((calls config limits).argLayout callerAbi).layout) = true)
    (compatible : (calls config limits).checkArgumentCompat () callerAbi calleeAbi before = .ok false checked)
    (rejected : onError (.undefinedBehavior s!"AbiMismatchArgument {calleeIndex}") checked) :
    Triple (Call.passArgument (calls config limits) () caller callerAbi calleeAbi
      calleeIndex dest calleeTy alreadyLive) (· = before) post onError := by
  vcgen
  subst_vars
  simpa only [CallWP.passArgumentPre, bne, calleeLayout, callerLayout,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, RvalueWP.actionPre_ok compatible]
    using rejected

/-- A mismatched caller-location contract rejects at the state returned by the
compiler query, before ABI lookup or a raw frame push. -/
theorem frameCallerLocationMismatch (config : Config) (limits : ExecutionMachine.Limits)
    (fnInstance : CallInstance) (body : LoadedBody) (abi : Miri.ABI.FnAbi TyId)
    (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation)
    (before queried : State) (post : State → Prop) (onError : StepError → State → Prop)
    (queriedLocation : (calls config limits).requiresCallerLocation fnInstance before = .ok true queried) :
    wp (Call.initStackFrame (calls config limits) () fnInstance body abi #[] false destination cont)
      (fun _ => post) onError before ↔
      onError (.undefinedBehavior "caller/callee #[track_caller] mismatch") queried := by
  rw [← CallWP.initStackFramePre_eq_wp]
  simp only [CallWP.initStackFramePre, RvalueWP.actionPre_ok queriedLocation]
  rfl

/-- Running out of caller operands reports UB before attempting to read the
caller ABI table. The selected callee ABI must already exist. -/
theorem ordinaryArgumentMissing (config : Config) (limits : ExecutionMachine.Limits)
    (callerAbis calleeAbis : Array (Miri.ABI.ArgAbi TyId)) (calleeAbi : Miri.ABI.ArgAbi TyId)
    (dest : Place) (ty : TyId) (before : State) (post : State → Prop) (onError : StepError → State → Prop)
    (selected : calleeAbis[0]? = some calleeAbi) :
    wp (Call.initOrdinaryArgument (calls config limits) () #[] callerAbis calleeAbis 0 0 dest ty)
      (fun _ => post) onError before ↔
      onError (.undefinedBehavior "calling a function with fewer arguments than it requires") before := by
  rw [← CallWP.ordinaryArgumentPre_eq_wp]
  simp only [CallWP.ordinaryArgumentPre, selected, Array.getElem?_empty]

/-- Successful completion of a frame with an indirect return place includes
return protection, restoration of the preamble span and publication. -/
theorem frameFinishIndirect (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (abi : Miri.ABI.FnAbi TyId) (destination : MPlaceTy Provenance)
    (preamble returnSpan : SpanRef) (before spanRead inReturn checked afterProtect restored initialized done : State)
    (post : State → Prop) (onError : StepError → State → Prop)
    (span : (calls config limits).localSpan body 0 before = .ok returnSpan spanRead)
    (returnLocation : Call.setSpan (calls config limits) returnSpan spanRead = .ok () inReturn)
    (compatible : (calls config limits).checkArgumentCompat () ((calls config limits).abiReturn abi)
      ((calls config limits).abiReturn abi) inReturn = .ok true checked)
    (protect : (calls config limits).protectArgument () destination checked = .ok () afterProtect)
    (restore : Call.setSpan (calls config limits) preamble afterProtect = .ok () restored)
    (initializedFrame : (calls config limits).afterFrameInit () restored = .ok () initialized)
    (publish : (calls config limits).pushDone () initialized = .ok () done) :
    wp (Call.finishFrameInit (calls config limits) () body abi abi #[] false #[]
      ⟨.indirect destination.mplace, destination.layout⟩ preamble (0, 0))
      (fun _ => post) onError before ↔ post done := by
  rw [← RvalueWP.actionPre_eq_wp, ← CallWP.finishFramePre_eq_actionPre]
  simp only [CallWP.finishFramePre, CallWP.setSpanPre_eq_actionPre,
    RvalueWP.actionPre_ok span, RvalueWP.actionPre_ok returnLocation, RvalueWP.actionPre_ok compatible,
    RvalueWP.actionPre_ok protect, RvalueWP.actionPre_ok restore]
  simp [RvalueWP.actionPre_ok initializedFrame, RvalueWP.actionPre_ok publish]

/-- A failing argument traversal restores the caller's retag mode in the
state returned to its error continuation. Other effects of the traversal
are taken from the actual failure state. -/
theorem frameArgumentsRestoreOnError (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (args : Array (FnArg Provenance))
    (callerAbis calleeAbis : Array (Miri.ABI.ArgAbi TyId))
    (before failed : State) (tracker afterTracker : MachineHooks.BorrowState) (error : StepError)
    (post : (Nat × Nat) → State → Prop) (onError : StepError → State → Prop)
    (tracking : before.machine.borrowTracker = some tracker)
    (failure : Call.initFrameArgumentsBody (calls config limits) () body false none args callerAbis calleeAbis
      { before with machine.borrowTracker := some { tracker with retagMode := .FnEntry } } =
        .error error failed)
    (failedTracking : failed.machine.borrowTracker = some afterTracker) :
    wp (Call.initFrameArguments (calls config limits) () body false none args callerAbis calleeAbis) post onError before ↔
      onError error
        { failed with machine.borrowTracker := some { afterTracker with retagMode := tracker.retagMode } } := by
  rw [← RvalueWP.actionPre_eq_wp, CallWP.canonicalFrameArgumentsPre]
  simp only [RvalueWP.retagModePre, tracking, RvalueWP.actionPre, failure]
  change (match failed.machine.borrowTracker with
    | none => onError (.invalidProgram "borrow tracker removed during retag mode scope") failed
    | some tracked => onError error
        { failed with machine.borrowTracker := some { tracked with retagMode := tracker.retagMode } }) ↔ _
  rw [failedTracking]

/-- A closure self argument sharing the variadic slot rejects after
diagnostics and layout lookup for the selected local. -/
theorem closureVariadicArgumentConflict (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (args : Array (FnArg Provenance)) (callerAbis calleeAbis : Array (Miri.ABI.ArgAbi TyId))
    (before spanRead located queried : State) (span : SpanRef) (layout : LocalLayout)
    (post : (Nat × Nat) → State → Prop) (onError : StepError → State → Prop)
    (count : body.argumentCount = 1)
    (foundSpan : (calls config limits).localSpan body 1 before = .ok span spanRead)
    (setLocation : Call.setSpan (calls config limits) span spanRead = .ok () located)
    (foundLayout : (calls config limits).localLayout () 1 located = .ok layout queried) :
    wp (Call.initFrameArgumentsBody (calls config limits) () body true (some 1) args callerAbis calleeAbis)
      post onError before ↔
      onError (.invalidProgram "special closure argument conflict") queried := by
  rw [← RvalueWP.actionPre_eq_wp, ← CallWP.frameArgumentsBodyPre_eq_actionPre]
  simp [count, CallWP.frameArgumentsFoldPre, Call.initFrameArgumentStep, Call.require_eq,
    RvalueWP.actionPre_bind_fun, RvalueWP.actionPre_ok foundSpan, RvalueWP.actionPre_ok setLocation,
    RvalueWP.actionPre_ok foundLayout, RvalueWP.actionPre_throw]

#print axioms closureVariadicArgumentConflict

#print axioms frameArgumentsRestoreOnError

#print axioms frameCallerLocationMismatch
#print axioms ordinaryArgumentMissing
#print axioms frameFinishIndirect

#print axioms callDestinationFailure
#print axioms callDispatchExhaustion
#print axioms tailCallRootFailure
#print axioms callDirectItem
#print axioms passArgumentCopy
#print axioms passArgumentAbiMismatch

end MiriTests.Verification.CallWP

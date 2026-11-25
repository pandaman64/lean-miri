import Generated

/-! Discharge the imported callee's assignment of the literal return value
to its live immediate slot. -/
namespace CalleeSummaryExample

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification
open GeneratedBodySafety

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "State" => MachineHooks.State K U
local notation "Limits" => ExecutionMachine.Limits
local notation "MachineFrame" => Frame Provenance LocalLayout MachineHooks.FrameExtra
local notation "Machine" => MachineHooks.MachineState K U

private def seven : Immediate Provenance := .scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 7))

private def resultLiteral : ConstOperand :=
  match mir_1_bb0_1 with
  | .statement (.Assign _ (.Use (.Constant literal) _)) => literal
  | _ => ⟨⟨0⟩, none, .Val .ZeroSized 0⟩

private theorem assignNode :
    mir_1_bb0_1 = .statement (.Assign ⟨0, #[]⟩ (.Use (.Constant resultLiteral) .Yes)) := by rfl

private def current (frames : Array MachineFrame) (frame : MachineFrame) (machine : Machine) : State :=
  ⟨⟨frames.push frame⟩, machine⟩

omit [DecidableEq K] in
@[simp] private theorem current_frame (frames : Array MachineFrame) (frame : MachineFrame) (machine : Machine) :
    (current frames frame machine).stack.currentFrame? = some frame := by
  simp [current, Stack.currentFrame?]

private def inDefault (machine : Machine) : Machine :=
  {machine with borrowTracker := machine.borrowTracker.map fun tracker => {tracker with retagMode := .Default}}

omit [DecidableEq K] in
/-- In the source's non-debug constant branch, the imported scalar literal
requires no compiler callback or memory access once its layout is known. -/
theorem evalResultLiteral {Other : Type} (runtime : Miri.Input.RuntimeMetadata)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (external : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError) (layout : LocalLayout) (before : State) :
    ConstantMachine.evalOperandWithLayout runtime functions arithmetic external classify resultLiteral
      (some layout) none before = .ok ⟨.immediate seven, layout⟩ before := by
  have value : resultLiteral.value = .Val (.Scalar (.Int 7 1)) 3 := by rfl
  rw [ConstantMachine.evalOperandWithLayout, value]
  rfl

/-- The optimized slot update preserves caller memory and the borrow tracker.
Only the scalar literal and typed-layout checks cross the compiler boundary.
This rule uses a cached return layout and the profile with validation disabled. -/
theorem assignResultPre (config : Config) (limits : Limits)
    (frames : Array MachineFrame) (frame updated : MachineFrame) (machine : Machine)
    (layout : LocalLayout) (slot : LocalState Provenance LocalLayout) (old : Immediate Provenance)
    (post : Bool → State → Prop) (failure : StepError → State → Prop)
    (atResult : frame.location = .mir ⟨0, 1⟩)
    (slotAt : frame.getLocal 0 = .ok slot) (cached : slot.layout = some layout)
    (loaded : frame.getLocalOperand 0 = .ok (.immediate old))
    (sized : layout.layout.isSized = true) (debugOff : config.projection.place.debugAssertions = false)
    (noLocalClocks : frame.extra.dataRace = none)
    (replace : frame.setLocalOperand 0 (.immediate seven) = .ok updated)
    (frameBinding : config.projection.place.getFrame = MachineHooks.currentFrame)
    (indexBinding : config.projection.place.frameIndex = (do match (← get).stack.frameIndex with
      | .ok i => pure i | .error e => throw (.stack e)))
    (typeCheck : config.projection.place.checkPlaceType () ⟨0, #[]⟩
      ⟨.local frames.size 0 none frame.localsIdentity, layout⟩ (current frames frame machine) =
      .ok () (current frames frame machine))
    (literal : config.operands.constant () resultLiteral (some layout) (current frames frame machine) =
      .ok ⟨.immediate seven, layout⟩ (current frames frame machine))
    (compatible : config.copy.compatible layout layout = .ok true)
    (padding : config.copy.hasPadding layout = .ok false)
    (noTouch : config.access.retainTouched (inDefault machine) none = inDefault machine)
    (localWriteBinding : config.projection.place.writeLocalImmediate () 0 layout seven =
      placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
        config.compiler.validationInProgress MachineHooks.afterLocalWrite config.compiler.debugAbiCheck
        0 layout seven)
    (debugAbi : config.compiler.debugAbiCheck seven layout (current frames updated (inDefault machine)) =
      .ok () (current frames updated (inDefault machine)))
    (validation : ∃ inProgress : Bool,
      config.compiler.validationInProgress (current frames updated (inDefault machine)) =
        .ok inProgress (current frames updated (inDefault machine)))
    (enforce : config.projection.place.enforceValidity () layout (current frames updated (inDefault machine)) =
      .ok false (current frames updated (inDefault machine))) :
    (transfer_1_bb0_1 config limits).pre () post failure (current frames frame machine) ↔
      post true (current frames {updated with location := .mir ⟨0, 2⟩} machine) := by
  have unchanged : updated.location = frame.location ∧ updated.extra = frame.extra := by
    simp only [Frame.setLocalOperand, loaded, Frame.replaceLocalValue] at replace
    split at replace
    · cases replace
      exact ⟨rfl, rfl⟩
    · contradiction
  rw [(transfer_1_bb0_1 config limits).exact]
  change BodyCFG.nodePre config limits () post failure _ mir_1_bb0_1 ↔ _
  rw [assignNode]
  unfold BodyCFG.nodePre CanonicalStepWP.statementPre RvalueWP.evalPre
  dsimp only
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  let dest : RuntimePlace Provenance := ⟨.local frames.size 0 none frame.localsIdentity, layout⟩
  have readFrame (m : Machine) (f : MachineFrame) :
      hooks.getFrame (current frames f m) = .ok f (current frames f m) := by
    change config.projection.place.getFrame _ = _
    rw [frameBinding]
    simp [MachineHooks.currentFrame, bind, Bind.bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure]
  have index (m : Machine) (f : MachineFrame) :
      hooks.frameIndex (current frames f m) = .ok frames.size (current frames f m) := by
    change config.projection.place.frameIndex _ = _
    rw [indexBinding]
    simp [Stack.frameIndex, Except.pure, current, bind, Bind.bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure]
  have evaluated : PlaceDynamic.evalPlace
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
      () ⟨0, #[]⟩ true (current frames frame machine) = .ok dest (current frames frame machine) := by
    have checked : hooks.checkPlaceType () ⟨0, #[]⟩ dest (current frames frame machine) =
        .ok () (current frames frame machine) := typeCheck
    unfold PlaceDynamic.evalPlace
    simp only [show (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place =
      hooks from rfl, localToPlace, placeLayoutOfLocal, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure, readFrame, slotAt, stackLift_ok, cached, sized,
      ↓reduceIte, index, ← Array.forIn_toList, List.forIn_nil]
    simp [show (#[] == #[ProjectionElem.Deref]) = false by rfl, dest, checked, EStateM.bind, EStateM.pure]
  have executed : ((ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits).evalPlace
      () ⟨0, #[]⟩ true) (current frames frame machine) = .ok dest (current frames frame machine) := evaluated
  rw [RvalueWP.actionPre_ok executed]
  have readLiteral : ((ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits).evalOperand
      () (.Constant resultLiteral) (some layout)) (current frames frame machine) =
        .ok ⟨.immediate seven, layout⟩ (current frames frame machine) := literal
  change RvalueWP.actionPre _ _ _ _ ↔ _
  simp only [show (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits).placeLayout dest =
    layout from rfl, RvalueWP.actionPre_ok readLiteral]
  have writeLocal : hooks.writeLocalImmediate () 0 layout seven (current frames frame (inDefault machine)) =
      .ok () (current frames updated (inDefault machine)) := by
    change config.projection.place.writeLocalImmediate () 0 layout seven _ = _
    rw [localWriteBinding]
    obtain ⟨active, validation⟩ := validation
    have frameRead₀ : MachineHooks.currentFrame (current frames frame (inDefault machine)) =
        .ok frame (current frames frame (inDefault machine)) := by
      simpa only [hooks, ExecutionMachine.projectionHooks, ExecutionMachine.withValidation, frameBinding] using readFrame (inDefault machine) frame
    have frameRead₁ : MachineHooks.currentFrame (current frames updated (inDefault machine)) =
        .ok updated (current frames updated (inDefault machine)) := by
      simpa only [hooks, ExecutionMachine.projectionHooks, ExecutionMachine.withValidation, frameBinding] using readFrame (inDefault machine) updated
    have put : MachineHooks.setCurrentFrame updated (current frames frame (inDefault machine)) =
        .ok () (current frames updated (inDefault machine)) := by
      simp [MachineHooks.setCurrentFrame, current, get, getThe, MonadStateOf.get, EStateM.get,
        set, MonadStateOf.set, EStateM.set, bind, Bind.bind, EStateM.bind]
    cases active <;> simp [placeWriteLocalImmediate, sized, frameRead₀, loaded, replace, put, validation,
      MachineHooks.afterLocalWrite, frameRead₁, unchanged.2, noLocalClocks, debugAbi, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
  have copied : copyRuntimePlace hooks (ExecutionMachine.withValidation config limits).copy ()
      ⟨.immediate seven, layout⟩ dest false (current frames frame (inDefault machine)) =
        .ok () (current frames updated (inDefault machine)) := by
    have readRaw : PlaceMachine.readRaw config.access ⟨.immediate seven, layout⟩
        (current frames frame (inDefault machine)) =
        .ok (.immediate ⟨seven, localMemoryLayout layout⟩) (current frames frame (inDefault machine)) := by
      simp [PlaceMachine.readRaw, readImmediateRaw, PlaceMachine.commit, PlaceMachine.finish, Id.run,
        noTouch, current, get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet,
        MonadStateOf.modifyGet, EStateM.modifyGet, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    have debug : hooks.debugAssertions = false := debugOff
    have enforced : hooks.enforceValidity () layout (current frames updated (inDefault machine)) =
        .ok false (current frames updated (inDefault machine)) := enforce
    have raw : (ExecutionMachine.withValidation config limits).copy.readRaw () ⟨.immediate seven, layout⟩
        (current frames frame (inDefault machine)) =
        .ok (.immediate ⟨seven, localMemoryLayout layout⟩) (current frames frame (inDefault machine)) := readRaw
    have compat : (ExecutionMachine.withValidation config limits).copy.compatible layout layout = .ok true := compatible
    have pad : (ExecutionMachine.withValidation config limits).copy.hasPadding layout = .ok false := padding
    simp [copyRuntimePlace, copyRuntimePlaceNoValidate, dest, compat, pad, raw,
      writePlaceImmediateNoValidate, asMplaceOrMutableLocal, requireCurrent_eq,
      debug, readFrame, index, loaded, sized, writeLocal, enforced,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  have withMode : MachineHooks.withRetagMode .Default
      (copyRuntimePlace hooks (ExecutionMachine.withValidation config limits).copy ()
        ⟨.immediate seven, layout⟩ dest false) (current frames frame machine) =
      .ok () (current frames updated machine) := by
    cases tracking : machine.borrowTracker with
    | none =>
      have unchanged : inDefault machine = machine := by
        simp [inDefault, tracking]
        rw [← tracking]
      simpa [MachineHooks.withRetagMode, current, tracking, unchanged] using copied
    | some tracker =>
      have entered : inDefault machine = {machine with borrowTracker := some {tracker with retagMode := .Default}} := by
        simp [inDefault, tracking]
      have restored : {machine with borrowTracker := some tracker} = machine := by
        rw [←tracking]
      simp only [MachineHooks.withRetagMode, current, tracking, ← entered]
      rw [show copyRuntimePlace hooks (ExecutionMachine.withValidation config limits).copy ()
        ⟨.immediate seven, layout⟩ dest false ⟨⟨frames.push frame⟩, inDefault machine⟩ =
        .ok () ⟨⟨frames.push updated⟩, inDefault machine⟩ from copied]
      simp [entered, restored]
  have copiedInScope : (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits).withRetagMode
      () .Default ((ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits).copyOp ()
        ⟨.immediate seven, layout⟩ dest) (current frames frame machine) =
      .ok () (current frames updated machine) := withMode
  simp only [beq_self_eq_true, ↓reduceIte, RvalueWP.actionPre_ok copiedInScope]
  simp [InstructionWP.finishStatementResultPre, current, Stack.currentFrame?, atResult, unchanged.1, Array.set_push]


#print axioms evalResultLiteral
#print axioms assignResultPre

end CalleeSummaryExample

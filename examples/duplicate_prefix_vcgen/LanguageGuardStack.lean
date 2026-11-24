import Representative
import Miri.Verification.StepWP
import Miri.Interpreter.ValidityMachine
import empty_function.FrameExit

namespace DuplicatePrefix.LanguageGuardStack

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
open EmptyFunction.FrameExit

set_option maxRecDepth 65536

/-- The imported runtime guard's Return is in a normal block at index 1. -/
theorem runtimeBodyReturn :
    (do
      let body ← GeneratedBodySafety.input.document.bodies[19]?
      let block ← body.mir.basicBlocks[0]?
      pure (block.statements.size, block.cleanup, block.terminator.kind)) =
      some (1, false, .Return) := by
  rfl

/-- Pointer `add` calls the language guard through the current instance
table. After the guard returns false, the zero case jumps directly to bb5. -/
theorem pointerAddGuardBinding :
    (do
      let body ← GeneratedBodySafety.input.document.bodies[4]?
      let evidence ← body.callEvidence[0]?.join
      evidence.instanceId) = some 9 ∧
    (do
      let body ← GeneratedBodySafety.input.document.bodies[4]?
      let block ← body.mir.basicBlocks[1]?
      match block.terminator.kind with
      | .SwitchInt _ targets => some targets
      | _ => none) = some ⟨#[.Case 0 5], 2⟩ := by
  exact ⟨rfl, rfl⟩

theorem pointerAddOffsetAfterGuard :
    (do
      let body ← GeneratedBodySafety.input.document.bodies[4]?
      let guard ← body.mir.basicBlocks[5]?
      let offset ← body.mir.basicBlocks[6]?.bind (fun block => block.statements[6]?)
      return (guard.terminator.kind, offset.kind)) =
    some (.Goto 6 #[], .Assign ⟨0, #[]⟩
      (.BinaryOp .Offset (.Move ⟨10, #[]⟩) (.Move ⟨11, #[]⟩))) := by
  rfl

variable {K U C Other : Type}
local notation "State" => MachineHooks.State K U

def falseSlot (layout : LocalLayout) : LocalState Provenance LocalLayout :=
  ⟨.live (.immediate (.scalar (Scalar.fromBool false))), some layout⟩

private theorem falseSlotRead (frame : F) (layout : LocalLayout)
    (locals : frame.locals = #[falseSlot layout]) :
    frame.getLocal 0 = .ok (falseSlot layout) ∧
    frame.getLocalOperand 0 = .ok (.immediate (.scalar (Scalar.fromBool false))) := by
  have slot : frame.getLocal 0 = .ok (falseSlot layout) := by
    simp [Frame.getLocal, locals, pure, Pure.pure, Except.pure]
  refine ⟨slot, ?_⟩
  simp [Frame.getLocalOperand, slot, falseSlot, LocalState.access, bind, Bind.bind,
    Except.bind, Except.mapError]

/-- The actual local read on Return uses the cached Boolean layout. No
compiler lookup or memory read occurs for an immediate return local. -/
theorem readReturnFalse (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (older : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (locals : frame.locals = #[falseSlot layout])
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (validation : ∀ state, ∃ flag, compiler.validationInProgress state = .ok flag state) :
    PlaceMachine.localToOp compiler choice 0 (withCurrent older frame machine) =
      .ok ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ (withCurrent older frame machine) := by
  obtain ⟨slot, operand⟩ := falseSlotRead frame layout locals
  obtain ⟨flag, check⟩ := validation (withCurrent older frame machine)
  simp only [withCurrent] at check
  cases flag <;> simp [PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
    MachineHooks.currentFrame, Stack.currentFrame?, withCurrent, slot, operand,
    falseSlot, sized, noClocks, check, MachineHooks.afterLocalRead,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]

/-- Cleanup of the actual Boolean helper frame has no stack allocation to
deallocate. Normal return invokes the production after-pop rule. -/
theorem cleanupRuntimeGuard (lifecycle : CallMachine.Lifecycle K U C)
    (hooks : Unwind.Hooks K U C Other) (choice : C) (frame : F) (state : State)
    (layout : LocalLayout) (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (locals : frame.locals = #[falseSlot layout]) (varargs : frame.vaList = #[]) :
    CallMachine.cleanup (CallMachine.withUnwind lifecycle hooks) choice false frame state =
      .ok .normal state :=
  cleanup_unit lifecycle hooks choice frame state (some target) unwind continuation
    (falseSlot layout) locals ⟨_, rfl⟩ varargs

/-- Write the helper's Boolean to a cached, live immediate caller slot
using the actual machine place writer. The expected frame differs only in
the selected local's payload. -/
theorem writeFalseCached [DecidableEq K]
    (access : PlaceMachine.AccessConfig K U) (alloc : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (older : Array F) (caller : F) (machine : MachineHooks.MachineState K U)
    (id : LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (atSlot : caller.locals[id]? = some slot)
    (live : ∃ old, slot.value = .live (.immediate old))
    (sized : layout.layout.isSized = true) (noClocks : caller.extra.dataRace = none)
    (debug : compiler.debugAssertions = false) (abi : compiler.debugAbiCheck = fun _ _ => pure ())
    (validation : ∀ state, ∃ flag, compiler.validationInProgress state = .ok flag state) :
    let destination : RuntimePlace Provenance :=
      ⟨.local older.size id none caller.localsIdentity, layout⟩
    let newSlot : LocalState Provenance LocalLayout := {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
    let updated := {caller with locals := caller.locals.setIfInBounds id newSlot}
    writePlaceImmediateNoValidate (PlaceMachine.placeHooks access alloc compiler) choice
      (.scalar (Scalar.fromBool false)) destination (withCurrent older caller machine) =
      .ok () (withCurrent older updated machine) := by
  obtain ⟨old, live⟩ := live
  have bound := (Array.getElem?_eq_some_iff.mp atSlot).1
  have found := (Array.getElem?_eq_some_iff.mp atSlot).2
  have got : caller.getLocalOperand id = .ok (.immediate old) := by
    simp [Frame.getLocalOperand, Frame.getLocal, bound, found, live, LocalState.access,
      bind, Bind.bind, pure, Pure.pure, Except.bind, Except.pure, Except.mapError]
  let newSlot : LocalState Provenance LocalLayout := {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
  let updated := {caller with locals := caller.locals.setIfInBounds id newSlot}
  have put : caller.setLocalOperand id (.immediate (.scalar (Scalar.fromBool false))) =
      .ok updated := by
    simp [Frame.setLocalOperand, Frame.replaceLocalValue, got, bound, found, updated, newSlot,
      Array.setIfInBounds, bind, Bind.bind, pure, Pure.pure, Except.bind, Except.pure]
  obtain ⟨flag, check⟩ := validation (withCurrent older updated machine)
  simp only [withCurrent] at check
  cases flag <;> with_unfolding_all
    simp [writePlaceImmediateNoValidate, asMplaceOrMutableLocal, PlaceMachine.placeHooks,
      requireCurrent_eq, checkLocalIdentity_debugOff, placeWriteLocalImmediate, stackLift_ok,
      sized, debug, abi, got, put, MachineHooks.currentFrame, Stack.currentFrame?, Stack.frameIndex,
      withCurrent, MachineHooks.setCurrentFrame, MachineHooks.afterLocalWrite, noClocks,
      updated, newSlot, check, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      set, MonadStateOf.set, EStateM.set, pure, Pure.pure, EStateM.pure, Except.pure, Except.bind]

/-- The production raw immediate read used by the Bool return transfer
returns the existing value and touches no allocation. -/
theorem readRawFalse [DecidableEq K]
    (access : PlaceMachine.AccessConfig K U) (layout : LocalLayout) (before : State)
    (retain : access.retainTouched before.machine none = before.machine) :
    PlaceMachine.readRaw access ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ before =
      .ok (.immediate ⟨.scalar (Scalar.fromBool false), localMemoryLayout layout⟩) before := by
  cases before with
  | mk stack machine =>
    simp [PlaceMachine.readRaw, readImmediateRaw, PlaceMachine.commit, PlaceMachine.finish, Id.run,
      retain, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, Pure.pure, EStateM.pure]

/-- A same-layout return copy through the real place hooks writes the
Boolean to the live caller slot. The exact residual operation is the
production validation branch on the updated destination. -/
theorem copyFalseCached [DecidableEq K]
    (access : PlaceMachine.AccessConfig K U) (alloc : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C) (copy : PlaceCopyHooks Provenance State C)
    (choice : C) (older : Array F) (caller : F) (machine : MachineHooks.MachineState K U)
    (id : LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (atSlot : caller.locals[id]? = some slot)
    (live : ∃ old, slot.value = .live (.immediate old))
    (sized : layout.layout.isSized = true) (noClocks : caller.extra.dataRace = none)
    (debug : compiler.debugAssertions = false) (abi : compiler.debugAbiCheck = fun _ _ => pure ())
    (validation : ∀ state, ∃ flag, compiler.validationInProgress state = .ok flag state)
    (compatible : copy.compatible layout layout = .ok true)
    (padding : ∃ hasPadding, copy.hasPadding layout = .ok hasPadding)
    (rawRead : copy.readRaw choice = PlaceMachine.readRaw access)
    (retain : access.retainTouched machine none = machine) :
    let destination : RuntimePlace Provenance :=
      ⟨.local older.size id none caller.localsIdentity, layout⟩
    let newSlot : LocalState Provenance LocalLayout :=
      {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
    let updated := {caller with locals := caller.locals.setIfInBounds id newSlot}
    copyRuntimePlace (PlaceMachine.placeHooks access alloc compiler) copy choice
      ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ destination true
      (withCurrent older caller machine) =
      ((do
        if ← compiler.enforceValidity choice layout then compiler.validate choice destination) :
          MachineHooks.M K U Unit) (withCurrent older updated machine) := by
  obtain ⟨pad, padding⟩ := padding
  have write := writeFalseCached access alloc compiler choice older caller machine id slot layout
    atSlot live sized noClocks debug abi validation
  have raw := readRawFalse access layout (withCurrent older caller machine) retain
  dsimp only at write ⊢
  cases pad <;>
    simp [copyRuntimePlace, copyRuntimePlaceNoValidate, placeLift_ok, compatible, padding,
      rawRead, raw, sized, write,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure] <;>
    rfl

/-- The normal Boolean helper return reads the cached local, releases its
empty protector list, pops the real frame, and follows the caller's target
after actual return-value copying. A copy failure retains its exact state. -/
theorem returnRuntimeGuard
    {O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (unwindHooks : Unwind.Hooks K U C Other) (lifecycle : CallMachine.Lifecycle K U C)
    (withUnwind : config.lifecycle = CallMachine.withUnwind lifecycle unwindHooks)
    (choice : C) (older : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (locals : frame.locals = #[falseSlot layout])
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (compiler : PlaceMachine.CompilerHooks K U C)
    (readLocal : config.projection.place.localToOp = PlaceMachine.localToOp compiler)
    (validation : ∀ state, ∃ flag, compiler.validationInProgress state = .ok flag state)
    (source : GeneratedBodySafety.input.document.bodies[19]?.map (·.mir) = some frame.body)
    (atReturn : frame.location = .mir ⟨0, 1⟩)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let control := (ExecutionMachine.terminatorHooks config limits).toControlHooks
    let operand : OpTy Provenance := ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩
    let popped : State := ⟨⟨older⟩, afterRelevanceAt older frame machine
      (thread.topUserRelevantFrame.getD older.size)⟩
    ControlFlow.returnFromCurrentFrame control choice false (withCurrent older frame machine) =
      match control.copyReturn choice operand frame.returnPlace popped with
      | (after, .error error) => (after, .error error)
      | (after, .ok ()) => ControlFlow.goToBlock target after := by
  let checked := ExecutionMachine.withValidation config limits
  let control := (ExecutionMachine.terminatorHooks config limits).toControlHooks
  let operand : OpTy Provenance := ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩
  let popped : State := ⟨⟨older⟩, afterRelevanceAt older frame machine
    (thread.topUserRelevantFrame.getD older.size)⟩
  have normalCode : (frame.body.basicBlocks[0]?.map (·.cleanup)) = some false := by
    have specific := congrArg (fun code : Option Body =>
      code.bind fun body => body.basicBlocks[0]?.map (·.cleanup)) source
    exact specific.symm
  have readEq : control.returnOperand choice (withCurrent older frame machine) =
      (withCurrent older frame machine, .ok operand) := by
    change MachineHooks.run (config.projection.place.localToOp choice 0) _ = _
    simp only [MachineHooks.run, Call.run, readLocal]
    rw [readReturnFalse compiler choice older frame machine layout locals sized noClocks validation]
  have popEq : control.popFrame choice (withCurrent older frame machine) = (popped, .ok frame) := by
    change MachineHooks.run (TypedMachineBindings.popRaw
      (TypedMachineBindings.retagHooks checked.access checked.retag)) _ = _
    simp only [MachineHooks.run, Call.run]
    rw [pop_empty _ older frame machine tracker borrowFrame tracked frameTracked empty thread active]
  have cleanEq (state : State) : control.cleanupFrame choice false frame state =
      (state, .ok .normal) := by
    change MachineHooks.run (CallMachine.cleanup config.lifecycle choice false frame) _ = _
    rw [withUnwind]
    simp only [MachineHooks.run, Call.run]
    rw [cleanupRuntimeGuard lifecycle unwindHooks choice frame state layout target unwind continuation locals varargs]
  change ControlFlow.returnFromCurrentFrame control choice false (withCurrent older frame machine) =
    match control.copyReturn choice operand frame.returnPlace popped with
    | (after, .error error) => (after, .error error)
    | (after, .ok ()) => ControlFlow.goToBlock target after
  generalize control = hooks at readEq popEq cleanEq ⊢
  cases hooks
  rename_i bodySpan readReturn pop copyReturn cleanup unwindTerminate
  rcases block : frame.body.basicBlocks[0]? with _ | code
  · simp [block] at normalCode
  have cleanupFalse : code.cleanup = false := by simpa [block] using normalCode
  simp only [ControlFlow.returnFromCurrentFrame, withCurrent, Stack.currentFrame?,
    Array.back?_push, atReturn, block, cleanupFalse, Id.run, bind, Bind.bind, pure, Pure.pure,
    ↓reduceIte, Bool.false_bne, Bool.false_eq_true, Bool.false_and, Bool.not_false] at readEq popEq ⊢
  erw [readEq]
  erw [popEq]
  rcases result : copyReturn choice operand frame.returnPlace popped with ⟨after, outcome⟩
  cases outcome with
  | error error => simp [result]
  | ok done =>
    cases done
    have cleaned := cleanEq after
    change cleanup choice false frame after = (after, .ok .normal) at cleaned
    simp [result, cleaned, continuation, ControlFlow.returnToBlock]

/-- At the exported helper's second instruction the real step selector
dispatches the retained Return. -/
theorem selectedRuntimeReturn (before : State) (frame : F)
    (current : before.stack.currentFrame? = some frame)
    (source : GeneratedBodySafety.input.document.bodies[19]?.map (·.mir) = some frame.body)
    (atReturn : frame.location = .mir ⟨0, 1⟩) :
    ∃ term, Miri.Verification.StepWP.currentTerminator before = some term ∧ term.kind = .Return := by
  have shape := congrArg (fun code : Option Body => code.bind fun body =>
    body.basicBlocks[0]?.map fun block => (block.statements.size, block.cleanup, block.terminator.kind)) source
  change some (1, false, .Return) =
    (frame.body.basicBlocks[0]?.map fun block => (block.statements.size, block.cleanup, block.terminator.kind)) at shape
  cases row : frame.body.basicBlocks[0]? with
  | none => simp [row] at shape
  | some block =>
    simp only [row, Option.map_some, Option.some.injEq, Prod.mk.injEq] at shape
    have empty : block.statements[1]? = none := by
      apply Array.getElem?_eq_none
      omega
    exact ⟨block.terminator,
      by simp [Miri.Verification.StepWP.currentTerminator, current, atReturn, row, empty], shape.2.2.symm⟩

theorem writeFalseScoped [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (alloc : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (older : Array F) (caller : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (atSlot : caller.locals[id]? = some slot)
    (live : ∃ old, slot.value = .live (.immediate old))
    (sized : layout.layout.isSized = true) (noClocks : caller.extra.dataRace = none)
    (debug : compiler.debugAssertions = false) (abi : compiler.debugAbiCheck = fun _ _ => pure ())
    :
    let destination : RuntimePlace Provenance :=
      ⟨.local older.size id none caller.localsIdentity, layout⟩
    let newSlot : LocalState Provenance LocalLayout := {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
    let updated := {caller with locals := caller.locals.setIfInBounds id newSlot}
    writePlaceImmediateNoValidate (ValidityMachine.placeHooks access alloc compiler) choice
      (.scalar (Scalar.fromBool false)) destination (withCurrent older caller machine) =
      .ok () (withCurrent older updated machine) := by
  obtain ⟨old, live⟩ := live
  have bound := (Array.getElem?_eq_some_iff.mp atSlot).1
  have found := (Array.getElem?_eq_some_iff.mp atSlot).2
  have got : caller.getLocalOperand id = .ok (.immediate old) := by
    simp [Frame.getLocalOperand, Frame.getLocal, bound, found, live, LocalState.access,
      bind, Bind.bind, pure, Pure.pure, Except.bind, Except.pure, Except.mapError]
  let newSlot : LocalState Provenance LocalLayout := {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
  let updated := {caller with locals := caller.locals.setIfInBounds id newSlot}
  have put : caller.setLocalOperand id (.immediate (.scalar (Scalar.fromBool false))) =
      .ok updated := by
    simp [Frame.setLocalOperand, Frame.replaceLocalValue, got, bound, found, updated, newSlot,
      Array.setIfInBounds, bind, Bind.bind, pure, Pure.pure, Except.bind, Except.pure]
  cases ghost : machine.user.payload.ghost <;> with_unfolding_all
    simp [writePlaceImmediateNoValidate, asMplaceOrMutableLocal, ValidityMachine.placeHooks,
      ValidityMachine.compilerPolicy, ValidityMachine.validationInProgress, PlaceMachine.placeHooks,
      requireCurrent_eq, checkLocalIdentity_debugOff, placeWriteLocalImmediate, stackLift_ok,
      sized, debug, abi, got, put, MachineHooks.currentFrame, Stack.currentFrame?, Stack.frameIndex,
      withCurrent, MachineHooks.setCurrentFrame, MachineHooks.afterLocalWrite, noClocks,
      updated, newSlot, ghost, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      set, MonadStateOf.set, EStateM.set, pure, Pure.pure, EStateM.pure, Except.pure, Except.bind]

/-- A same-layout return copy through the real place hooks writes the
Boolean to the live caller slot. The exact residual operation is the
production validation branch on the updated destination. -/
theorem copyFalseScoped [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (alloc : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (copy : PlaceCopyHooks Provenance (ValidityMachine.State K U) C)
    (choice : C) (older : Array F) (caller : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : LocalId) (slot : LocalState Provenance LocalLayout) (layout : LocalLayout)
    (atSlot : caller.locals[id]? = some slot)
    (live : ∃ old, slot.value = .live (.immediate old))
    (sized : layout.layout.isSized = true) (noClocks : caller.extra.dataRace = none)
    (debug : compiler.debugAssertions = false) (abi : compiler.debugAbiCheck = fun _ _ => pure ())
    (compatible : copy.compatible layout layout = .ok true)
    (padding : ∃ hasPadding, copy.hasPadding layout = .ok hasPadding)
    (rawRead : copy.readRaw choice = PlaceMachine.readRaw access)
    (retain : access.retainTouched machine none = machine) :
    let destination : RuntimePlace Provenance :=
      ⟨.local older.size id none caller.localsIdentity, layout⟩
    let newSlot : LocalState Provenance LocalLayout :=
      {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
    let updated := {caller with locals := caller.locals.setIfInBounds id newSlot}
    copyRuntimePlace (ValidityMachine.placeHooks access alloc compiler) copy choice
      ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ destination true
      (withCurrent older caller machine) =
      ((do
        if ← ValidityMachine.enforceValidity then compiler.validate choice destination) :
          ValidityMachine.M K U Unit) (withCurrent older updated machine) := by
  obtain ⟨pad, padding⟩ := padding
  have write := writeFalseScoped access alloc compiler choice older caller machine id slot layout
    atSlot live sized noClocks debug abi
  have raw := readRawFalse access layout (withCurrent older caller machine) retain
  dsimp only at write ⊢
  cases pad <;>
    simp [copyRuntimePlace, copyRuntimePlaceNoValidate, placeLift_ok, compatible, padding,
      rawRead, raw, sized, write,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure] <;>
    rfl

end DuplicatePrefix.LanguageGuardStack

#print axioms DuplicatePrefix.LanguageGuardStack.pointerAddGuardBinding
#print axioms DuplicatePrefix.LanguageGuardStack.writeFalseCached
#print axioms DuplicatePrefix.LanguageGuardStack.copyFalseCached
#print axioms DuplicatePrefix.LanguageGuardStack.returnRuntimeGuard

#print axioms DuplicatePrefix.LanguageGuardStack.selectedRuntimeReturn

#print axioms DuplicatePrefix.LanguageGuardStack.copyFalseScoped

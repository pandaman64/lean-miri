import LanguageGuardStack

namespace DuplicatePrefix.LanguageGuardStack

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
open EmptyFunction.FrameExit

variable {K U C Other : Type}
local notation "State" => MachineHooks.State K U

set_option maxRecDepth 65536

private theorem readLanguageGuardFalse (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (older : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (deadOne deadTwo : LocalState Provenance LocalLayout)
    (locals : frame.locals = #[falseSlot layout, deadOne, deadTwo])
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (validation : ∀ state, ∃ flag, compiler.validationInProgress state = .ok flag state) :
    PlaceMachine.localToOp compiler choice 0 (withCurrent older frame machine) =
      .ok ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ (withCurrent older frame machine) := by
  have slot : frame.getLocal 0 = .ok (falseSlot layout) := by
    simp [Frame.getLocal, locals, pure, Pure.pure, Except.pure]
  have operand : frame.getLocalOperand 0 = .ok (.immediate (.scalar (Scalar.fromBool false))) := by
    simp [Frame.getLocalOperand, slot, falseSlot, LocalState.access, bind, Bind.bind,
      Except.bind, Except.mapError]
  obtain ⟨flag, check⟩ := validation (withCurrent older frame machine)
  simp only [withCurrent] at check
  cases flag <;> simp [PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
    MachineHooks.currentFrame, Stack.currentFrame?, withCurrent, slot, operand,
    falseSlot, sized, noClocks, check, MachineHooks.afterLocalRead,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]

/-- The normal Boolean helper return reads the cached local, releases its
empty protector list, pops the real frame, and follows the caller's target
after actual return-value copying. A copy failure retains its exact state. -/
theorem returnLanguageGuard
    {O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (unwindHooks : Unwind.Hooks K U C Other) (lifecycle : CallMachine.Lifecycle K U C)
    (withUnwind : config.lifecycle = CallMachine.withUnwind lifecycle unwindHooks)
    (choice : C) (older : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (deadOne deadTwo : LocalState Provenance LocalLayout)
    (deadOneValue : deadOne.value = .dead) (deadTwoValue : deadTwo.value = .dead)
    (locals : frame.locals = #[falseSlot layout, deadOne, deadTwo])
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (compiler : PlaceMachine.CompilerHooks K U C)
    (readLocal : config.projection.place.localToOp = PlaceMachine.localToOp compiler)
    (validation : ∀ state, ∃ flag, compiler.validationInProgress state = .ok flag state)
    (source : GeneratedBodySafety.input.document.bodies[9]?.map (·.mir) = some frame.body)
    (atReturn : frame.location = .mir ⟨4, 1⟩)
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
  have normalCode : (frame.body.basicBlocks[4]?.map (·.cleanup)) = some false := by
    have specific := congrArg (fun code : Option Body =>
      code.bind fun body => body.basicBlocks[4]?.map (·.cleanup)) source
    exact specific.symm
  have readEq : control.returnOperand choice (withCurrent older frame machine) =
      (withCurrent older frame machine, .ok operand) := by
    change MachineHooks.run (config.projection.place.localToOp choice 0) _ = _
    simp only [MachineHooks.run, Call.run, readLocal]
    rw [readLanguageGuardFalse compiler choice older frame machine layout deadOne deadTwo locals sized noClocks validation]
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
    simp [CallMachine.cleanup, continuation, locals, varargs, falseSlot, deadOneValue, deadTwoValue,
      CallMachine.withUnwind, Unwind.afterStackPop, bind, EStateM.bind, pure, EStateM.pure]
  change ControlFlow.returnFromCurrentFrame control choice false (withCurrent older frame machine) =
    match control.copyReturn choice operand frame.returnPlace popped with
    | (after, .error error) => (after, .error error)
    | (after, .ok ()) => ControlFlow.goToBlock target after
  generalize control = hooks at readEq popEq cleanEq ⊢
  cases hooks
  rename_i bodySpan readReturn pop copyReturn cleanup unwindTerminate
  rcases block : frame.body.basicBlocks[4]? with _ | code
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


/-- After the exported language guard's final StorageDead the real step selector
dispatches the retained Return. -/
theorem selectedLanguageGuardReturn (before : State) (frame : F)
    (current : before.stack.currentFrame? = some frame)
    (source : GeneratedBodySafety.input.document.bodies[9]?.map (·.mir) = some frame.body)
    (atReturn : frame.location = .mir ⟨4, 1⟩) :
    ∃ term, Miri.Verification.StepWP.currentTerminator before = some term ∧ term.kind = .Return := by
  have shape := congrArg (fun code : Option Body => code.bind fun body =>
    body.basicBlocks[4]?.map fun block => (block.statements.size, block.cleanup, block.terminator.kind)) source
  change some (1, false, .Return) =
    (frame.body.basicBlocks[4]?.map fun block => (block.statements.size, block.cleanup, block.terminator.kind)) at shape
  cases row : frame.body.basicBlocks[4]? with
  | none => simp [row] at shape
  | some block =>
    simp only [row, Option.map_some, Option.some.injEq, Prod.mk.injEq] at shape
    have empty : block.statements[1]? = none := by
      apply Array.getElem?_eq_none
      omega
    exact ⟨block.terminator,
      by simp [Miri.Verification.StepWP.currentTerminator, current, atReturn, row, empty], shape.2.2.symm⟩

end DuplicatePrefix.LanguageGuardStack

#print axioms DuplicatePrefix.LanguageGuardStack.returnLanguageGuard

#print axioms DuplicatePrefix.LanguageGuardStack.selectedLanguageGuardReturn

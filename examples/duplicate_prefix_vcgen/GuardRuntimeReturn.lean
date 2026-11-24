import LanguageGuardStack

namespace DuplicatePrefix.LanguageGuardStack

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
open EmptyFunction.FrameExit

variable {K U C Other : Type}
local notation "State" => MachineHooks.State K U

/-- The actual retained Boolean helper returns to a live caller. The
scoped return-copy lemma supplies the locally isolated place effect. -/
theorem returnRuntimeGuardCachedCaller
    {O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (unwindHooks : Unwind.Hooks K U C Other) (lifecycle : CallMachine.Lifecycle K U C)
    (withUnwind : config.lifecycle = CallMachine.withUnwind lifecycle unwindHooks)
    (choice : C) (older : Array F) (caller frame : F) (machine : MachineHooks.MachineState K U)
    (layout : LocalLayout) (locals : frame.locals = #[falseSlot layout])
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (compiler : PlaceMachine.CompilerHooks K U C)
    (readLocal : config.projection.place.localToOp = PlaceMachine.localToOp compiler)
    (validation : ∀ state, ∃ flag, compiler.validationInProgress state = .ok flag state)
    (source : GeneratedBodySafety.input.document.bodies[19]?.map (·.mir) = some frame.body)
    (atReturn : frame.location = .mir ⟨0, 1⟩)
    (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some 1) unwind)
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (index : LocalId) (destination : frame.returnPlace = .frameLocal older.size index none layout caller.localsIdentity)
    (slot : LocalState Provenance LocalLayout)
    :
    let newSlot := {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
    let updated := {caller with locals := caller.locals.setIfInBounds index newSlot}
    let popMachine := afterRelevanceAt (older.push caller) frame machine
      (thread.topUserRelevantFrame.getD (older.push caller).size)
    let checked := ExecutionMachine.withValidation config limits
    copyRuntimePlace config.projection.place checked.copy choice
      ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩
      ⟨.local older.size index none caller.localsIdentity, layout⟩ true
      (withCurrent older caller popMachine) = .ok () (withCurrent older updated popMachine) →
    ControlFlow.returnFromCurrentFrame (ExecutionMachine.terminatorHooks config limits).toControlHooks
      choice false (withCurrent (older.push caller) frame machine) =
      (withCurrent older {updated with location := .mir ⟨1, 0⟩} popMachine, .ok ()) := by
  intro newSlot updated popMachine checked copied
  have returned := returnRuntimeGuard config limits unwindHooks lifecycle withUnwind choice
    (older.push caller) frame machine layout locals sized noClocks compiler readLocal validation
    source atReturn 1 unwind continuation varargs tracker borrowFrame tracked frameTracked empty thread active
  rw [returned]
  simp only [ExecutionControl.hooks, ExecutionMachine.projectionHooks,
    destination, RuntimeStackPlace.toRuntimePlace, MachineHooks.run, Call.run]
  change copyRuntimePlace (ExecutionMachine.withValidation config limits).projection.place
    (ExecutionMachine.withValidation config limits).copy choice
    ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩
    ⟨.local older.size index none caller.localsIdentity, layout⟩ true
    ⟨⟨older.push caller⟩, afterRelevanceAt (older.push caller) frame machine
      (thread.topUserRelevantFrame.getD (older.push caller).size)⟩ = _ at copied
  rw [copied]
  simp [ControlFlow.goToBlock, ControlFlow.setLocation, withCurrent, Stack.currentFrame?]

end DuplicatePrefix.LanguageGuardStack

#print axioms DuplicatePrefix.LanguageGuardStack.returnRuntimeGuardCachedCaller

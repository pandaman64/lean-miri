import duplicate_prefix.PointerAddCurrentFacts
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.LiteralUse
import duplicate_prefix.LiteralConstant
import duplicate_prefix.SourceSteps
import NestedGuardDriver

namespace DuplicatePrefix.PointerAddCurrentGuardTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def literal : ConstOperand := ⟨⟨102⟩, none, .Val .ZeroSized 5⟩
private def location : Location := ⟨5, 0⟩
private def place : Place := ⟨3, #[]⟩

theorem normalizedUnit (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 3 = .ok 5 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem guardTailAssignment
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 3 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[3].value = .live (.immediate old))
    (uncached : frame.locals[3].layout = none)
    (body : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (located : frame.location = .mir location)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let written := ActualLocalCopy.written frame 3 CopyHelperUnit.layout valid .uninit
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {written with location := .mir ⟨5, 1⟩} machine, .ok true) := by
  intro config written
  let cached := LocalPlaces.cachePlaceLayout frame 3 CopyHelperUnit.layout valid
  have operand := LiteralConstant.operand_at options limits (remaining+1) span debug
    .ZeroSized 5 ⟨102⟩ (some CopyHelperUnit.layout) .uninit CopyHelperUnit.layout
    (by intros; with_unfolding_all rfl) (Storage.withCurrent older cached machine)
  have bound : 3 < cached.locals.size := by simpa [cached, LocalPlaces.cachePlaceLayout] using valid
  have oldLive : cached.locals[3].value = .live (.immediate old) := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using live
  have cache : cached.locals[3].layout = some CopyHelperUnit.layout := by
    simp [cached, LocalPlaces.cachePlaceLayout]
  have copy := CopyHelperUnit.copy_unit_shallow options limits remaining span debug fuel budget
    older cached machine 3 old bound oldLive cache noClocks ghost shallow
  have effect := LiteralUse.uncached options limits remaining span debug older frame machine
    literal 3 CopyHelperUnit.layout .uninit CopyHelperUnit.layout_shape.2.1 valid uncached
    (PointerAddFacts.compute_local older frame machine 3 5 CopyHelperUnit.layout
      (normalizedUnit frame body identity callee)
      (by with_unfolding_all exact CopyHelperUnit.layout_query))
    tracker tracked mode operand copy
  have blockBound : 5 < PointerAddCurrentFacts.body.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := PointerAddCurrentFacts.body.body.basicBlocks[5]'blockBound
  have assignBound : 0 < block.statements.size := by
    with_unfolding_all change 0 < 1
    decide
  let stmt := block.statements[0]'assignBound
  apply SourceSteps.assign_exact config limits () older frame written machine machine location
    block stmt place (.Use (.Constant literal) .Yes) located
  · simp [body, location, block, blockBound]
  · simp [location, stmt, assignBound]
  · with_unfolding_all rfl
  · exact effect
  · exact located

/-- At the next PC the actual code is the fixed-scheduling jump to the
offset block. The tick only updates interpreter control in the machine. -/
theorem guardTailGoto
    {K U C O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState K U)
    (body : frame.body = PointerAddCurrentFacts.body.body)
    (located : frame.location = .mir ⟨5, 1⟩)
    (lens : ∀ control user, config.terminators.getControl
      (config.terminators.setControl control user) = control)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : (config.terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : (config.terminators.getControl machine.user).gcInterval = 0) :
    let user := NestedGuardDriver.nextTerminatorUser config.terminators machine.user
    ExecutionMachine.step config limits choice (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {frame with location := .mir ⟨6, 0⟩} {machine with user}, .ok true) := by
  let before := Storage.withCurrent older frame machine
  have bound : 5 < PointerAddCurrentFacts.body.body.basicBlocks.size := by with_unfolding_all decide +kernel
  let block := PointerAddCurrentFacts.body.body.basicBlocks[5]'bound
  have present : frame.body.basicBlocks[5]? = some block := by simp [body, block, bound]
  have exhausted : block.statements[1]? = none := by with_unfolding_all rfl
  have code : block.terminator.kind = .Goto 6 #[] := by with_unfolding_all rfl
  have selected : Miri.Verification.StepWP.currentTerminator before = some block.terminator := by
    simp [Miri.Verification.StepWP.currentTerminator, before, Storage.withCurrent,
      Stack.currentFrame?, located, present, exhausted]
  rw [show (ExecutionMachine.step config limits choice (Storage.withCurrent older frame machine) =
      ExecutionMachine.step config limits choice before) from rfl]
  rw [NestedGuardDriver.stepFixedTerminator config limits choice before block.terminator selected lens fixed unchecked noGc]
  simp only [ControlFlow.evalTerminator, code, ControlFlow.goToBlock, ControlFlow.setLocation, before,
    Storage.withCurrent, Stack.currentFrame?, Array.back?_push, Array.pop_push, Id.run, pure, Pure.pure]
  rfl

end DuplicatePrefix.PointerAddCurrentGuardTail

#print axioms DuplicatePrefix.PointerAddCurrentGuardTail.guardTailAssignment

#print axioms DuplicatePrefix.PointerAddCurrentGuardTail.guardTailGoto

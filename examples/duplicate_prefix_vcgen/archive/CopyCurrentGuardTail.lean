import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.LiteralUse
import duplicate_prefix.LiteralConstant
import duplicate_prefix.SourceSteps
import duplicate_prefix.SourceControl
import duplicate_prefix.CompilerFrameLayout

namespace DuplicatePrefix.CopyCurrentGuardTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def literal : ConstOperand := ⟨⟨138⟩, none, .Val .ZeroSized 5⟩
private def location : Location := ⟨6, 0⟩
private def place : Place := ⟨4, #[]⟩

theorem normalizedUnit (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 4 = .ok 5 := by
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
    (valid : 4 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[4].value = .live (.immediate old))
    (uncached : frame.locals[4].layout = none)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (located : frame.location = .mir location)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let written := ActualLocalCopy.written frame 4 CopyHelperUnit.layout valid .uninit
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {written with location := .mir ⟨6, 1⟩} machine, .ok true) := by
  intro config written
  let cached := LocalPlaces.cachePlaceLayout frame 4 CopyHelperUnit.layout valid
  have operand := LiteralConstant.operand_at options limits (remaining+1) span debug
    .ZeroSized 5 ⟨138⟩ (some CopyHelperUnit.layout) .uninit CopyHelperUnit.layout
    (by intros; with_unfolding_all rfl) (Storage.withCurrent older cached machine)
  have bound : 4 < cached.locals.size := by simpa [cached, LocalPlaces.cachePlaceLayout] using valid
  have oldLive : cached.locals[4].value = .live (.immediate old) := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using live
  have cache : cached.locals[4].layout = some CopyHelperUnit.layout := by
    simp [cached, LocalPlaces.cachePlaceLayout]
  have copy := CopyHelperUnit.copy_unit_shallow options limits remaining span debug fuel budget
    older cached machine 4 old bound oldLive cache noClocks ghost shallow
  have effect := LiteralUse.uncached options limits remaining span debug older frame machine
    literal 4 CopyHelperUnit.layout .uninit CopyHelperUnit.layout_shape.2.1 valid uncached
    (PointerAddFacts.compute_local older frame machine 4 5 CopyHelperUnit.layout
      (normalizedUnit frame body identity callee)
      (by with_unfolding_all exact CopyHelperUnit.layout_query))
    tracker tracked mode operand copy
  have blockBound : 6 < HelperCompilerFacts.copyBody.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := HelperCompilerFacts.copyBody.body.basicBlocks[6]'blockBound
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

/-- The actual branch from the checked false path into the copy block. -/
theorem guardTailGoto
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (located : frame.location = .mir ⟨6,1⟩)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {frame with location := .mir ⟨7,0⟩}
        (SourceControl.accounted config.terminators (Storage.withCurrent older frame machine)).machine, .ok true) := by
  intro config
  have bound : 6 < HelperCompilerFacts.copyBody.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := HelperCompilerFacts.copyBody.body.basicBlocks[6]'bound
  exact SourceControl.goto_step config limits () older frame machine ⟨6,1⟩ block 7 located
    (by simp [body,block]) (by with_unfolding_all rfl) ⟨#[],by with_unfolding_all rfl⟩
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span)
    unchecked noGc fixed

end DuplicatePrefix.CopyCurrentGuardTail

#print axioms DuplicatePrefix.CopyCurrentGuardTail.guardTailAssignment
#print axioms DuplicatePrefix.CopyCurrentGuardTail.guardTailGoto

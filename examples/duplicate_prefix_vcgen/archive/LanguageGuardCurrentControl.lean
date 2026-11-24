import duplicate_prefix.LanguageGuardCurrentFacts
import duplicate_prefix.SourceSteps
import duplicate_prefix.SourceControl
import duplicate_prefix.CanonicalConfigFacts

namespace DuplicatePrefix.LanguageGuardCurrentControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

inductive Retirement where
  | unitTemporary
  | guardValue

def blockOf : Retirement → BasicBlockId
  | .unitTemporary => 1
  | .guardValue => 4

def slotOf : Retirement → Miri.MIR.LocalId
  | .unitTemporary => 2
  | .guardValue => 1

theorem retire
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (which : Retirement) (located : frame.location = .mir ⟨blockOf which, 0⟩)
    (valid : slotOf which < frame.locals.size) (immediate : Immediate Provenance)
    (live : frame.locals[slotOf which].value = .live (.immediate immediate)) :
    let config := PreparedContracts.actualConfig options () remaining span
    let dead := SourceSteps.deadFrame frame ⟨blockOf which, 0⟩ (slotOf which) valid
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older dead machine, .ok true) := by
  intro config dead
  have blockBound : blockOf which < LanguageGuardCurrentFacts.parentBody.body.basicBlocks.size := by
    cases which <;> with_unfolding_all decide +kernel
  let block := LanguageGuardCurrentFacts.parentBody.body.basicBlocks[blockOf which]'blockBound
  have count : block.statements.size = 1 := by cases which <;> with_unfolding_all rfl
  let statement := block.statements[0]'(by omega)
  apply SourceSteps.storage_dead_exact config limits () older frame machine ⟨blockOf which,0⟩
    block statement (slotOf which) immediate located
  · simp [body, block, blockBound]
  · simp [statement]
  · cases which <;> with_unfolding_all rfl
  · cases which <;> decide
  · exact live

theorem gotoRetirement
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (located : frame.location = .mir ⟨3, 1⟩)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () remaining span).terminators.getControl
      machine.user).gcInterval = 0) :
    let config := PreparedContracts.actualConfig options () remaining span
    let before := Storage.withCurrent older frame machine
    ExecutionMachine.step config limits () before =
      (Storage.withCurrent older {frame with location := .mir ⟨4, 0⟩}
        (SourceControl.accounted config.terminators before).machine, .ok true) := by
  intro config before
  have bound : 3 < LanguageGuardCurrentFacts.parentBody.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := LanguageGuardCurrentFacts.parentBody.body.basicBlocks[3]'bound
  apply SourceControl.goto_step config limits () older frame machine ⟨3,1⟩ block 4 located
  · simp [body, block, bound]
  · with_unfolding_all rfl
  · exact ⟨#[], by with_unfolding_all rfl⟩
  · exact CanonicalConfigFacts.actual_term_get_set options () remaining span
  · exact CanonicalConfigFacts.actual_term_set_set options () remaining span
  · exact unchecked
  · exact noGc
  · exact fixed

end DuplicatePrefix.LanguageGuardCurrentControl

#print axioms DuplicatePrefix.LanguageGuardCurrentControl.retire
#print axioms DuplicatePrefix.LanguageGuardCurrentControl.gotoRetirement

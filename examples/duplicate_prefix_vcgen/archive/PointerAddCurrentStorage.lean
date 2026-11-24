import duplicate_prefix.PointerAddCurrentFacts
import duplicate_prefix.SourceSteps
import duplicate_prefix.CanonicalConfigFacts

namespace DuplicatePrefix.PointerAddCurrentStorage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem live_pointer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (location : frame.location = .mir ⟨6,2⟩)
    (valid : (10 : Miri.MIR.LocalId) < frame.locals.size)
    (ready : frame.locals[10].value = .dead) (noClocks : frame.extra.dataRace = none) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (SourceSteps.liveFrame frame ⟨6,2⟩ 10 valid) machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := PointerAddCurrentFacts.body.body.basicBlocks[6]'(by decide +kernel)
  let statement := block.statements[2]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[6]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[2]? = some statement := by simp [statement]
  have kind : statement.kind = .StorageLive 10 := by rfl
  have trivial : config.lifecycle.storage.veryTriviallySized 8 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).storage]
    decide +kernel
  exact SourceSteps.storage_live_exact config limits () frames frame machine ⟨6,2⟩
    block statement 10 8 location blockAt statementAt kind valid (by rw [sourceBody]; rfl) trivial ready noClocks

theorem live_count
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (location : frame.location = .mir ⟨6,4⟩)
    (valid : (11 : Miri.MIR.LocalId) < frame.locals.size)
    (ready : frame.locals[11].value = .dead) (noClocks : frame.extra.dataRace = none) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (SourceSteps.liveFrame frame ⟨6,4⟩ 11 valid) machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := PointerAddCurrentFacts.body.body.basicBlocks[6]'(by decide +kernel)
  let statement := block.statements[4]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[6]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[4]? = some statement := by simp [statement]
  have kind : statement.kind = .StorageLive 11 := by rfl
  have trivial : config.lifecycle.storage.veryTriviallySized 4 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).storage]
    decide +kernel
  exact SourceSteps.storage_live_exact config limits () frames frame machine ⟨6,4⟩
    block statement 11 4 location blockAt statementAt kind valid (by rw [sourceBody]; rfl) trivial ready noClocks

theorem dead_count
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (location : frame.location = .mir ⟨6,7⟩)
    (valid : (11 : Miri.MIR.LocalId) < frame.locals.size)
    (value : Immediate Provenance) (ready : frame.locals[11].value = .live (.immediate value)) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (SourceSteps.deadFrame frame ⟨6,7⟩ 11 valid) machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := PointerAddCurrentFacts.body.body.basicBlocks[6]'(by decide +kernel)
  let statement := block.statements[7]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[6]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[7]? = some statement := by simp [statement]
  have kind : statement.kind = .StorageDead 11 := by rfl
  exact SourceSteps.storage_dead_exact config limits () frames frame machine ⟨6,7⟩
    block statement 11 value location blockAt statementAt kind valid (by decide) ready

theorem dead_pointer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (location : frame.location = .mir ⟨6,8⟩)
    (valid : (10 : Miri.MIR.LocalId) < frame.locals.size)
    (value : Immediate Provenance) (ready : frame.locals[10].value = .live (.immediate value)) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (SourceSteps.deadFrame frame ⟨6,8⟩ 10 valid) machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := PointerAddCurrentFacts.body.body.basicBlocks[6]'(by decide +kernel)
  let statement := block.statements[8]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[6]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[8]? = some statement := by simp [statement]
  have kind : statement.kind = .StorageDead 10 := by rfl
  exact SourceSteps.storage_dead_exact config limits () frames frame machine ⟨6,8⟩
    block statement 10 value location blockAt statementAt kind valid (by decide) ready

#print axioms live_pointer
#print axioms live_count
#print axioms dead_count
#print axioms dead_pointer
end DuplicatePrefix.PointerAddCurrentStorage

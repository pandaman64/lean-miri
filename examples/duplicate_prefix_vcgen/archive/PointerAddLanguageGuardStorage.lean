import duplicate_prefix.PointerAddCurrentFacts
import duplicate_prefix.SourceSteps
import duplicate_prefix.CanonicalConfigFacts

namespace DuplicatePrefix.PointerAddLanguageGuardStorage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem guardStorageLive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = PointerAddCurrentFacts.body.body)
    (located : frame.location = .mir ⟨0, 0⟩)
    (validOne : 3 < frame.locals.size) (validTwo : 4 < frame.locals.size)
    (deadOne : frame.locals[3].value = .dead) (deadTwo : frame.locals[4].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    let config := PreparedContracts.actualConfig options () remaining span
    let one := SourceSteps.liveFrame frame ⟨0,0⟩ 3 validOne
    let two := SourceSteps.liveFrame one ⟨0,1⟩ 4 (by simpa [one, SourceSteps.liveFrame] using validTwo)
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older one machine, .ok true) ∧
    ExecutionMachine.step config limits () (Storage.withCurrent older one machine) =
      (Storage.withCurrent older two machine, .ok true) := by
  intro config one two
  have blockBound : 0 < PointerAddCurrentFacts.body.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := PointerAddCurrentFacts.body.body.basicBlocks[0]'blockBound
  have blockAt : frame.body.basicBlocks[0]? = some block := by simp [body, block, blockBound]
  have count : block.statements.size = 2 := by with_unfolding_all rfl
  let first := block.statements[0]'(by omega)
  let second := block.statements[1]'(by omega)
  have oneType : frame.body.locals[3]? = some 5 := by rw [body]; with_unfolding_all rfl
  have twoType : frame.body.locals[4]? = some 0 := by rw [body]; with_unfolding_all rfl
  have configBool : config.lifecycle.storage.veryTriviallySized 0 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
    exact RootCompilerFacts.root_storage_trivial_bool
  have configUnit : config.lifecycle.storage.veryTriviallySized 5 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
    exact RootCompilerFacts.root_storage_trivial_type2
  constructor
  · apply SourceSteps.storage_live_exact config limits () older frame machine ⟨0,0⟩ block first 3 5
      located blockAt
    · simp [first]
    · with_unfolding_all rfl
    · exact oneType
    · exact configUnit
    · exact deadOne
    · exact noClocks
  · have twoBound : 4 < one.locals.size := by simpa [one, SourceSteps.liveFrame] using validTwo
    have stillDead : (one.locals[4]'twoBound).value = .dead := by
      simp [one, SourceSteps.liveFrame, Array.getElem_set, deadTwo]
    apply SourceSteps.storage_live_exact config limits () older one machine ⟨0,1⟩ block second 4 0
    · rfl
    · exact blockAt
    · simp [second]
    · with_unfolding_all rfl
    · exact twoType
    · exact configBool
    · exact stillDead
    · exact noClocks

end DuplicatePrefix.PointerAddLanguageGuardStorage

#print axioms DuplicatePrefix.PointerAddLanguageGuardStorage.guardStorageLive

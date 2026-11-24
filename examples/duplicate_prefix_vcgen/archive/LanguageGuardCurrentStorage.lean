import duplicate_prefix.LanguageGuardCurrentFacts
import duplicate_prefix.SourceSteps
import duplicate_prefix.CanonicalConfigFacts

namespace DuplicatePrefix.LanguageGuardCurrentStorage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

inductive Site where
  | languageGuard
  | pointerAdd

noncomputable def bodyAt : Site → Miri.MIR.Body
  | .languageGuard => LanguageGuardCurrentFacts.parentBody.body
  | .pointerAdd => PointerAddCurrentFacts.body.body

def slotOne : Site → Miri.MIR.LocalId
  | .languageGuard => 1
  | .pointerAdd => 3

def slotTwo : Site → Miri.MIR.LocalId
  | .languageGuard => 2
  | .pointerAdd => 4

def tyOne : Site → TyId
  | .languageGuard => 0
  | .pointerAdd => 5

def tyTwo : Site → TyId
  | .languageGuard => 5
  | .pointerAdd => 0

theorem storageLive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (site : Site) (body : frame.body = bodyAt site)
    (located : frame.location = .mir ⟨0, 0⟩)
    (validOne : slotOne site < frame.locals.size) (validTwo : slotTwo site < frame.locals.size)
    (deadOne : frame.locals[slotOne site].value = .dead) (deadTwo : frame.locals[slotTwo site].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    let config := PreparedContracts.actualConfig options () remaining span
    let one := SourceSteps.liveFrame frame ⟨0,0⟩ (slotOne site) validOne
    let two := SourceSteps.liveFrame one ⟨0,1⟩ (slotTwo site) (by simpa [one, SourceSteps.liveFrame] using validTwo)
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older one machine, .ok true) ∧
    ExecutionMachine.step config limits () (Storage.withCurrent older one machine) =
      (Storage.withCurrent older two machine, .ok true) := by
  intro config one two
  have blockBound : 0 < (bodyAt site).basicBlocks.size := by
    cases site <;> with_unfolding_all decide +kernel
  let block := (bodyAt site).basicBlocks[0]'blockBound
  have blockAt : frame.body.basicBlocks[0]? = some block := by simp [body, block, blockBound]
  have count : 2 ≤ block.statements.size := by
    cases site
    · with_unfolding_all change 2 ≤ 3
      decide
    · with_unfolding_all change 2 ≤ 2
      decide
  let first := block.statements[0]'(by omega)
  let second := block.statements[1]'(by omega)
  have oneType : frame.body.locals[slotOne site]? = some (tyOne site) := by
    rw [body]
    cases site <;> with_unfolding_all rfl
  have twoType : frame.body.locals[slotTwo site]? = some (tyTwo site) := by
    rw [body]
    cases site <;> with_unfolding_all rfl
  have configBool : config.lifecycle.storage.veryTriviallySized 0 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
    exact RootCompilerFacts.root_storage_trivial_bool
  have configUnit : config.lifecycle.storage.veryTriviallySized 5 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
    exact RootCompilerFacts.root_storage_trivial_type2
  have different : slotTwo site ≠ slotOne site := by cases site <;> decide
  constructor
  · apply SourceSteps.storage_live_exact config limits () older frame machine ⟨0,0⟩ block first (slotOne site) (tyOne site)
      located blockAt
    · simp [first]
    · cases site <;> with_unfolding_all rfl
    · exact oneType
    · cases site
      · exact configBool
      · exact configUnit
    · exact deadOne
    · exact noClocks
  · have twoBound : slotTwo site < one.locals.size := by simpa [one, SourceSteps.liveFrame] using validTwo
    have stillDead : (one.locals[slotTwo site]'twoBound).value = .dead := by
      simp [one, SourceSteps.liveFrame, Array.getElem_set, deadTwo, Ne.symm different]
    apply SourceSteps.storage_live_exact config limits () older one machine ⟨0,1⟩ block second (slotTwo site) (tyTwo site)
    · rfl
    · exact blockAt
    · simp [second]
    · cases site <;> with_unfolding_all rfl
    · exact twoType
    · cases site
      · exact configUnit
      · exact configBool
    · exact stillDead
    · exact noClocks

theorem guardStorageLive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (located : frame.location = .mir ⟨0, 0⟩)
    (validOne : 1 < frame.locals.size) (validTwo : 2 < frame.locals.size)
    (deadOne : frame.locals[1].value = .dead) (deadTwo : frame.locals[2].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    let config := PreparedContracts.actualConfig options () remaining span
    let one := SourceSteps.liveFrame frame ⟨0,0⟩ 1 validOne
    let two := SourceSteps.liveFrame one ⟨0,1⟩ 2 (by simpa [one, SourceSteps.liveFrame] using validTwo)
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older one machine, .ok true) ∧
    ExecutionMachine.step config limits () (Storage.withCurrent older one machine) =
      (Storage.withCurrent older two machine, .ok true) :=
  storageLive options limits remaining span older frame machine .languageGuard body located
    validOne validTwo deadOne deadTwo noClocks

end DuplicatePrefix.LanguageGuardCurrentStorage

#print axioms DuplicatePrefix.LanguageGuardCurrentStorage.storageLive

#print axioms DuplicatePrefix.LanguageGuardCurrentStorage.guardStorageLive

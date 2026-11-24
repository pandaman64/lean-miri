import duplicate_prefix.LanguageGuardCurrentStorage
import duplicate_prefix.LanguageGuardCurrentUnit
import duplicate_prefix.SuccessfulTrace
import duplicate_prefix.LocalDirectness

namespace DuplicatePrefix.LanguageGuardCurrentParentPrelude
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

noncomputable def result (frame : CompilerFrameContext.ActualFrame)
    (valid1 : 1 < frame.locals.size) (valid2 : 2 < frame.locals.size) :=
  let one := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1
  let two := SourceSteps.liveFrame one ⟨0,1⟩ 2 (by simpa [one,SourceSteps.liveFrame] using valid2)
  let three := LocalPlaces.cachePlaceLayout two 2 CopyHelperUnit.layout
    (by simpa [two,one,SourceSteps.liveFrame] using valid2)
  {three with location := .mir ⟨0,3⟩}

/-- Execute the parent guard's two declarations and unit tuple before its runtime call. -/
theorem to_runtime_call
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.parentBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.parentCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (valid1 : 1 < frame.locals.size) (valid2 : 2 < frame.locals.size)
    (dead1 : frame.locals[1].value = .dead) (dead2 : frame.locals[2].value = .dead)
    (uncached2 : frame.locals[2].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    SuccessfulTrace.Trace (PreparedContracts.actualConfig options () remaining span) limits
      (Storage.withCurrent older frame machine)
      (Storage.withCurrent older (result frame valid1 valid2) machine) := by
  let one := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1
  let two := SourceSteps.liveFrame one ⟨0,1⟩ 2 (by simpa [one,SourceSteps.liveFrame] using valid2)
  obtain ⟨first,second⟩ := LanguageGuardCurrentStorage.guardStorageLive options limits remaining span older frame machine
    body location valid1 valid2 dead1 dead2 noClocks
  have bound : 2 < two.locals.size := by simpa [two,one,SourceSteps.liveFrame] using valid2
  have cache : two.locals[2].layout = none := by
    simpa [two,one,SourceSteps.liveFrame,Array.getElem_set] using uncached2
  have unit := LanguageGuardCurrentUnit.guardUnitAssignment options limits remaining span debug fuel budget
    older two machine bound (by simp [two,SourceSteps.liveFrame]) cache body identity callee rfl noClocks ghost shallow
  exact .next first (.next second (.next unit (.refl _)))

end DuplicatePrefix.LanguageGuardCurrentParentPrelude

#print axioms DuplicatePrefix.LanguageGuardCurrentParentPrelude.to_runtime_call

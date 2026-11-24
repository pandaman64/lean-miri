import duplicate_prefix.CopyHelperSteps

namespace DuplicatePrefix.CopyHelperResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

noncomputable def constant : ConstOperand :=
  (CopyPreconditions.Bodies.useConstantAt HelperCompilerFacts.copyBody 7 9).get (by decide +kernel)

theorem literal : constant.value = .Val .ZeroSized 5 := by rfl

theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (old : Immediate Provenance)
    (valid : 0 < frame.locals.size)
    (live : frame.locals[0].value = .live (.immediate old))
    (uncached : frame.locals[0].layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (location : frame.location = .mir ⟨7,9⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        (CopyHelperSteps.advance (ActualLocalCopy.written frame 0 CopyHelperUnit.layout valid .uninit) ⟨7,9⟩) machine,.ok true) := by
  have query := PointerAddFacts.compute_local framesBefore frame machine 0 5 CopyHelperUnit.layout
    (CopyHelperFacts.normalized_local0 frame sourceBody identity fnInstance) CopyHelperUnit.layout_query
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    framesBefore frame (ActualLocalCopy.written frame 0 CopyHelperUnit.layout valid .uninit) machine machine
    ⟨7,9⟩ ⟨0,#[]⟩ (.Use (.Constant constant) .Yes) location
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using location
  · rw [sourceBody]
    with_unfolding_all rfl
  · exact CopyHelperConstant.assign_unit_literal_uncached options limits remaining span constant literal debugOff fuel validationFuel
      framesBefore frame machine 0 old valid live uncached query noClocks
      tracker tracked defaultMode ghostFalse shallow

#print axioms step
end DuplicatePrefix.CopyHelperResult

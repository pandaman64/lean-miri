import duplicate_prefix.AsMutEntryFacts
import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.CallArgumentStages
import duplicate_prefix.CallEntryLocals
import duplicate_prefix.CurrentReferenceLocalWrite

namespace DuplicatePrefix.AsMutPassArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts ActualReferenceMetadata
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem referenceStorage :
    CompilerStorage.veryTriviallySized PreparedReflection.actual.compiler.runtime 1 = .ok true := by
  exact RootCompilerFacts.root_storage_trivial_slice

noncomputable abbrev abi := HelperCompilerFacts.asMutPtrAbi

theorem copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (dead : frame.locals[1].value = .dead)
    (cached : frame.locals[1].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (value : Immediate Provenance) (after : RootState) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let h := ExecutionMachine.callHooks cfg limits
    let liveFrame := CurrentReferenceLocalWrite.written frame 1 .uninit valid
    let liveValid := show 1 < liveFrame.locals.size by simpa [liveFrame, CurrentReferenceLocalWrite.written] using valid
    let written := CurrentReferenceLocalWrite.written liveFrame 1 value liveValid
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size liveFrame 1 reference) true
      (Storage.withCurrent frames written machine) = .ok () after →
    Call.passArgument h () (.Copy ⟨.immediate value,reference⟩) (abi.args.getD 0 abi.ret)
      (abi.args.getD 0 abi.ret) 0 ⟨1,#[]⟩ 1 false (Storage.withCurrent frames frame machine) = .ok () after := by
  intro cfg h liveFrame liveValid written validated
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have typed : frame.body.locals[1]? = some 1 := by rw [body];rfl
  have storage := CallEntryLocals.storage_live options limits (remaining+1) span frames frame machine 1 1 valid
    typed referenceStorage dead noClocks
  have postCached : liveFrame.locals[1].layout = some reference := by
    simpa [liveFrame, CurrentReferenceLocalWrite.written, Array.getElem_set_self] using cached
  have evaluate := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff frames
    liveFrame machine 1 reference liveValid postCached reference_sized
  have compat : h.checkArgumentCompat () (abi.args.getD 0 abi.ret) (abi.args.getD 0 abi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact AsMutEntryFacts.argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 0 ⟨1,#[]⟩ 1 _ _ _ _ _
  · change (1 == (abi.args.getD 0 abi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (reference.layout == (abi.args.getD 0 abi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · exact ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff
      frames liveFrame machine 1 .uninit value liveValid
      (by simp [liveFrame,CurrentReferenceLocalWrite.written]) postCached noClocks ghost shallow _ rfl after validated

end DuplicatePrefix.AsMutPassArgument

#print axioms DuplicatePrefix.AsMutPassArgument.copy

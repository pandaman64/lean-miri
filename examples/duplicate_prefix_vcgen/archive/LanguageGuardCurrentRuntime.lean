import duplicate_prefix.LanguageGuardCurrentFacts
import PreparedArguments
import duplicate_prefix.LiteralConstant
import duplicate_prefix.ActualLocalPlace
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.RootScalarQueries
import duplicate_prefix.RootLocalStages
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.SourceSteps

namespace DuplicatePrefix.LanguageGuardCurrentRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private def expression : Rvalue := .UnaryOp .Not (.Constant ⟨⟨350⟩, none, .Val (.Scalar (.Int 1 1)) 0⟩)

theorem normalizedLocal (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = LanguageGuardCurrentFacts.leafBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.leafBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.leafCall.callee) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 0 = .ok 0 := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem runtimeGuardAssignment
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 0 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[0].value = .live (.immediate old))
    (uncached : frame.locals[0].layout = none)
    (body : frame.body = LanguageGuardCurrentFacts.leafBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.leafBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.leafCall.callee)
    (located : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let written := ActualLocalCopy.written frame 0 RootCompilerFacts.boolLayout valid
      (.scalar (.fromBool false))
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {written with location := .mir ⟨0,1⟩} machine, .ok true) := by
  intro config written
  let layout := RootCompilerFacts.boolLayout
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cached := LocalPlaces.cachePlaceLayout frame 0 layout valid
  let before := Storage.withCurrent older frame machine
  let prepared := Storage.withCurrent older cached machine
  let dest := LocalPlaces.localRuntimePlace older.size cached 0 layout
  let raw : Scalar Provenance := .fromBool true
  let operand : OpTy Provenance := ⟨.immediate (.scalar raw), layout⟩
  have computed := PointerAddFacts.compute_local older frame machine 0 0 layout
    (normalizedLocal frame body identity callee)
    (by with_unfolding_all exact RootCompilerFacts.bool_layout_eq)
  have place := ActualLocalPlace.uncached options limits (remaining+1) span debug older frame machine
    0 layout valid uncached RootGenericBoolWrite.bool_sized computed
  have literal := LiteralConstant.operand_at options limits (remaining+1) span debug
    (.Scalar (.Int 1 1)) 0 ⟨350⟩ (some layout) (.scalar raw) layout
    (by intros; with_unfolding_all rfl) prepared
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists
    layout RootGenericBoolWrite.bool_initialized
  have read := RootLocalStages.canonical_read_scalar options limits (remaining+1) span
    prepared raw layout ⟨primitive, range, repr⟩
  have classification := RootScalarQueries.bool_classification options (remaining+1) span limits
  have boolLayout := RootScalarQueries.bool_layout options (remaining+1) span limits
  have classificationAt : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
    () layout.ty).run prepared = .ok .boolean prepared := by
    change ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
      () 0) prepared = _
    rw [classification]
    rfl
  have boolLayoutAt : ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
    ()).run prepared = .ok layout prepared := by
    change ((ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
      ()) prepared = _
    rw [boolLayout]
    rfl
  have reduction := PreparedArguments.languageCheckRuntimeAssignment config limits () layout dest operand
    before prepared prepared prepared prepared prepared hooks rfl place rfl literal read
    classificationAt boolLayoutAt
  change evalRvalueIntoPlace hooks () expression ⟨0,#[]⟩ before =
    hooks.writeImmediate () (.scalar (Scalar.fromBool false)) dest prepared at reduction
  have bound : 0 < cached.locals.size := by simpa [cached, LocalPlaces.cachePlaceLayout] using valid
  have oldLive : cached.locals[0].value = .live (.immediate old) := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using live
  have cache : cached.locals[0].layout = some layout := by simp [cached, LocalPlaces.cachePlaceLayout]
  have writer := RootGenericBoolWrite.write_bool_shallow options limits remaining span debug fuel budget
    older cached machine 0 old false bound oldLive cache noClocks ghost shallow
  have effect : evalRvalueIntoPlace hooks () expression ⟨0,#[]⟩ before =
      .ok () (Storage.withCurrent older written machine) := by
    rw [reduction]
    simpa [dest, prepared, written, ActualLocalCopy.written, cached, LocalPlaces.cachePlaceLayout]
      using writer
  have blockBound : 0 < LanguageGuardCurrentFacts.leafBody.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := LanguageGuardCurrentFacts.leafBody.body.basicBlocks[0]'blockBound
  have assignBound : 0 < block.statements.size := by
    with_unfolding_all change 0 < 1
    decide
  let stmt := block.statements[0]'assignBound
  apply SourceSteps.assign_exact config limits () older frame written machine machine ⟨0,0⟩
    block stmt ⟨0,#[]⟩ expression located
  · simp [body, block, blockBound]
  · simp [stmt, assignBound]
  · with_unfolding_all rfl
  · exact effect
  · exact located

end DuplicatePrefix.LanguageGuardCurrentRuntime

#print axioms DuplicatePrefix.LanguageGuardCurrentRuntime.runtimeGuardAssignment

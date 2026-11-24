import duplicate_prefix.LanguageGuardCurrentFacts
import LanguageGuardPrepare
import duplicate_prefix.BoundUnitValidation
import duplicate_prefix.CallLocalRead
import duplicate_prefix.ActualLocalPlace
import duplicate_prefix.SourceSteps
import duplicate_prefix.RootMetadataQueries

namespace DuplicatePrefix.LanguageGuardCurrentUnit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootMetadataQueries

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private noncomputable def layout := CopyHelperUnit.layout

private theorem unitDiscriminantType :
    CompilerFacts.requiredType PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context
      5 "discriminant_type" = .ok 3 := by
  change CompilerFacts.requiredType context 5 "discriminant_type" = .ok 3
  with_unfolding_all rfl

private theorem unitDiscriminantLayout :
    CompilerDiscriminantFacts.discriminantLayout
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 5 =
        .ok CopyCompilerFacts.byteLayout := by
  unfold CompilerDiscriminantFacts.discriminantLayout
  rw [unitDiscriminantType]
  exact CopyCompilerFacts.compiler_byte_layout

private theorem actualUnitDiscriminantLayout
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.discriminantHooks
      (PreparedContracts.actualConfig options () remaining span)).discriminantLayout
        () 5 state = .ok CopyCompilerFacts.byteLayout state := by
  have facts := CanonicalConfigFacts.actual_fields options () remaining span
  unfold ExecutionMachine.discriminantHooks
  rw [facts.discriminant]
  unfold CompilerScalarLeaves.discriminant
  simp only [unitDiscriminantLayout]
  unfold_internal ".CompilerScalarLeaves.lift"
  rfl

theorem guardUnitAssignment
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : limits.validation = fuel + 1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 2 < frame.locals.size)
    (live : frame.locals[2].value = .live (.immediate .uninit))
    (uncached : frame.locals[2].layout = none)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.parentBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.parentCall.callee)
    (located : frame.location = .mir ⟨0, 2⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () remaining span
    let cached := LocalPlaces.cachePlaceLayout frame 2 layout valid
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {cached with location := .mir ⟨0, 3⟩} machine, .ok true) := by
  intro config cached
  let before := Storage.withCurrent older frame machine
  let prepared := Storage.withCurrent older cached machine
  let dest := LocalPlaces.localRuntimePlace older.size cached 2 layout
  let hooks := ExecutionMachine.rvalueHooks config limits
  let bound := ExecutionMachine.withValidation config limits
  let loc : Location := ⟨0, 2⟩
  let rvalue : Rvalue := .Aggregate .Tuple #[]
  have query := PointerAddFacts.compute_local older frame machine 2 5 layout
    (LanguageGuardCurrentFacts.parent_local2 frame body identity callee)
    (by with_unfolding_all exact CopyHelperUnit.layout_query)
  have placed : hooks.evalPlace () ⟨2,#[]⟩ true before = .ok dest prepared :=
    ActualLocalPlace.uncached options limits remaining span debug older frame machine
      2 layout valid uncached CopyHelperUnit.layout_shape.2.1 query
  have aggregate := LanguageGuardPrepare.prepareEmptyTuple config limits () before prepared dest placed
  have sized := CopyHelperUnit.layout_shape.2.1
  have stillLive : 2 < cached.locals.size := by simpa [cached, LocalPlaces.cachePlaceLayout] using valid
  have initial : cached.locals[2].value = .live (.immediate .uninit) := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using live
  have haveLayout : cached.locals[2].layout = some layout := by simp [cached, LocalPlaces.cachePlaceLayout]
  have read := CallLocalRead.place_to_op_cached options limits remaining span debug
    older cached machine 2 layout .uninit stillLive initial haveLayout sized noClocks ghost
  have expectedOp : (ExecutionMachine.discriminantHooks bound).toOp () dest prepared =
      .ok ⟨.immediate .uninit, layout⟩ prepared := read
  have discrLayout : (ExecutionMachine.discriminantHooks bound).discriminantLayout
      () dest.layout.ty prepared = .ok CopyCompilerFacts.byteLayout prepared := by
    change (ExecutionMachine.discriminantHooks config).discriminantLayout () layout.ty prepared = _
    have ty : layout.ty = 5 := CopyHelperUnit.layout_shape.1
    rw [ty]
    exact actualUnitDiscriminantLayout options remaining span prepared
  have discr := LanguageGuardPrepare.writeUnitDiscriminant (ExecutionMachine.discriminantHooks bound)
    () prepared CopyCompilerFacts.byteLayout dest ⟨.immediate .uninit, layout⟩ rfl rfl
    CopyHelperUnit.layout_shape.2.2.2 (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    expectedOp discrLayout
  have enforce : bound.compiler.enforceValidity () dest.layout prepared = .ok true prepared := by
    change config.compiler.enforceValidity () dest.layout prepared = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerEnforce]
    simp [ValidityMachine.enforceValidity, prepared, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  have validated := BoundUnitValidation.compiler_validate options limits remaining span debug fuel budget
    older cached machine 2 stillLive initial haveLayout ghost shallow
  have effect : evalRvalueIntoPlace hooks () rvalue ⟨2,#[]⟩ before = .ok () prepared := by
    change evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) () (.Aggregate .Tuple #[])
      ⟨2,#[]⟩ before = _ at aggregate
    change evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) () (.Aggregate .Tuple #[])
      ⟨2,#[]⟩ before = _
    rw [aggregate]
    change ((do
      Discriminant.writeDiscriminant (ExecutionMachine.discriminantHooks bound) () 0 dest
      if ← bound.compiler.enforceValidity () dest.layout then bound.compiler.validate () dest) :
      MachineHooks.M MiriMemoryKind Machine.RootUser Unit) prepared = _
    simp only [bind, Bind.bind, EStateM.bind, discr, enforce, ↓reduceIte]
    exact validated
  have blockBound : 0 < LanguageGuardCurrentFacts.parentBody.body.basicBlocks.size := by
    with_unfolding_all decide +kernel
  let block := LanguageGuardCurrentFacts.parentBody.body.basicBlocks[0]'blockBound
  have assignBound : 2 < block.statements.size := by
    with_unfolding_all change 2 < 3
    decide
  let stmt := block.statements[2]'assignBound
  apply SourceSteps.assign_exact config limits () older frame cached machine machine loc block stmt
    ⟨2,#[]⟩ rvalue located
  · simp [body, loc, block, blockBound]
  · simp [loc, stmt, assignBound]
  · with_unfolding_all rfl
  · exact effect
  · exact located

end DuplicatePrefix.LanguageGuardCurrentUnit

#print axioms DuplicatePrefix.LanguageGuardCurrentUnit.guardUnitAssignment

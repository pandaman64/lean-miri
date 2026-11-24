import duplicate_prefix.LanguageGuardCurrentFacts
import duplicate_prefix.LiteralUse
import duplicate_prefix.LiteralConstant
import duplicate_prefix.ActualScalarCopy
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.SourceSteps

namespace DuplicatePrefix.LanguageGuardCurrentFalse
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

inductive Site where
  | languageGuard
  | rejectedCount

noncomputable def loaded : Site → LoadedBody
  | .languageGuard => LanguageGuardCurrentFacts.parentBody
  | .rejectedCount => RootBody.reflected.body

noncomputable def function : Site → CallInstance
  | .languageGuard => LanguageGuardCurrentFacts.parentCall.callee
  | .rejectedCount => RootBody.reflected.functionInstance

private def literalSpan : Site → SpanRef
  | .languageGuard => ⟨212⟩
  | .rejectedCount => ⟨34⟩

private def literal (site : Site) : ConstOperand := ⟨literalSpan site, none, .Val (.Scalar (.Int 0 1)) 0⟩

def location : Site → Location
  | .languageGuard => ⟨3, 0⟩
  | .rejectedCount => ⟨5, 2⟩

private theorem normalizedReturn (site : Site) (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = (loaded site).body) (identity : frame.bodyIdentity = (loaded site).identity)
    (callee : frame.functionInstance = function site) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame 0 = .ok 0 := by
  cases site with
  | languageGuard => exact LanguageGuardCurrentFacts.parent_local0 frame body identity callee
  | rejectedCount =>
    unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
    rw [body, identity, callee]
    with_unfolding_all rfl

theorem writeFalse
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 0 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[0].value = .live (.immediate old))
    (uncached : frame.locals[0].layout = none)
    (site : Site) (body : frame.body = (loaded site).body)
    (identity : frame.bodyIdentity = (loaded site).identity)
    (callee : frame.functionInstance = function site)
    (located : frame.location = .mir (location site))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let written := ActualLocalCopy.written frame 0 RootCompilerFacts.boolLayout valid
      (.scalar (.fromBool false))
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {written with location := .mir {(location site) with statementIndex := (location site).statementIndex+1}} machine, .ok true) := by
  intro config written
  let layout := RootCompilerFacts.boolLayout
  let cached := LocalPlaces.cachePlaceLayout frame 0 layout valid
  let before := Storage.withCurrent older cached machine
  let dest := LocalPlaces.localRuntimePlace older.size cached 0 layout
  let value : Immediate Provenance := .scalar (.fromBool false)
  have operand := LiteralConstant.operand_at options limits (remaining+1) span debug
    (.Scalar (.Int 0 1)) 0 (literalSpan site) (some layout) value layout
    (by intros; with_unfolding_all rfl) before
  have bound : 0 < cached.locals.size := by simpa [cached, LocalPlaces.cachePlaceLayout] using valid
  have oldLive : cached.locals[0].value = .live (.immediate old) := by
    simpa [cached, LocalPlaces.cachePlaceLayout] using live
  have cache : cached.locals[0].layout = some layout := by simp [cached, LocalPlaces.cachePlaceLayout]
  have writer := RootGenericBoolWrite.write_bool_shallow options limits remaining span debug fuel budget
    older cached machine 0 old false bound oldLive cache noClocks ghost shallow
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists
    layout RootGenericBoolWrite.bool_initialized
  have copying := ActualScalarCopy.actual_copy_scalar options limits (remaining+1) span debug
    layout value dest rfl (.Initialized (value := primitive) (validRange := range)) repr
    RootGenericBoolWrite.bool_sized
  have copied : (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate value, layout⟩
      dest before = .ok () (Storage.withCurrent older written machine) := by
    rw [copying]
    simpa [dest, before, written, ActualLocalCopy.written, cached, LocalPlaces.cachePlaceLayout]
      using writer
  have computed := PointerAddFacts.compute_local older frame machine 0 0 layout
    (normalizedReturn site frame body identity callee)
    (by with_unfolding_all exact RootCompilerFacts.bool_layout_eq)
  have effect := LiteralUse.uncached options limits remaining span debug older frame machine (literal site) 0 layout value
    RootGenericBoolWrite.bool_sized valid uncached computed tracker tracked mode operand copied
  let loc := location site
  have blockBound : loc.block < (loaded site).body.basicBlocks.size := by
    cases site <;> with_unfolding_all decide +kernel
  let block := (loaded site).body.basicBlocks[loc.block]'blockBound
  have assignBound : loc.statementIndex < block.statements.size := by
    cases site
    · with_unfolding_all change 0 < 1
      decide
    · with_unfolding_all change 2 < 5
      decide
  let stmt := block.statements[loc.statementIndex]'assignBound
  apply SourceSteps.assign_exact config limits () older frame written machine machine loc
    block stmt ⟨0, #[]⟩ (.Use (.Constant (literal site)) .Yes) located
  · simp [body, block, blockBound]
  · simp [stmt, assignBound]
  · cases site <;> with_unfolding_all rfl
  · exact effect
  · exact located

theorem guardFalseAssignment
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (budget : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : 0 < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[0].value = .live (.immediate old))
    (uncached : frame.locals[0].layout = none)
    (body : frame.body = LanguageGuardCurrentFacts.parentBody.body)
    (identity : frame.bodyIdentity = LanguageGuardCurrentFacts.parentBody.identity)
    (callee : frame.functionInstance = LanguageGuardCurrentFacts.parentCall.callee)
    (located : frame.location = .mir (location .languageGuard))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let written := ActualLocalCopy.written frame 0 RootCompilerFacts.boolLayout valid
      (.scalar (.fromBool false))
    ExecutionMachine.step config limits () (Storage.withCurrent older frame machine) =
      (Storage.withCurrent older {written with location := .mir ⟨3, 1⟩} machine, .ok true) :=
  writeFalse options limits remaining span debug fuel budget older frame machine valid old live uncached
    .languageGuard body identity callee located noClocks tracker tracked mode ghost shallow

end DuplicatePrefix.LanguageGuardCurrentFalse

#print axioms DuplicatePrefix.LanguageGuardCurrentFalse.writeFalse

#print axioms DuplicatePrefix.LanguageGuardCurrentFalse.guardFalseAssignment

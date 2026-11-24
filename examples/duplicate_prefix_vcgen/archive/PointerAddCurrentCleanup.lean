import duplicate_prefix.PointerAddCurrentFacts
import duplicate_prefix.SourceSteps
import duplicate_prefix.SuccessfulTrace

/-! Retire the language guard's two temporaries at the actual entry to
the current pointer-add block. -/
namespace DuplicatePrefix.PointerAddCurrentCleanup
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem cleanup
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (location : frame.location = .mir ⟨6,0⟩)
    (valid3 : (3 : Miri.MIR.LocalId) < frame.locals.size) (valid4 : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (temp3 temp4 : Immediate Provenance)
    (live3 : frame.locals[3].value = .live (.immediate temp3))
    (live4 : frame.locals[4].value = .live (.immediate temp4)) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let one := SourceSteps.deadFrame frame ⟨6,0⟩ 4 valid4
    let two := SourceSteps.deadFrame one ⟨6,1⟩ 3 (by simpa [one,SourceSteps.deadFrame] using valid3)
    SuccessfulTrace.Trace config limits
      (Storage.withCurrent frames frame machine) (Storage.withCurrent frames two machine) := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := PointerAddCurrentFacts.body.body.basicBlocks[6]'(by decide +kernel)
  let stmt0 := block.statements[0]'(by decide +kernel)
  let stmt1 := block.statements[1]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[6]? = some block := by rw [sourceBody]; simp [block]
  have stmtAt0 : block.statements[0]? = some stmt0 := by simp [stmt0]
  have stmtAt1 : block.statements[1]? = some stmt1 := by simp [stmt1]
  have kind0 : stmt0.kind = .StorageDead 4 := by rfl
  have kind1 : stmt1.kind = .StorageDead 3 := by rfl
  let one := SourceSteps.deadFrame frame ⟨6,0⟩ 4 valid4
  have nextValid3 : (3 : Miri.MIR.LocalId) < one.locals.size := by
    simpa [one, SourceSteps.deadFrame] using valid3
  have first := SourceSteps.storage_dead_exact config limits () frames frame machine ⟨6,0⟩
    block stmt0 4 temp4 location blockAt stmtAt0 kind0 valid4 (by decide) live4
  have nextLive3 : one.locals[3].value = .live (.immediate temp3) := by
    simpa [one,SourceSteps.deadFrame,Array.getElem_set] using live3
  have second := SourceSteps.storage_dead_exact config limits () frames one machine ⟨6,1⟩
    block stmt1 3 temp3 rfl blockAt stmtAt1 kind1 nextValid3 (by decide) nextLive3
  exact .next first (.next second (.refl _))

#print axioms cleanup
end DuplicatePrefix.PointerAddCurrentCleanup

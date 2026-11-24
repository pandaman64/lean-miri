import duplicate_prefix.PointerAddCurrentStatements
import duplicate_prefix.PointerOffsetRvalueCore
namespace DuplicatePrefix.PointerAddCurrentOffset
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem offset
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (overflowLayout : LocalLayout)
    (overflowQuery : (PreparedContracts.actualConfig options () (remaining+1) span).scalar.overflowLayout ()
      RootCompilerFacts.usizeLayout = pure overflowLayout)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (validPointer : (10 : Miri.MIR.LocalId) < frame.locals.size) (validCount : (11 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (pointerLive : frame.locals[10].value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (pointerCached : frame.locals[10].layout = some CopyCompilerFacts.destPointerLayout)
    (countLive : frame.locals[11].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (countCached : frame.locals[11].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[0].value = .live (.immediate .uninit))
    (destUncached : frame.locals[0].layout = none)
    (sourceBody : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (callee : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : frame.location = .mir ⟨6,6⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live[id]? = some entry)
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    let value : Immediate Provenance := .scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))))
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame 0 CopyCompilerFacts.destPointerLayout validDest value) with location := .mir ⟨6,7⟩}
        machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let value : Immediate Provenance := .scalar (Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))))
  let block := PointerAddCurrentFacts.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[6]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[6]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[6]? = some statement := by simp [statement]
  have kind : statement.kind = .Assign ⟨0,#[]⟩ (.BinaryOp .Offset (.Move ⟨10,#[]⟩) (.Move ⟨11,#[]⟩)) := by with_unfolding_all rfl
  have normalized := PointerAddCurrentFacts.normalized_local0 frame sourceBody identity callee
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 8 = .ok CopyCompilerFacts.destPointerLayout := by
    with_unfolding_all exact CopyCompilerFacts.dest_pointer_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine 0 8 CopyCompilerFacts.destPointerLayout normalized lookup
  have effect := PointerOffsetRvalueCore.evaluate options limits remaining span overflowLayout overflowQuery debugOff fuel validationFuel
    framesBefore frame machine 10 11 0 validPointer validCount validDest (by decide) (by decide)
    id tag base offset count entry pointerLive pointerCached countLive countCached destLive destUncached
    query noClocks ghostFalse shallow cached present positive fits bounds
  have afterLocation : (ActualLocalCopy.written frame 0 CopyCompilerFacts.destPointerLayout validDest value).location = .mir ⟨6,6⟩ := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,location]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine ⟨6,6⟩ block statement
    ⟨0,#[]⟩ (.BinaryOp .Offset (.Move ⟨10,#[]⟩) (.Move ⟨11,#[]⟩)) location blockAt statementAt kind effect afterLocation

#print axioms offset
end DuplicatePrefix.PointerAddCurrentOffset

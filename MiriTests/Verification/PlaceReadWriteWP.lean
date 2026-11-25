import Miri.Verification.PlaceReadWriteWP

namespace MiriTests.PlaceReadWriteWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.Verification Std.WP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U

-- An immediate uninit read fails at the state with no touched allocation.
example (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (layout : LocalLayout) (before : State) (onError : StepError → State → Prop)
    (readable : isPrimitiveReadable (localMemoryLayout layout).backendRepr = true) :
    wp ((ExecutionMachine.rvalueHooks config limits).readImmediate choice ⟨.immediate .uninit, layout⟩)
      (fun _ _ => False) onError before =
      onError (config.access.memoryError .invalidUninitBytes)
        {before with machine := config.access.retainTouched before.machine none} := by
  simp only [miri_initial_wp, readable, ↓reduceIte]

-- A direct memory write delivers the actual post-write state to validity.
example (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (layout : LocalLayout) (memory : MemPlace Provenance) (value : Immediate Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (sized : layout.layout.isSized = true) :
    wp ((ExecutionMachine.rvalueHooks config limits).writeImmediate choice value
      ⟨.memory memory, layout⟩) post onError =
      let hooks := (ExecutionMachine.projectionHooks config).place
      RvalueWP.actionPre (hooks.writeMemoryNoValidate choice value ⟨memory, layout⟩) (fun _ =>
        Miri.Verification.PlaceReadWriteWP.writeValidityPre hooks choice
          ⟨.memory memory, layout⟩ post onError) onError := by
  simp only [miri_initial_wp, sized]

-- A canonical indirect read forwards the allocation's uninitialized byte error
-- and keeps the access effects, including the selected allocation snapshot.
example (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (operand : OpTy Provenance) (memory : MemPlace Provenance)
    (primitive : BackendPrimitive) (validRange : WrappingRange) (before : State)
    (onError : StepError → State → Prop)
    (selected : AllocationAccessRef Provenance Miri.TreeBorrows.BorrowTree)
    (range bad : AllocRange)
    (indirect : operand.op = .indirect memory)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.access.runtime = .ok (localMemoryLayout operand.layout).size)
    (component : selected.range.subrange (allocRange Size.ZERO (localMemoryLayout operand.layout).size) =
      .ok range)
    (uninitialized : selected.allocation.initializationMask.isRangeInitialized range = .ok (.error bad)) :
    let access := getPlaceAlloc before.machine.memory ⟨before.machine, none⟩
      ⟨memory, localMemoryLayout operand.layout⟩ config.access.runtime config.access.ghostMode
      config.access.globalKind config.access.globalHooks (PlaceMachine.accessHooks config.access)
      config.access.dynamicLayout
    access.outcome = .ok (some selected) →
    (wp ((ExecutionMachine.rvalueHooks config limits).readImmediate choice operand)
      (fun _ _ => False) onError before ↔
      onError (access.hooks.pendingError.getD (config.access.memoryError
        (.allocation (.invalidUninitBytes (some ⟨range, bad⟩)))))
        {before with machine := (config.access.retainTouched
          {access.hooks.machine with memory := access.memory} access.touched)}) := by
  intro access loaded
  rw [RvalueWP.canonical_readImmediate,
    MemoryWP.scalarRead_access_iff config.access before operand memory primitive validRange access
      indirect backend width rfl]
  exact MemoryWP.scalarLoad_uninit_resultPre_iff config.access before (localMemoryLayout operand.layout)
    primitive access selected range bad loaded component uninitialized _ onError

-- An ordinary copy inside a retag scope checks compatibility before it
-- reaches the raw read, then takes the same scope restoration on failure.
example (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (source : OpTy Provenance) (dest : RuntimePlace Provenance) (error : StepError)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (incompatible : (ExecutionMachine.withValidation config limits).copy.compatible
      source.layout dest.layout = .error error) :
    RvalueWP.actionPre ((ExecutionMachine.rvalueHooks config limits).withRetagMode choice .None
      ((ExecutionMachine.rvalueHooks config limits).copyOp choice source dest)) post onError =
      RvalueWP.retagModePullback .None (fun _ failed => failed error) post onError := by
  simp only [miri_initial_wp]
  congr 1
  funext success failed
  simp only [Miri.Verification.PlaceReadWriteWP.copyPre,
    Miri.Verification.PlaceReadWriteWP.copyNoValidatePre, incompatible]

#print axioms Miri.Verification.PlaceReadWriteWP.wp_canonicalRead
#print axioms Miri.Verification.PlaceReadWriteWP.wp_canonicalWrite
#print axioms Miri.Verification.PlaceReadWriteWP.writePre_wholeLocal
#print axioms Miri.Verification.PlaceReadWriteWP.actionPre_localToOp
#print axioms Miri.Verification.PlaceReadWriteWP.actionPre_scopedWriteLocal
#print axioms Miri.Verification.PlaceReadWriteWP.immediateReadPre_scalar
#print axioms Miri.Verification.PlaceReadWriteWP.immediateWritePre_scalar
#print axioms Miri.Verification.PlaceReadWriteWP.actionPre_copyRuntimePlace

end MiriTests.PlaceReadWriteWP

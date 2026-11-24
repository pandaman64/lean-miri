import duplicate_prefix.RootThinPointerWrite
namespace DuplicatePrefix.RootPointerCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem copy_mut_pointer_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (value : Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate (.scalar value), CopyCompilerFacts.destPointerLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.destPointerLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar value)), layout := frame.locals[localId].layout} valid)} machine) := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists CopyCompilerFacts.destPointerLayout CopyCompilerFacts.primitive_layouts_initialized.2.2.1
  rw [ActualScalarCopy.actual_copy_scalar options limits (remaining + 1) span debugOff
    CopyCompilerFacts.destPointerLayout (.scalar value) _ rfl _ repr RootRawPointerValidity.mut_pointer_sized]
  exact RootPointerWrite.write_mut_pointer_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old value valid live cached noClocks ghostFalse shallow

theorem copy_const_pointer_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (value : Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.sourcePointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate (.scalar value), CopyCompilerFacts.sourcePointerLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.sourcePointerLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar value)), layout := frame.locals[localId].layout} valid)} machine) := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists CopyCompilerFacts.sourcePointerLayout CopyCompilerFacts.primitive_layouts_initialized.2.1
  rw [ActualScalarCopy.actual_copy_scalar options limits (remaining + 1) span debugOff
    CopyCompilerFacts.sourcePointerLayout (.scalar value) _ rfl _ repr RootRawPointerValidity.const_pointer_sized]
  exact RootPointerWrite.write_const_pointer_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old value valid live cached noClocks ghostFalse shallow

end DuplicatePrefix.RootPointerCopy

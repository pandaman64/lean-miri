import duplicate_prefix.EmptyReferenceInfo
import duplicate_prefix.RootUsizeWrite
namespace DuplicatePrefix.EmptyReferenceWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts EmptyReferenceContext EmptyReferenceInfo
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def written (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) (value : Immediate Provenance)
    (valid : localId < frame.locals.size) :=
  {frame with locals := (frame.locals.set localId {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}

theorem of_validation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old value : Immediate Provenance) (reference : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (after : RootState)
    (validation : ValidityMachine.validateRuntime
      (PreparedContracts.actualConfig options () remaining span).validity () (fuel+1)
      (LocalPlaces.localRuntimePlace frames.size (written frame localId value valid) localId reference) true
      (Storage.withCurrent frames (written frame localId value valid) machine) = .ok () after) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () value (LocalPlaces.localRuntimePlace frames.size frame localId reference)
      (Storage.withCurrent frames frame machine) = .ok () after := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let place := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation cfg limits)).place
  let post := Storage.withCurrent frames (written frame localId value valid) machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have physical := RootUsizeWrite.write_local_no_validate options limits (remaining+1) span debugOff frames frame machine
    localId old value reference valid live sized noClocks ghost
  have enforced : place.enforceValidity () reference post = .ok true post := by
    change cfg.projection.place.enforceValidity () reference post = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity,post,written,Storage.withCurrent,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have validated : place.validate () (LocalPlaces.localRuntimePlace frames.size frame localId reference) post = .ok () after := by
    change cfg.projection.place.validate () _ post = _
    rw [fields.projectionValidate,CanonicalConfigFacts.actual_validate_successor,validationFuel]
    exact validation
  change writePlaceImmediate place () value (LocalPlaces.localRuntimePlace frames.size frame localId reference) _ = _
  unfold writePlaceImmediate
  simp only [bind,EStateM.bind]
  rw [physical]
  simp only [bind,EStateM.bind]
  erw [enforced]
  exact validated

end
end DuplicatePrefix.EmptyReferenceWrite

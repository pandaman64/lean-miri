import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.LocalOperands
import duplicate_prefix.LocalPlaces
import duplicate_prefix.OperandDispatch
import duplicate_prefix.RootConstantStage
import duplicate_prefix.ImmediateReadProof
import duplicate_prefix.RvalueDispatch
import Miri.Input.EvalConfigurationCore
import Miri.Input.CompilerPlaceTypes

/-! Small canonical-machine bridges for the root guard assignment. These
lemmas retain the interpreter's real local operations and only discharge the
place-type debug branch selected by the canonical options. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace DuplicatePrefix.RootLocalStages
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem operand_check_skipped
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (place : Place) (op : OpTy Provenance) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options choice remaining span) limits)).checkPlaceType
      choice place op state = .ok () state := by
  have fields := CanonicalConfigFacts.actual_fields options choice remaining span
  have debugOff' : (PreparedContracts.actualConfig options choice remaining span).compiler.debugAssertions = false :=
    by rw [fields.debug, debugOff]
  simp [ExecutionMachine.operandHooks, ExecutionMachine.withValidation,
    TypedMachineBindings.bindValidation, debugOff', pure, EStateM.pure]

theorem place_check_skipped
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (place : Place) (value : RuntimePlace Provenance)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    ((ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options choice remaining span) limits)).place.checkPlaceType
      choice place value state) = .ok () state := by
  have fields := CanonicalConfigFacts.actual_fields options choice remaining span
  change (PreparedContracts.actualConfig options choice remaining span).projection.place.checkPlaceType
    choice place value state = .ok () state
  rw [fields.projectionPlaceType]
  simp [CompilerPlaceTypes.place, CompilerPlaceTypes.check, debugOff,
    pure, EStateM.pure]

end DuplicatePrefix.RootLocalStages

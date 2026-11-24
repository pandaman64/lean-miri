import CanonicalPhysicalLengthContext
import RejectPhysicalAfterLength
import CanonicalPreparedPhysicalResources
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open SourceDomain PreparedArguments CanonicalConfigFacts
open GeneralRangeMapOrigins ArchiveForestProjection RetagReleaseFootprint RootZeroShallowReturn NonemptyReturnWatch
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem nonemptyPhysicalSharedRejected
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1)
    (dynamic : options.place.dynamicFuel = sizeFuel+1) (dispatchFuel : limits.callDispatch = dispatch+1)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) (positive : 0 < length)
    (rejected : count > length / 2)
    (continues : frame.returnContinuation = .stop true)
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer length true)
    (admitted : Admitted program options remaining preparedTagHeadroom span
      (Storage.withCurrent #[] frame machine) frame pointer length count true)
    (compiler : InitialCompilerControl (Storage.withCurrent #[] frame machine) frame)
    (resource : ∀ id tag, pointer.provenance = some (.concrete id tag) →
      ∀ entry, machine.memory.live[id]? = some entry → CopySourceResources entry) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent #[] frame machine) := by
  have nonzero : count ≠ 0 := by
    intro equal
    rw [equal] at rejected
    exact UInt64.not_lt_zero rejected
  obtain ⟨context⟩ := reachesPhysicalLengthContext program loaded options limits remaining sizeFuel fuel dispatch span
    validation dynamic dispatchFuel frame machine pointer length count positive nonzero admitted compiler resource
  obtain ⟨done,finish,ended,_⟩ := context.post.rejectedPhysicalTrace options limits remaining fuel span validation
    admitted.profile.debugOff compilerSourceComparator context.base rejected positive pointer context.pointerTag
    context.retainedEntry context.loan.tracked context.cached context.address context.upper destination
    preparedTagHeadroom admitted.allocations admitted.profile.raceOff admitted.profile.backendOff continues admitted.stack.noVarargs
  exact GeneratedSafetyOfTrace.required program loaded _ limits _ done
    admitted.entered
    (SuccessfulTrace.append context.trace finish) (by simpa [Storage.withCurrent,ended])

#print axioms nonemptyPhysicalSharedRejected
end DuplicatePrefix.CanonicalCallDomain

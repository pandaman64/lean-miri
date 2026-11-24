import EmptyBackedCanonicalEntry
import EmptyBackedPhysicalTail
import VerifyZeroCachedCanonical

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open SourceDomain CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Nonzero counts on a concrete empty slice reject and return through an
independent interior physical Boolean destination. -/
theorem emptyBackedPhysicalRejects
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (id : AllocId) (tag : BorTag) (concrete : pointer.provenance = some (.concrete id tag))
    (ready : ∀ entry, before.machine.memory.live[id]? = some entry →
      RetagInsertionCapacity.Ready entry.allocation.extra ∧ entry.allocation.extra.nodes.size + 2 < 2^32)
    (positive : count ≠ 0)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer 0 count)
    (compiler : InitialCompilerControl before frame) (physical : PhysicalBoolDestination before frame pointer 0)
    (stack : before.stack.frames = #[frame]) (continues : frame.returnContinuation = .stop true) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let machine := before.machine
  have state : before = Storage.withCurrent #[] frame machine := withFrames stack
  obtain ⟨result, final, updated, holder, tracker, post⟩ :=
    emptyBackedReachesReturn program loaded options limits remaining dynamicFuel fuel dispatch span sizing validation calling
      before frame pointer count id tag concrete ready positive admitted compiler #[] stack
  obtain ⟨initialTracker, tracked, protectedTags⟩ := post.sameProtections
  obtain ⟨treeNode, node, hidden⟩ := post.node
  obtain ⟨thread, active⟩ := post.active
  obtain ⟨old, fresh, originalLive, sameBytes, transfer, vacant, ranks, unheld⟩ := post.transfer
  have originalDestination : PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer 0 := by
    rw [← state]
    exact physical
  have allocationProfile : AllocationProfile (Storage.withCurrent #[] frame machine) frame preparedTagHeadroom := by
    rw [← state]
    exact admitted.allocations
  obtain ⟨done, returned, empty, _⟩ :=
    emptyBackedPhysicalTail options limits remaining fuel span validation admitted.profile.debugOff
      frame result machine final pointer id tag concrete initialTracker tracker tracked post.tracked protectedTags.symm
      updated post.sourceLive holder treeNode post.tagAt node hidden post.dormant thread active originalDestination
      old originalLive sameBytes fresh transfer vacant ranks unheld preparedTagHeadroom allocationProfile post.returnPlace (congrArg (·.borrowTracker) post.extra)
      post.addresses post.extras post.otherLive post.body post.location post.resultSlot
      ((congrArg (·.dataRace) post.extra).trans admitted.stack.calleeClocksOff)
      (post.continuation.trans continues) post.immediate (post.varargs.trans admitted.stack.noVarargs)
      post.ghost post.shallow post.unchecked post.noGc post.fixed post.race post.backend
  exact GeneratedSafetyOfTrace.required program loaded cfg limits _ done admitted.entered
    (SuccessfulTrace.append post.trace returned) (by rw [state]; simp [empty,Storage.withCurrent])

#print axioms emptyBackedPhysicalRejects
end DuplicatePrefix.CanonicalCallDomain

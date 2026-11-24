import EmptyBackedCanonicalEntry
import CanonicalCallRelease
import duplicate_prefix.RootLocalBoolReturn
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Verification
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

/-- A prepared backed empty slice rejects every nonzero count and returns
false to a cached Boolean local. The two temporary shared children use
available storage in the actual tag table; the original tag remains dormant. -/
theorem emptyBackedCachedRejects
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
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
    (compiler : InitialCompilerControl before frame) (destination : CachedBoolDestination before frame)
    (ledger : ∃ tracked, frame.extra.borrowTracker = some tracked ∧ tracked.protectedTags = argumentLedger pointer) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  obtain ⟨older, caller, index, target, unwind, original, oldBool, stack, continuation, targetFits,
    saved, callerType, found, cached, live, callerClocks⟩ := destination.localSlot
  let frames := older.push caller
  obtain ⟨result, final, updated, holder, finalTracker, reached⟩ :=
    emptyBackedReachesReturn program loaded options limits remaining dynamicFuel fuel dispatch span sizing validation calling
      before frame pointer count id tag concrete ready positive admitted compiler frames stack
  obtain ⟨old, owned, beforeTracked, ownedFrame, _⟩ := admitted.allocations.ledger
  have rowsEq : owned.protectedTags = #[(id,tag)] := by
    obtain ⟨actual, present, savedRows⟩ := ledger
    have same : actual = owned := Option.some.inj (present.symm.trans ownedFrame)
    subst actual
    exact savedRows.trans (by simp [argumentLedger, concrete])
  obtain ⟨bound, localResult⟩ := Array.getElem?_eq_some_iff.mp reached.resultSlot
  obtain ⟨destBound, dest⟩ := Array.getElem?_eq_some_iff.mp found
  obtain ⟨threadAfter, activeAfter⟩ := reached.active
  obtain ⟨newNode, liveNode, unexposed⟩ := reached.node
  have noRelease : StackPopRelease.Plan finalTracker.global.protectedTags owned.protectedTags.toList final.memory final.memory := by
    rw [rowsEq]
    exact prependDormantRelease final.memory final.memory reached.sourceLive reached.dormant reached.tagAt liveNode unexposed
      finalTracker.global.protectedTags [] (.nil _)
  have returnStep := RootLocalBoolReturn.step_with_plan options limits remaining span admitted.profile.debugOff fuel validation
    older caller result final false reached.body reached.location bound (congrArg LocalState.value localResult)
    (congrArg LocalState.layout localResult) ((congrArg (·.dataRace) reached.extra).trans admitted.stack.calleeClocksOff)
    index destBound oldBool ((congrArg LocalState.value dest).trans live) ((congrArg LocalState.layout dest).trans cached)
    callerClocks (by rw [reached.returnPlace, saved]; rfl) target unwind (reached.continuation.trans continuation) reached.immediate
    (reached.varargs.trans admitted.stack.noVarargs) finalTracker owned reached.tracked (by rw [reached.extra]; exact ownedFrame)
    final.memory noRelease threadAfter activeAfter reached.unchecked reached.noGc reached.fixed reached.ghost reached.shallow
  apply DuplicatePrefix.GeneratedSafetyOfTrace.required program loaded _ limits _ _ admitted.entered
    (SuccessfulTrace.append reached.trace (.next returnStep (.refl _)))
  rw [stack]
  simp [Storage.withCurrent]

#print axioms emptyBackedCachedRejects
end
end DuplicatePrefix.CanonicalCallDomain

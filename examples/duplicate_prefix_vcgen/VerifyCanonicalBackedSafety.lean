import VerifyCanonicalSafety
import VerifyEmptyBackedCached
import VerifyEmptyBackedPhysical
import VerifyEmptyWildcardCanonical

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows

set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

/-- The concrete empty source needs room for the two zero-width reborrows.
A physical output may use an admitted byte window in that allocation or in a separate one. -/
structure EmptyBackedResources
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (id : AllocId) : Prop where
  capacity : ∀ entry, before.machine.memory.live[id]? = some entry →
    RetagInsertionCapacity.Ready entry.allocation.extra ∧ entry.allocation.extra.nodes.size + 2 < 2^32

/-- The safety VC from the saved standalone MIR holds for each prepared
count, with the physical or cached return protocol. Empty inputs may have
no provenance, name a concrete allocation, or use wildcard provenance whose
zero-width address lookup selects no allocation. A concrete empty argument
requires room for its two zero-width reborrows. -/
theorem safetyForPreparedCallWithBackedEmpty
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (dynamic : options.place.dynamicFuel = sizeFuel+1) (dispatchFuel : limits.callDispatch = dispatch+1)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (length count : UInt64)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer length count)
    (compiler : InitialCompilerControl before frame)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (source : length ≠ 0 → ∀ id tag, pointer.provenance = some (.concrete id tag) →
      ∀ allocation, before.machine.memory.live[id]? = some allocation → CopySourceResources allocation)
    (empty : length = 0 → count ≠ 0 → match pointer.provenance with
      | none => True
      | some (.concrete id _) => EmptyBackedResources before id
      | some .wildcard => EmptyWildcardLocalValidator.Unresolved
          before.machine.user.addresses before.machine.memory pointer.offset.bytes) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  by_cases backed : length = 0 ∧ count ≠ 0
  · obtain ⟨zeroLength, nonzeroCount⟩ := backed
    have resource := empty zeroLength nonzeroCount
    cases actual : pointer.provenance with
    | none =>
      exact safetyForPreparedCall program loaded options limits remaining sizeFuel fuel dispatch span validation statementFuel
        dynamic dispatchFuel before frame pointer length count admitted compiler outerRank innerRank source (fun _ _ => actual)
    | some provenance =>
      cases provenance with
      | wildcard =>
        rw [actual] at resource
        subst length
        exact allCountsEmptyWildcard program loaded options limits remaining sizeFuel fuel dispatch span dynamic
          validation dispatchFuel before frame pointer count actual resource admitted compiler
      | concrete id tag =>
        rw [actual] at resource
        subst length
        cases admitted.destination with
        | physicalRoot stack continuation physical =>
          exact emptyBackedPhysicalRejects program loaded options limits remaining sizeFuel fuel dispatch span dynamic
            validation dispatchFuel before frame pointer count id tag actual resource.capacity nonzeroCount admitted compiler
            physical stack continuation
        | cachedCaller destination ledger =>
          exact emptyBackedCachedRejects program loaded options limits remaining sizeFuel fuel dispatch span dynamic
            validation dispatchFuel before frame pointer count id tag actual resource.capacity nonzeroCount admitted compiler
            destination ledger
  · exact safetyForPreparedCall program loaded options limits remaining sizeFuel fuel dispatch span validation statementFuel
      dynamic dispatchFuel before frame pointer length count admitted compiler outerRank innerRank source
      (fun zeroLength nonzeroCount => (backed ⟨zeroLength,nonzeroCount⟩).elim)

#print axioms safetyForPreparedCallWithBackedEmpty
end DuplicatePrefix.CanonicalCallDomain

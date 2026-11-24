import CanonicalPreparedCachedResources
import VerifyZeroPhysicalCanonical
import VerifyEmptyIntegerCanonical
import VerifyEmptyIntegerPhysical

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open SourceDomain PreparedArguments CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The saved MIR safety VC under the prepared-call domain, for both return
carriers and every count. For nonempty input the additional condition is the
ordinary backing and append capacity of the allocation actually named by the
argument. For a nonzero count on an empty input this version admits a pointer
with no provenance. -/
theorem safetyForPreparedCall
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
    (empty : length = 0 → count ≠ 0 → pointer.provenance = none) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  by_cases zeroCount : count = 0
  · subst count
    exact CanonicalCallDomain.zeroCount program loaded options limits remaining span fuel validation before frame pointer length
      admitted compiler
  by_cases zeroLength : length = 0
  · have noProvenance := empty zeroLength zeroCount
    subst length
    cases admitted.destination with
    | physicalRoot stack continuation physical =>
      exact emptyIntegerPhysicalRejects program loaded options limits remaining sizeFuel fuel dispatch span dynamic validation
        dispatchFuel before frame pointer count noProvenance zeroCount admitted compiler physical stack continuation
    | cachedCaller destination _ =>
      exact emptyIntegerRejects program loaded options limits remaining sizeFuel fuel dispatch span dynamic validation dispatchFuel
        before frame pointer count noProvenance zeroCount admitted compiler destination
  · have positive : 0 < length := UInt64.lt_iff_toNat_lt.mpr (by
      have nonzero : length.toNat ≠ 0 := by
        intro none
        exact zeroLength (UInt64.toNat.inj (by simp [none]))
      simp only [UInt64.toNat_zero]
      omega)
    cases admitted.destination with
    | physicalRoot stack _ _ =>
      let machine := before.machine
      have state : before = Storage.withCurrent #[] frame machine := withFrames stack
      rw [state] at admitted compiler ⊢
      exact nonemptyPhysical program loaded options limits remaining sizeFuel fuel dispatch span validation statementFuel
        dynamic dispatchFuel frame machine pointer length count positive admitted compiler outerRank innerRank (source zeroLength)
    | cachedCaller destination ledger =>
      exact nonemptyCached program loaded options limits remaining sizeFuel fuel dispatch span validation statementFuel
        dynamic dispatchFuel frame before pointer length count positive admitted compiler outerRank innerRank destination ledger
        (source zeroLength)

#print axioms safetyForPreparedCall
end DuplicatePrefix.CanonicalCallDomain

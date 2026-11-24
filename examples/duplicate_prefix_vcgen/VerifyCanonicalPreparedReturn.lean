import VerifyCanonicalBackedSafety
import VerifyZeroNonemptyPhysicalShared
import VerifyNonemptyPhysicalSharedRejected
import VerifyNonemptyPhysicalSharedAccepted
import PreparedAliasCompatibility

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows

set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

open SourceDomain

/-- The generated safety condition for every count under the prepared-call
contract. A physical output can share the source allocation outside the
source's byte span. The existing cached and empty carriers are also admitted. -/
theorem safetyForPreparedReturn
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (dynamic : options.place.dynamicFuel = sizeFuel+1) (dispatchFuel : limits.callDispatch = dispatch+1)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (length count : UInt64)
    (admitted : PreparedReturnDomain program options remaining preparedTagHeadroom span before frame pointer length count)
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
  cases admitted with
  | legacy call =>
    exact safetyForPreparedCallWithBackedEmpty program loaded options limits remaining sizeFuel fuel dispatch span
      validation statementFuel dynamic dispatchFuel before frame pointer length count call compiler outerRank innerRank source empty
  | physical call positive stack continuation physical shared =>
    by_cases zero : count = 0
    · subst count
      exact zeroCountNonemptyPhysicalShared program loaded options limits remaining span fuel validation before frame
        pointer length positive call compiler physical stack continuation
    · have nonempty : length ≠ 0 := by
        intro equal
        rw [equal] at positive
        exact UInt64.lt_irrefl _ positive
      let machine := before.machine
      have state : before = Storage.withCurrent #[] frame machine := withFrames stack
      have needed := source nonempty
      rw [state] at call compiler physical needed ⊢
      by_cases rejected : count > length/2
      · exact nonemptyPhysicalSharedRejected program loaded options limits remaining sizeFuel fuel dispatch span
          validation dynamic dispatchFuel frame machine pointer length count positive rejected continuation physical
          call compiler needed
      · exact nonemptyPhysicalSharedAccepted program loaded options limits remaining sizeFuel fuel dispatch span
          validation statementFuel dynamic dispatchFuel frame machine pointer length count positive zero
          rejected continuation physical shared call compiler outerRank innerRank needed

#print axioms safetyForPreparedReturn
end DuplicatePrefix.CanonicalCallDomain

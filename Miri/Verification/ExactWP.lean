import Miri.Verification.AggregateWP
import Miri.Verification.CallDispatchWP
import Miri.Verification.CallLifecycleWP
import Miri.Verification.CanonicalStepWP
import Miri.Verification.AssertPanicWP
import Miri.Verification.DiscriminantWP
import Miri.Verification.CopyTreeWP
import Miri.Verification.CopyLoadObservationWP
import Miri.Verification.DropWP
import Miri.Verification.NondivergingIntrinsicWP
import Miri.Verification.PlaceMentionWP
import Miri.Verification.StorageLiveWP
import Miri.Verification.MemoryObservationWP
import Miri.Verification.MemoryWP
import Miri.Verification.OperandPlaceWP
import Miri.Verification.PlaceReadWriteWP
import Miri.Verification.ScalarMemoryWP
import Miri.Verification.RvalueWP
import Miri.Verification.TreeBorrowSetupWP
import Miri.Verification.TreeDiagnosticWP
import Miri.Verification.TreeEffectsWP
import Miri.Verification.TreeNormalRangeWP
import Miri.Verification.TreeObservationWP
import Miri.Verification.TreeOverlapWP
import Miri.Verification.TreeWildcardPairWP
import Miri.Verification.TreeRangeCursorsWP
import Miri.Verification.TreeRangeAccess
import Miri.Verification.TreeRangeOutcomeWP
import Miri.Verification.TreeRangeInitWP
import Miri.Verification.TreeReadWriteWP
import Miri.Verification.TreeTopologyWP
import Miri.Verification.TreeVisitWP
import Miri.Verification.TypedRetagWP

/-! Import this module to register the exact driver, memory and Tree Borrows
weakest-precondition rules for `vcgen`. -/

namespace Miri.Verification

/-- Open the concrete rule for a selected MIR instruction. Keep each inner
operation named so clients can simplify just the branch their goal uses. -/
macro "miri_instruction_wp" : tactic =>
  `(tactic| simp only [DiscriminantWP.statementPre_setDiscriminant,
    StorageLiveWP.statement_storageLive, PlaceMentionWP.canonical_statementPre,
    NondivergingIntrinsicWP.statementPre_intrinsic, DropWP.selectedDrop_eq,
    AssertPanicWP.selectedAssert_eq, AssertPanicWP.selectedUnwindTerminate_eq])

end Miri.Verification

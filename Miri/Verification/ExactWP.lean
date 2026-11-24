import Miri.Verification.AggregateWP
import Miri.Verification.CallDispatchWP
import Miri.Verification.CallLifecycleWP
import Miri.Verification.CanonicalStepWP
import Miri.Verification.MemoryWP
import Miri.Verification.ScalarMemoryWP
import Miri.Verification.RvalueWP
import Miri.Verification.TreeBorrowSetupWP
import Miri.Verification.TreeDiagnosticWP
import Miri.Verification.TreeEffectsWP
import Miri.Verification.TreeRangeAccess
import Miri.Verification.TreeRangeInitWP
import Miri.Verification.TreeReadWriteWP
import Miri.Verification.TreeTopologyWP
import Miri.Verification.TreeVisitWP
import Miri.Verification.TypedRetagWP

/-! Import this module to register the exact driver, memory and Tree Borrows
weakest-precondition rules for `vcgen`. -/

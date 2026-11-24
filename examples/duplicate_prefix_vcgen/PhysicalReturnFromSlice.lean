import CanonicalPhysicalWindow
import RootPhysicalRejectionPrefix
import PhysicalEndCall
import duplicate_prefix.LenExitFacts
import duplicate_prefix.AllocationBacktrace
import RetainedSlicePhysicalPlan
import CanonicalCallDomain
import duplicate_prefix.RootWindowPhysicalReturn

namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open Miri.TreeBorrows Miri.Verification
open CanonicalCallDomain SourceDomain ArchiveForestProjection GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame

private theorem zeroTickFields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineState) :
    let after := RootZeroCompleteState.tick options remaining span machine
    after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
      after.threads = machine.threads ∧ after.dataRace = machine.dataRace ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.ghost = machine.user.payload.ghost ∧
      after.user.payload.validation = machine.user.payload.validation ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  dsimp only
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem grantForByte {tree : BorrowTree} {start : Size} {source : UniIndex}
    {tags : ProtectedTags} (grant : ByteWriteGrant tree start.bytes source tags)
    (extent : ReleaseRange tree source start 1) :
    OwnedOn (fun row => LocationRights tree row tags source)
      start.bytes (start.bytes + 1) tree.locations := by
  have fits : start.bytes.toNat + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt extent.extent tree.locations.size.bytes.toNat_lt
  have endByte : (start.bytes + 1).toNat = start.bytes.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  intro position inside _ starts stops
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  have below : segment.range.start ≤ start.bytes := by
    rw [UInt64.le_iff_toNat_le]
    change segment.range.start.toNat < (start.bytes + 1).toNat at starts
    omega
  exact grant segment member below (UInt64.lt_iff_toNat_lt.mpr stops)

/-- Perform the real physical Return once the source has produced its Boolean.
The two protected ranges are released through the existing keyed heap. -/
theorem returnPhysicalWithRetainedSlice
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (fuel : Nat) (validation : options.limits.validation = fuel+1)
    (debugOff : options.place.debugAssertions = false)
    (result : Frame) (machine : MachineState)
    (pointer : Pointer (Option Provenance)) (length : UInt64) (positive : 0 < length)
    (ready : RetainedSlice machine)
    (concrete : pointer.provenance = some (.concrete ready.id ready.tag))
    (physical : PhysicalBoolDestination (Storage.withCurrent #[] result machine) result pointer length)
    (backing : ∀ key entry, key ≠ ready.id → machine.memory.live[key]? = some entry →
      machine.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) =
        some (key, {weakMemory := none, backtrace := (AllocationBacktrace.get
          machine.user.payload.payload.user.runtime.extras.allocations key)}))
    (coherentSlice : CoherentForest ready.entry.allocation.extra)
    (lower upper : UInt64) (footprint : CopyHolderRights.Footprint ready.entry.allocation.extra
      ready.tracker.global.protectedTags ready.source ready.source lower upper)
    (body : result.body = RootBody.reflected.body.body) (location : result.location = .mir ⟨10,0⟩)
    (value : Bool)
    (slot : result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool value))),some RootCompilerFacts.boolLayout⟩)
    (noLocalClocks : result.extra.dataRace = none)
    (continues : result.returnContinuation = .stop true)
    (immediate : ZeroImmediateFacts.AllImmediate result) (noVarargs : result.vaList = #[])
    (ghostOff : machine.user.payload.ghost = false) (shallowMode : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (raceOff : machine.dataRace = none)
    (backendOff : machine.user.payload.payload.user.backend = .none) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ final, SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] result machine) final ∧
      final.stack.frames = #[] ∧ ExecutionMachine.step cfg limits () final = (final,.ok false) := by
  obtain ⟨place, id, allocation, relative, tag, base, tracker, owned, source, returnTag, holder,
    saved, layout, aligned, live, mutable, storage, mask, maskLength, provenance, fits, ptr, _,
    address, addressFits, cached, tracked, trackedFrame, ledger, _, coherent, sourceKey,
    sourceNode, holderKey, holderNode, extent, writeGrant, _, separated⟩ := physical.storage
  have same : tracker = ready.tracker := Option.some.inj (tracked.symm.trans ready.tracked)
  subst tracker
  let tracker := ready.tracker
  obtain ⟨node, atNode, nodeTag, parent, hidden⟩ := holderNode
  have ownsTag : returnTag ∈ owned.protectedTags.toList.map Prod.snd := by rw [ledger]; simp
  obtain ⟨afterTree, outputReleased, treeFrame, afterCoherent, treeSize, owners⟩ :=
    physicalReleasePreservesParent allocation.allocation.extra tracker.global owned returnTag holder source
      node relative holderKey atNode nodeTag parent hidden coherent extent ownsTag (grantForByte writeGrant extent)
  have nonempty : length ≠ 0 := by intro eq; rw [eq] at positive; exact (UInt64.lt_irrefl _ positive)
  have disjoint := separated nonempty ready.id ready.tag concrete
  have ledgerRows : owned.protectedTags = #[(ready.id,ready.tag),(id,returnTag)] := by
    simpa [argumentLedger,concrete] using ledger
  obtain ⟨finalHeap, release, outputLive⟩ :=
    ready.physicalPlan owned id returnTag allocation afterTree ledgerRows disjoint live outputReleased coherentSlice lower upper footprint
  let charged := PtrMetadataReturn.accountedMachine options remaining span machine
  have tails := zeroTickFields options remaining span machine
  have trackerNow : charged.borrowTracker = some tracker := tails.2.1.trans ready.tracked
  have legalRelease : StackPopRelease.Plan tracker.global.protectedTags owned.protectedTags.toList
      charged.memory finalHeap := by rw [show charged.memory = machine.memory from tails.1]; exact release
  have liveThread : charged.threads.activeThread? = some ready.thread := by
    rw [show charged.threads = machine.threads from tails.2.2.1]
    exact ready.active
  let released := ActualPopPlan.released charged finalHeap tracker owned
  let passed := GenericPopFrame.afterRelevanceAt #[] result released (ready.thread.topUserRelevantFrame.getD 0)
  let retState : State := ⟨⟨#[]⟩, passed⟩
  have resultHeap : retState.machine.memory = finalHeap := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  let finalTracker := {tracker with global := tracker.global.endCall owned}
  have resultTracker : retState.machine.borrowTracker = some finalTracker := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultUser : retState.machine.user = charged.user := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultRace : retState.machine.dataRace = charged.dataRace := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have addresses : retState.machine.user.addresses = machine.user.addresses :=
    (congrArg (·.addresses) resultUser).trans tails.2.2.2.2.1
  have extrasPreserved : retState.machine.user.payload.payload.user.runtime.extras =
      machine.user.payload.payload.user.runtime.extras :=
    (congrArg (·.payload.payload.user.runtime.extras) resultUser).trans tails.2.2.2.2.2.2.2.2
  have race : retState.machine.dataRace = none :=
    resultRace.trans (tails.2.2.2.1.trans raceOff)
  have backend : retState.machine.user.payload.payload.user.backend = .none :=
    (congrArg (·.payload.payload.user.backend) resultUser).trans (tails.2.2.2.2.2.2.2.1.trans backendOff)
  have beforeGhost : charged.user.payload.ghost = false := tails.2.2.2.2.2.1.trans ghostOff
  have ghost : retState.machine.user.payload.ghost = false := (congrArg (·.payload.ghost) resultUser).trans beforeGhost
  have shallow : retState.machine.user.payload.validation = .Shallow :=
    (congrArg (·.payload.validation) resultUser).trans (tails.2.2.2.2.2.2.1.trans shallowMode)
  have relativeFits := UInt64.lt_iff_toNat_lt.mp fits
  let window := physicalWindowAfterRelease retState.machine place id tag base relative allocation afterTree
    layout aligned (by rw [resultHeap]; exact outputLive) (by rw [addresses]; exact cached)
    mutable storage mask maskLength provenance fits ptr address addressFits
  have newKey : window.entry.allocation.extra.indexOfTag window.tag = some source := by
    change afterTree.indexOfTag tag = some source
    rw [treeFrame]
    exact sourceKey
  obtain ⟨originalSource, sourceHere, _⟩ := sourceNode
  have newNode : window.entry.allocation.extra.nodeAt source = some originalSource := by
    change afterTree.nodeAt source = some originalSource
    rw [treeFrame]
    exact sourceHere
  obtain ⟨root, rootEq⟩ := extent.root
  have roots : window.entry.allocation.extra.roots = #[root] := by
    change afterTree.roots = #[root]
    rw [treeFrame]
    exact rootEq
  have bound : window.offset.toNat + 1 ≤ window.entry.allocation.extra.locations.size.bytes.toNat := by
    change relative.bytes.toNat + 1 ≤ afterTree.locations.size.bytes.toNat
    rw [treeSize]
    exact extent.extent
  have effects : let ctx := (DuplicatePrefixPhysicalContexts.canonical options remaining span).writeContext
      (ctx.extras.get retState.machine.user).allocations.find? (·.1 == id) =
        some (id, {weakMemory := none, backtrace := (AllocationBacktrace.get
          ((ctx.extras.get retState.machine.user).allocations) id)}) := by
    dsimp only
    let actualRows := retState.machine.user.payload.payload.user.runtime.extras.allocations
    change actualRows.find? (·.1 == id) =
      some (id,{weakMemory := none, backtrace := AllocationBacktrace.get actualRows id})
    dsimp only [actualRows]
    rw [extrasPreserved]
    exact backing id allocation (separated (by intro eq; rw [eq] at positive; exact (UInt64.lt_irrefl _ positive))
      ready.id ready.tag concrete).symm live
  have addressBound : place.mplace.ptr.offset.bytes.toNat + 1 < 2^64 := by omega
  obtain ⟨valid, bool⟩ := Array.getElem?_eq_some_iff.mp slot
  obtain ⟨updated, returned, stopped, _, _, _⟩ :=
    RootWindowPhysicalReturn.return_step_terminal options remaining span limits fuel validation debugOff
      result machine charged rfl unchecked gc fixed tracker owned trackerNow trackedFrame finalHeap legalRelease
      ready.thread liveThread retState rfl body location valid value
      (congrArg LocalState.value bool) (congrArg LocalState.layout bool) noLocalClocks beforeGhost
      continues immediate noVarargs place window (by rw [saved]; rfl) finalTracker resultTracker race backend ghost shallow
      source root originalSource newNode newKey roots afterCoherent bound owners effects addressBound
  exact ⟨_, .next returned (.refl _), rfl, stopped⟩

#print axioms returnPhysicalWithRetainedSlice
end DuplicatePrefix.RootZeroShallowReturn

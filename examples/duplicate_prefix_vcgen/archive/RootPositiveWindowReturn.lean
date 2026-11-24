import PhysicalEndCall
import duplicate_prefix.RootPositivePhysicalPop
import duplicate_prefix.RootWindowPhysicalReturn

namespace DuplicatePrefix.RootPositiveWindowReturn
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PreparedArguments SourceDomain RootPositiveCachedReturn RootPositivePhysicalPop GeneralRangeMapOrigins ArchiveForestProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

/-- Geometry and backing of the original saved physical place, independent of
the body instructions and the protector release plan. -/
structure Slot (before : RootPositivePhysicalPop.MachineState) (frame : CompilerFrameContext.ActualFrame) where
  place : MPlaceTy Provenance
  id : AllocId
  sourceTag : BorTag
  protectedTag : BorTag
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  capacity : UInt64
  layout : place.layout = RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned = none
  present : before.memory.live[id]? = some entry
  cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  pointer : place.mplace.ptr = Pointer.new (some (.concrete id sourceTag)) (Size.ofBytes (base+offset))
  bounds : offset.toNat+1 ≤ capacity.toNat
  size : entry.allocation.byteSize = Size.ofBytes capacity
  bytes : entry.allocation.len = capacity.toNat
  mutable : entry.allocation.mutability = .Mut
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = Size.ofBytes capacity
  provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  destination : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩
  extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
    some (id,{weakMemory := none,backtrace := (AllocationBacktrace.get
      before.user.payload.payload.user.runtime.extras.allocations id)})
  addressBound : place.mplace.ptr.offset.bytes.toNat+1 < 2^64

structure ReleasedSlot (tracker : MachineHooks.BorrowState) (owned : FrameState)
    (slot : Slot machine frame) where
  tree : BorrowTree
  released : slot.entry.allocation.extra.releaseProtector slot.protectedTag tracker.global.protectedTags =
    ⟨tree,.Released⟩
  source : UniIndex
  root : UniIndex
  node : TreeNode
  found : tree.nodeAt source = some node
  key : tree.indexOfTag slot.sourceTag = some source
  roots : tree.roots = #[root]
  coherent : CoherentForest tree
  fits : slot.offset.toNat+1 ≤ tree.locations.size.bytes.toNat
  owners : OwnedOn (fun row => LocationRights tree row (tracker.global.endCall owned).protectedTags source)
    slot.offset (slot.offset+1) tree.locations

/-- Derive the physical slot's actual release and the parent write grant
from its original one-byte holder permissions and the source frame ledger. -/
theorem released_slot_of_rights
    {machine : RootPositivePhysicalPop.MachineState} {frame : CompilerFrameContext.ActualFrame}
    (slot : Slot machine frame) (tracker : MachineHooks.BorrowState) (owned : FrameState)
    (parent holder : UniIndex) (parentNode holderNode : TreeNode)
    (sourceKey : slot.entry.allocation.extra.indexOfTag slot.sourceTag = some parent)
    (sourceNode : slot.entry.allocation.extra.nodeAt parent = some parentNode)
    (holderKey : slot.entry.allocation.extra.indexOfTag slot.protectedTag = some holder)
    (present : slot.entry.allocation.extra.nodeAt holder = some holderNode)
    (tagMatches : holderNode.tag = slot.protectedTag)
    (edge : holderNode.parent = some parent) (unexposed : holderNode.isExposed = false)
    (coherent : CoherentForest slot.entry.allocation.extra)
    (extent : CanonicalCallDomain.ReleaseRange slot.entry.allocation.extra holder (Size.ofBytes slot.offset) 1)
    (ownedTag : slot.protectedTag ∈ owned.protectedTags.toList.map Prod.snd)
    (grant : OwnedOn (fun row => LocationRights slot.entry.allocation.extra row tracker.global.protectedTags holder)
      slot.offset (slot.offset+1) slot.entry.allocation.extra.locations) :
    Nonempty (ReleasedSlot tracker owned slot) := by
  obtain ⟨tree, exactRelease, shape, formed, size, owners⟩ :=
    CanonicalCallDomain.physicalReleasePreservesParent slot.entry.allocation.extra tracker.global owned slot.protectedTag
      holder parent holderNode (Size.ofBytes slot.offset) holderKey present tagMatches edge unexposed coherent extent ownedTag grant
  obtain ⟨root, roots⟩ := extent.root (by decide)
  refine ⟨⟨tree,exactRelease,parent,root,parentNode,?_,?_,?_,formed,?_,owners⟩⟩
  · rw [shape]
    exact sourceNode
  · rw [shape]
    exact sourceKey
  · rw [shape]
    exact roots
  · rw [size]
    exact extent.extent

/-- Connect the real copy tree, ordered protector stack pop, and ordinary
typed Boolean store at the saved byte of an arbitrary allocation. -/
theorem returns
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1)
    (frame result done : CompilerFrameContext.ActualFrame) (machine last : RootPositivePhysicalPop.MachineState)
    (length count base : UInt64) (copyTag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent #[] frame machine) length)
    (rights : ExclusiveRegion (Storage.withCurrent #[] frame machine) length storage copyTag)
    (holder : Holder storage.entry.allocation.extra rights.tracker.global.protectedTags copyTag rights.source
      storage.relativeStart length)
    (disjoint : count.toNat + count.toNat ≤ length.toNat)
    (allocation : Allocation Provenance BorrowTree)
    (copy : RootPositiveRootSuffix.ReadyAfterCopy options remaining span #[] frame machine
      length count base copyTag storage rights result last allocation)
    (cleanup : RootSuccessCleanupFacts.Shape result done RootCompilerFacts.boolLayout (.scalar (.fromBool true)))
    (body : frame.body = RootBody.reflected.body.body)
    (clocks : frame.extra.dataRace = none)
    (varargs : frame.vaList = #[])
    (continuation : frame.returnContinuation = .stop true)
    (slot : Slot machine frame) (separate : slot.id ≠ storage.id)
    (owned : FrameState) (ownedBy : frame.extra.borrowTracker = some owned)
    (ledger : owned.protectedTags = #[(storage.id,holder.tag),(slot.id,slot.protectedTag)])
    (releasedSlot : ReleasedSlot rights.tracker owned slot) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let start := Storage.withCurrent #[] {done with location := .mir ⟨10,0⟩}
      (SourceControl.accounted config.terminators (Storage.withCurrent #[] done last)).machine
    ∃ final, ExecutionMachine.step config limits () start = (final,.ok true) ∧
      ExecutionMachine.step config limits () final = (final,.ok false) ∧ final.stack.frames = #[] := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let tick := LanguageZeroStep.accountedMachine options remaining span
  let initial := tick last
  let charged := tick initial
  let clean := {done with location := .mir ⟨10,0⟩}
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let physical := contexts.writeContext
  obtain ⟨thread,released,active,tracked,plan,lookup,nextTracker,addresses,backing,noRace,backend,ghost,shallow,_⟩ :=
    RootPositivePhysicalPop.prepare options remaining span frame result done machine last length count base copyTag storage rights
      holder disjoint allocation copy slot.id slot.protectedTag slot.entry slot.present releasedSlot.tree releasedSlot.released
      separate owned ledger
  let state := afterPop clean charged released rights.tracker owned thread
  let tracker := {rights.tracker with global := rights.tracker.global.endCall owned}
  let entry := {slot.entry with allocation := slot.entry.allocation.setExtra releasedSlot.tree}
  let window : PhysicalBoolWindowWrite.Window state.machine slot.place :=
    { layout := slot.layout
      aligned := slot.aligned
      id := slot.id
      tag := slot.sourceTag
      entry := entry
      base := slot.base
      offset := slot.offset
      capacity := slot.capacity
      live := lookup
      cachedBase := by rw [addresses]; exact slot.cached
      pointer := slot.pointer
      bounds := slot.bounds
      size := slot.size
      bytes := slot.bytes
      mutable := slot.mutable
      maskValid := slot.maskValid
      maskLength := slot.maskLength
      provenance := ProvenanceCopy.WellFormed.pointerBounds slot.provenance }
  have backingReady :
      (physical.extras.get state.machine.user).allocations.find? (fun row => row.1 == slot.id) =
      some (slot.id,{weakMemory := none,backtrace := (AllocationBacktrace.get
        ((physical.extras.get state.machine.user).allocations) slot.id)}) := by
    change state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slot.id) =
      some (slot.id,{weakMemory := none,backtrace := (AllocationBacktrace.get
        state.machine.user.payload.payload.user.runtime.extras.allocations slot.id)})
    rw [backing]
    exact slot.extras
  have control : cfg.terminators.getControl initial.user = TerminatorClock.advance (cfg.terminators.getControl last.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have unchecked : (cfg.terminators.getControl initial.user).checkedArithmetic = false := by rw [control]; exact copy.unchecked
  have noGc : (cfg.terminators.getControl initial.user).gcInterval = 0 := by rw [control]; exact copy.noGc
  have fixed : initial.threads.fixedScheduling = true :=
    (congrArg (·.fixedScheduling) (CopyRootGuardState.accounted_fields options remaining span last).2.2.1).trans copy.fixed
  have ghostCharged : charged.user.payload.ghost = false :=
    (PointerAddCurrentReturn.accounted_ghost options remaining span initial).trans
      ((PointerAddCurrentReturn.accounted_ghost options remaining span last).trans copy.ghost)
  have valid0 : (0 : MIR.LocalId) < clean.locals.size := by change 0 < done.locals.size; rw [cleanup.size]; decide
  have retval : clean.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    (Array.getElem?_eq_some_iff.mp cleanup.output).2
  have recorded : clean.extra.borrowTracker = some owned :=
    (congrArg MachineHooks.FrameExtra.borrowTracker (cleanup.extra.trans copy.extra)).trans ownedBy
  obtain ⟨updated,returned,stopped,_,_,_⟩ :=
    RootWindowPhysicalReturn.return_step_terminal options remaining span limits fuel validation debug clean initial charged rfl
      unchecked noGc fixed rights.tracker owned tracked recorded released plan thread active state rfl
      (cleanup.body.trans (copy.body.trans body)) rfl valid0 true (by rw [retval]) (by rw [retval])
      (by change done.extra.dataRace = none; rw [cleanup.extra,copy.extra]; exact clocks) ghostCharged
      (cleanup.continuation.trans (copy.returnContinuation.trans continuation)) (cleanup.immediate copy.direct)
      (cleanup.varargs.trans (copy.varargs.trans varargs)) slot.place window
      (by change done.returnPlace.toRuntimePlace = _; rw [cleanup.destination,copy.returnPlace]; exact slot.destination)
      tracker nextTracker noRace backend ghost shallow releasedSlot.source releasedSlot.root releasedSlot.node
      releasedSlot.found releasedSlot.key releasedSlot.roots releasedSlot.coherent releasedSlot.fits
      releasedSlot.owners backingReady slot.addressBound
  exact ⟨CanonicalCopy.replaceAllocation state slot.id slot.entry.kind updated,returned,stopped,rfl⟩

#print axioms released_slot_of_rights
#print axioms returns
end DuplicatePrefix.RootPositiveWindowReturn

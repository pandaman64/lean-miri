import LengthFromCallOfSlice
import duplicate_prefix.RootNonzeroSharedHeap
import duplicate_prefix.TightParentDepth

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ArchiveForestProjection SourceDomain GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild
open RootZeroCompleteState PtrMetadataReturn

set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

private theorem nextTag (old next : TreeBorrows.GlobalState)
    (allocated : old.newPointerTag = .ok (next, old.nextPointerTag))
    (headroom : old.nextPointerTag.value.toNat + 1 < 18446744073709551615) :
    next.nextPointerTag.value.toNat = old.nextPointerTag.value.toNat + 1 := by
  have notMax : old.nextPointerTag.value ≠ 18446744073709551615 := by
    intro equal
    rw [equal] at headroom
    simp at headroom
  have nextNotZero : old.nextPointerTag.value + 1 ≠ 0 := by
    intro equal
    have mod := congrArg UInt64.toNat equal
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using (show old.nextPointerTag.value.toNat + 1 < 2^64 by omega))] at mod
    simp at mod
  unfold TreeBorrows.GlobalState.newPointerTag BorTag.succ BorTag.ofUInt64 at allocated
  simp [notMax,nextNotZero] at allocated
  have changeTag := congrArg (fun state : TreeBorrows.GlobalState => state.nextPointerTag.value.toNat) allocated
  rw [← changeTag]
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt (by simpa using (show old.nextPointerTag.value.toNat + 1 < 2^64 by omega))]

private theorem selectedRawFrame
    (crates : Array Nat) (state : RootState) (destination : RuntimeStackPlace Provenance)
    (thread : ThreadRecord)
    (bound : ∀ i, thread.topUserRelevantFrame = some i → i < state.stack.frames.size) :
    ∃ index current,
      FrameRelevance.top (LenPush.pushed crates state destination).stack thread.topUserRelevantFrame = some index ∧
      (LenPush.pushed crates state destination).stack.frames[index]? = some current := by
  let pushed := LenPush.pushed crates state destination
  have size : pushed.stack.frames.size = state.stack.frames.size + 1 := by
    simp [pushed, LenPush.pushed, Storage.withCurrent]
  cases cached : thread.topUserRelevantFrame with
  | some index =>
    have valid : index < pushed.stack.frames.size := by
      rw [size]
      exact Nat.lt_succ_of_lt (bound index cached)
    refine ⟨index, pushed.stack.frames[index], ?_, Array.getElem?_eq_getElem valid⟩
    simp [FrameRelevance.top]
  | none =>
    have valid : state.stack.frames.size < pushed.stack.frames.size := by omega
    refine ⟨state.stack.frames.size, pushed.stack.frames[state.stack.frames.size], ?_,
      Array.getElem?_eq_getElem valid⟩
    have nonempty : pushed.stack.frames.isEmpty = false := by simp [pushed, LenPush.pushed, Storage.withCurrent]
    change FrameRelevance.top pushed.stack none = _
    simp only [FrameRelevance.top, Option.orElse_none, nonempty, Bool.false_eq_true, ite_false, size, Nat.add_sub_cancel]


/-- Shared root and allocation state at the actual guard after slice length. -/
structure RootLengthOfSlice (config : CanonicalConfigFacts.RootConfig)
    (frames : Array CompilerFrameContext.ActualFrame) (frame result : CompilerFrameContext.ActualFrame)
    (initial final : LenExitFacts.MachineState) (root : RetainedSlice initial)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (offset len count : UInt64)
    (originalTracker : MachineHooks.BorrowState) where
  beforeRelease : BorrowTree
  branch : LengthBranchOfSlice config initial initial root entry beforeRelease offset (offset+len) len count result final
  frameExtra : result.extra = frame.extra
  place : result.returnPlace = frame.returnPlace
  continuation : result.returnContinuation = frame.returnContinuation
  varargs : result.vaList = frame.vaList
  localsIdentity : result.localsIdentity = frame.localsIdentity
  trackCallerArg : result.trackCallerArg = frame.trackCallerArg
  bystanders : ∀ i, i < 3 ∨ 13 ≤ i → result.locals[i]? = frame.locals[i]?
  uncached7 : (result.locals[7]'(by rw [branch.guard.size]; decide)).layout = none
  rootCache : frame.extra.userRelevance = 255 →
    ∃ thread, final.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some frames.size
  nodes : branch.ready.entry.allocation.extra.nodes.size ≤ entry.allocation.extra.nodes.size + 2
  nextTag : branch.ready.tracker.global.nextPointerTag.value.toNat = originalTracker.global.nextPointerTag.value.toNat + 2
  protectors : branch.ready.tracker.global.protectedTags = originalTracker.global.protectedTags
  keys : RetagInsertionCapacity.Ready branch.ready.entry.allocation.extra
  tagAge : ∀ index data, branch.ready.entry.allocation.extra.nodeAt index = some data →
    data.tag.value.toNat < branch.ready.tracker.global.nextPointerTag.value.toNat

/-- Enter the nonzero path and compute the emitted length guard's data.
The same prefix serves all nonzero counts, irrespective of the decision. -/
theorem reachesRootLengthGuardOfSlice
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64) (positive : n ≠ 0)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (uncached3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : ZeroImmediateFacts.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (sizing : options.place.dynamicFuel = sizeFuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut) (raceOff : machine.dataRace = none)
    (positiveLen : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 2) = false)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes)
    (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tracker.global.nextPointerTag = none)
    (nodeFresh : ∀ index data, entry.allocation.extra.nodeAt index = some data → data.tag ≠ tracker.global.nextPointerTag)
    (unheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : VacantRows entry.allocation.extra)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (extent : MaterializedWithin entry.allocation.extra parent offset (offset+len))
    (sourceSlot : frame.locals[1]? = some ⟨.live (.immediate (.scalarPair
      (.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len)))), some RootCompilerFacts.sliceLayout⟩)
    (ready : RetainedSlice machine)
    (sameId : id = ready.id) (sameRoot : root = ready.root) (sameHolder : parent = ready.source)
    (sameTag : parentTag = ready.tag)
    (heldUnexposed : parentNode.isExposed = false)
    (resultSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩)
    (tempSlot : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩)
    (backend : machine.user.payload.payload.user.backend = .none)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (cacheValid : ∀ index, ready.thread.topUserRelevantFrame = some index → index < frames.size + 1)
    (tagHeadroom : tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615)
    (initialKeys : RetagInsertionCapacity.Ready entry.allocation.extra)
    (keySpace : entry.allocation.extra.nodes.size + 2 < 2^32)
    (keyAge : ∀ old i, entry.allocation.extra.indexOfTag old = some i → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (nodeAge : ∀ i data, entry.allocation.extra.nodeAt i = some data → data.tag.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectedAge : ∀ old, tracker.global.protectedTags.contains old = true → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (cachedRoot : ready.thread.topUserRelevantFrame = some frames.size) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result final, SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames frame machine)
      (Storage.withCurrent frames result final) ∧
      Nonempty (RootLengthOfSlice cfg frames frame result machine final ready entry offset len n tracker) := by
  intro cfg
  let first := tracker.global.nextPointerTag
  let initial := entry.allocation.extra
  let read := initial.performNormalAccessRange parentTag (Size.ofBytes offset) (Size.ofBytes len)
    .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let inside := DedupRangeMap.new (Size.ofBytes len) sharedState
  let afterTree := (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) first inside .Frozen false).tree
  let afterEntry := {entry with allocation := entry.allocation.setExtra afterTree}
  obtain ⟨caller, after, leading, bodyC, identityC, instanceC, extraC, placeC, contC, vaC, localsIdC, trackC, sizeC, locC,
    slot0, slot7, slot8, slot9, slot10, slot11, slot12, slot13, immediateC, afterShape, heap, holds, retainedScope, vacant,
    ⟨child, selected, framed⟩, next, trackedNext, modeNext, protections, nextKey, reads, originalSlots, firstUnaffected⟩ :=
    RootNonzeroEntry.reachesLenCallWithHeap options limits remaining sizeFuel span source debugOff fuel fuelEq frames frame machine
      body identity callee location size n positive unused dead3 uncached3 dead4 dead5 uncached4 uncached5 live2 cached2 noClocks
      all tracker tracked defaultMode ghost shallow unchecked noGc fixed sizing preciseOff implicitOff id parentTag parent root
      base offset len entry fresh cached live allocationMut raceOff positiveLen bounded memoryBounds notNull cmp metadata noAlias
      coherent parentNode parentStored roots parentFound depth rank tagFresh nodeFresh unheld room aligned reuse clean bounds
      owners extent sourceSlot
  obtain ⟨grantTree, grantIndex, grantHeap, good, afterRoots, capacityEq, grantKey, childPresence, reader⟩ := reads
  have sameTree : grantTree = afterTree :=
    congrArg (fun a : LocalAllocation Provenance BorrowTree MiriMemoryKind => a.allocation.extra)
      (Option.some.inj (grantHeap.symm.trans heap))
  have sameChild : grantIndex = child := Option.some.inj ((sameTree ▸ grantKey).symm.trans selected)
  subst grantTree
  subst grantIndex
  obtain ⟨newNode, newFound, newTagEq, _⟩ := childPresence
  let second := next.global.nextPointerTag
  have secondValue := nextTag tracker.global next.global nextKey tagHeadroom
  have differentTags : first ≠ second := by
    intro equal
    have eq := congrArg (fun t : BorTag => t.value.toNat) equal
    change first.value.toNat = second.value.toNat at eq
    change second.value.toNat = first.value.toNat + 1 at secondValue
    omega
  have secondRoom : second.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change next.global.nextPointerTag.value.toNat < 18446744073709551615
    rw [secondValue]
    exact tagHeadroom
  have firstUnheld : tracker.global.protectedTags.remove first = tracker.global.protectedTags :=
    ProtectedTags.remove_of_absent tracker.global.protectedTags first unheld
  have ordered : Ancestor afterTree parent child ∧ parent ≠ child ∧
      ∀ i data, afterTree.nodeAt i = some data → Ancestor afterTree i child →
        ¬ Ancestor afterTree i parent → tracker.global.protectedTags.contains data.tag = false := by
    have certificate := framed.releaseLineage (holder := parent) ⟨parentNode, parentStored⟩ (.self parent)
      (fun data known => (congrArg TreeNode.tag (Option.some.inj (known.symm.trans newFound))).trans newTagEq)
      tracker.global.protectedTags (fun _ _ _ h impossible => (impossible h).elim)
    rwa [firstUnheld] at certificate
  have holderRead : read.tree.nodeAt parent = some parentNode := by
    rw [framed.readMetadata]
    exact parentStored
  obtain ⟨holder, holderAfter, _⟩ := framed.attached.oldEdges parent parentNode holderRead
  have holderShallow : holder.isExposed = false := by
    have result := framed.olderExposure parent ordered.2.1
    rw [holderAfter, parentStored] at result
    exact (Option.some.inj result).trans heldUnexposed
  have holderTagDiff : parentTag ≠ first := by
    intro eq
    rw [eq, tagFresh] at parentFound
    contradiction
  have holderIndexed := (framed.olderTags parentTag holderTagDiff).trans parentFound
  have freshKey : afterTree.indexOfTag second = none := by
    rw [framed.olderTags second (Ne.symm differentTags)]
    cases saved : initial.indexOfTag second with
    | none => rfl
    | some index =>
      have age := keyAge second index saved
      change second.value.toNat < first.value.toNat at age
      change second.value.toNat = first.value.toNat + 1 at secondValue
      omega
  have freshNodes : ∀ index data, afterTree.nodeAt index = some data → data.tag ≠ second := by
    intro index data saved collision
    by_cases isChild : index = child
    · subst index
      have dataEq := Option.some.inj (saved.symm.trans newFound)
      exact differentTags (newTagEq.symm.trans ((congrArg TreeNode.tag dataEq).symm.trans collision))
    · obtain ⟨previous, previousFound, preservesTag, _⟩ := framed.olderNodes index data isChild saved
      have age := nodeAge index previous previousFound
      rw [preservesTag, collision] at age
      change second.value.toNat < first.value.toNat at age
      change second.value.toNat = first.value.toNat + 1 at secondValue
      omega
  have noHeld : next.global.protectedTags.contains second = false := by
    rw [protections]
    cases value : tracker.global.protectedTags.contains second with
    | false => rfl
    | true =>
      have age := protectedAge second value
      change second.value.toNat < first.value.toNat at age
      change second.value.toNat = first.value.toNat + 1 at secondValue
      omega
  have nextCapacity := framed.readyAfterInsertion initialKeys (by omega)
    tagFresh ⟨newNode, newFound, newTagEq⟩ vacant
  have nextKeys : RetagInsertionCapacity.Ready afterTree := nextCapacity.1
  have sharedRoom : afterTree.nodes.size + 1 < 2^32 := by
    have growth := nextCapacity.2
    change afterTree.nodes.size ≤ entry.allocation.extra.nodes.size + 1 at growth
    omega
  obtain ⟨loose, boundedDepth, decreasing⟩ := good.parentDepth
  let graph : BorrowTree.ZeroProtection.ParentDepth afterTree.nodes := ⟨loose, boundedDepth, by
    intro index data present parentIndex edge
    obtain ⟨related, found⟩ := good.parentPresent index data parentIndex present edge
    exact ⟨related, found, decreasing index data parentIndex present edge⟩⟩
  obtain ⟨rankGraph, tight⟩ := BorrowTree.ZeroProtection.ParentDepth.tight afterTree.nodes graph
  have readOwners : OwnedOn (fun row => LocationAccessRights afterTree row next.global.protectedTags child .Read)
      offset (offset+len) afterTree.locations := by
    rw [protections]
    exact ownership_from_bytes afterTree.locations offset (offset+len) good.ranges _ reader
  have nextBounds : offset.toNat + len.toNat ≤ afterTree.locations.size.bytes.toNat := by
    rw [capacityEq]
    exact bounds
  let secondMachine := accountedMachine options remaining span after
  have userAfter : after.user = (tick options remaining span machine).user := congrArg (·.user) afterShape
  have threadsAfter : after.threads = machine.threads := congrArg (·.threads) afterShape
  have raceAfter : after.dataRace = machine.dataRace := congrArg (·.dataRace) afterShape
  have profileFirst := LenRuntimeProfile.accounted_flags options remaining span machine
  have profileSecond := LenRuntimeProfile.accounted_flags options remaining span after
  have threadActive : secondMachine.threads.activeThread? = some ready.thread := by
    rw [show secondMachine.threads = _ from profileSecond.2.2.2, threadsAfter]
    exact ready.active
  have fixedAfter : after.threads.fixedScheduling = true := by rw [threadsAfter]; exact fixed
  have gcAfter : (cfg.terminators.getControl after.user).gcInterval = 0 := by
    rw [userAfter]
    exact (tick_flags options remaining span machine).2.trans noGc
  have uncheckedAfter : (cfg.terminators.getControl after.user).checkedArithmetic = false := by
    rw [userAfter]
    exact (tick_flags options remaining span machine).1.trans unchecked
  have ghostAfter : secondMachine.user.payload.ghost = false := by
    change (tick options remaining span after).user.payload.ghost = false
    rw [tick_ghost, userAfter, tick_ghost]
    exact ghost
  have shallowAfter : secondMachine.user.payload.validation = .Shallow := by
    change (tick options remaining span after).user.payload.validation = .Shallow
    rw [tick_shallow, userAfter, tick_shallow]
    exact shallow
  have addressesTick (s : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
      (tick options remaining span s).user.addresses = s.user.addresses := by
    unfold tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have cachedAfter : secondMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    change ((tick options remaining span after).user.addresses.baseAddr.find? (fun row => row.allocId == id)) = _
    rw [addressesTick, userAfter, addressesTick]
    exact cached
  have arraysAfter : EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller secondMachine) =
      EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine) := by
    change secondMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types
    rw [show secondMachine.user.payload.payload.user.types = _ from profileSecond.2.2.1, userAfter]
    exact profileFirst.2.2.1
  have nextBackend : secondMachine.user.payload.payload.user.backend = .none := by
    unfold secondMachine accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    change after.user.payload.payload.user.backend = _
    rw [userAfter]
    unfold tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  let valid11 : 11 < caller.locals.size := by rw [sizeC]; decide
  let valid12 : 12 < caller.locals.size := by rw [sizeC]; decide
  let cf := LenUncachedFrontend.cachedCaller caller valid11
  let destination := (LocalPlaces.localRuntimePlace frames.size cf 11 RootCompilerFacts.usizeLayout).stackView
  let callState := Storage.withCurrent frames cf secondMachine
  obtain ⟨index, current, top, present⟩ :=
    selectedRawFrame options.userRelevantCrates callState destination ready.thread (by
      intro index saved
      simpa only [callState, Storage.withCurrent, Array.size_push] using cacheValid index saved)
  have callerSlot (i : Nat) (valid : i < caller.locals.size) {slot : LocalState Provenance LocalLayout}
      (found : caller.locals[i]? = some slot) : caller.locals[i] = slot :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans found)
  have destSlot := callerSlot 11 valid11 slot11
  have lenSource := callerSlot 12 valid12 slot12
  have bystanders (i : Nat) (different : i ≠ 11) : cf.locals[i]? = caller.locals[i]? := by
    simp [cf, LenUncachedFrontend.cachedCaller, LocalPlaces.cachePlaceLayout, Ne.symm different]
  have cfSize : cf.locals.size = 25 := by
    simpa [cf, LenUncachedFrontend.cachedCaller, LocalPlaces.cachePlaceLayout] using sizeC
  have cfSlot7 := Option.some.inj ((Array.getElem?_eq_getElem (show 7 < cf.locals.size by omega)).symm.trans
    ((bystanders 7 (by decide)).trans slot7))
  have cfSlot12 := Option.some.inj ((Array.getElem?_eq_getElem (show 12 < cf.locals.size by omega)).symm.trans
    ((bystanders 12 (by decide)).trans slot12))
  let prepared : BeforeLengthReturn cf n := {
    size := cfSize
    body := bodyC.trans body
    identity := identityC.trans identity
    callee := instanceC.trans callee
    temp := _
    slot0 := (bystanders 0 (by decide)).trans (slot0.trans resultSlot)
    live7 := congrArg (·.value) cfSlot7
    slot8 := (bystanders 8 (by decide)).trans slot8
    slot9 := (bystanders 9 (by decide)).trans slot9
    slot10 := (bystanders 10 (by decide)).trans slot10
    cached11 := by simp [cf, LenUncachedFrontend.cachedCaller, LocalPlaces.cachePlaceLayout]
    live12 := congrArg (·.value) cfSlot12
    slot13 := (bystanders 13 (by decide)).trans (slot13.trans tempSlot)
    immediate := ZeroImmediateFacts.all_immediate_cache caller 11 RootCompilerFacts.usizeLayout valid11 immediateC
    noClocks := (congrArg (·.dataRace) extraC).trans noClocks }
  have runtimeSet : (PreparedContracts.actualConfig options () remaining span).access.runtime =
      cfg.access.runtime := (CanonicalConfigFacts.actual_access_runtime options () remaining span).trans
      (CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span).symm
  have supplied : caller.locals[12].value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
        (Pointer.new (.concrete id first) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm) := by
    rw [runtimeSet]
    exact congrArg (·.value) lenSource
  have nextHolder : afterTree.nodeAt ready.source = some holder := by rw [← sameHolder]; exact holderAfter
  have nextHolderTag : afterTree.indexOfTag ready.tag = some ready.source := by
    rw [← sameTag, ← sameHolder]
    exact holderIndexed
  have transferRights : OwnedOn (fun row => LocationRights afterTree row next.global.protectedTags ready.source)
      offset (offset+len) afterTree.locations := by rw [protections, ← sameHolder]; exact holds
  have transferExtent : MaterializedWithin afterTree ready.source offset (offset+len) := by
    rw [← sameHolder]
    exact retainedScope
  have unheldNext : ∀ i data, afterTree.nodeAt i = some data → Ancestor afterTree i child →
      ¬ Ancestor afterTree i ready.source → next.global.protectedTags.contains data.tag = false := by
    rw [protections, ← sameHolder]
    exact ordered.2.2
  obtain ⟨result, final, suffix, ⟨post⟩⟩ := preparesFromLenCallOfSlice options limits remaining fuel sizeFuel span fuelEq sizing debugOff
    preciseOff implicitOff frames caller machine secondMachine id first child root base offset len afterEntry
    next trackedNext secondRoom cachedAfter heap allocationMut (raceAfter.trans raceOff)
    ((congrArg (·.dataRace) extraC).trans noClocks) positiveLen bounded memoryBounds notNull cmp
    (by rw [arraysAfter]; exact metadata) (by rw [arraysAfter]; exact noAlias) ghostAfter shallowAfter
    good newNode newFound afterRoots selected rankGraph (tight child newNode newFound)
    freshKey freshNodes
    (fun empty => by
      change afterTree.tagMapping.deassigned.back? = none at empty
      change afterTree.tagMapping.mapping.size ≤ 4294967295
      have noPool := Array.back?_eq_none_iff.mp empty
      have aligned : afterTree.tagMapping.mapping.size = afterTree.nodes.size := by
        simpa [noPool] using nextKeys.balanced
      rw [aligned]
      omega)
    (fun empty => by
      change afterTree.tagMapping.deassigned.back? = none at empty
      change afterTree.tagMapping.mapping.size = afterTree.nodes.size
      have noPool := Array.back?_eq_none_iff.mp empty
      simpa [noPool] using nextKeys.balanced)
    (fun i saved => nextKeys.free i (Array.mem_of_back? saved)) vacant nextBounds readOwners
    valid11 .uninit (congrArg (·.value) destSlot) (congrArg (·.layout) destSlot) ready.thread index current threadActive
    top present (bodyC.trans body) (identityC.trans identity) (instanceC.trans callee) locC source valid12
    (congrArg (·.layout) lenSource) nextBackend dispatch dispatchFuel after rfl uncheckedAfter gcAfter fixedAfter
    ready sameId sameRoot modeNext n prepared rfl
    cacheValid cachedRoot nextKeys sharedRoom noHeld holder nextHolder nextHolderTag holderShallow
    (by rw [← sameHolder]; exact ordered.1) (by rw [← sameHolder]; exact ordered.2.1) unheldNext
    transferExtent transferRights supplied
  have stableFirst : LenExitFacts.Stable machine after := by
    rw [afterShape]
    unfold tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  let branch : LengthBranchOfSlice cfg machine machine ready entry post.graphBeforeRelease
      offset (offset+len) len n result final := {
    guard := post.branch.guard
    ready := post.branch.ready
    id := post.branch.id
    source := post.branch.source
    tag := post.branch.tag
    origin := post.branch.origin
    allocationData := post.branch.allocationData
    graph := post.branch.graph
    rangeCapacity := post.branch.rangeCapacity.trans capacityEq
    coherence := post.branch.coherence
    writable := post.branch.writable
    materialized := post.branch.materialized
    vacant := post.branch.vacant
    stable := stableFirst.trans post.branch.stable
    unrelated := fun key different => (post.branch.unrelated key different).trans
      (firstUnaffected key (by simpa only [sameId] using different))
    defaultMode := post.branch.defaultMode
    gc := post.branch.gc
    unchecked := post.branch.unchecked }
  have uncached7 : (result.locals[7]'(by rw [branch.guard.size]; decide)).layout = none := by
    have fromSource := (post.locals 7 (by decide)).trans slot7
    rw [Array.getElem?_eq_getElem (show 7 < result.locals.size by rw [branch.guard.size]; decide)] at fromSource
    exact congrArg (·.layout) (Option.some.inj fromSource)
  have kept (index : Nat) (which : index < 3 ∨ 13 ≤ index) : result.locals[index]? = frame.locals[index]? :=
    (post.locals index (by omega)).trans (originalSlots index which)
  have countNodes : branch.ready.entry.allocation.extra.nodes.size ≤ entry.allocation.extra.nodes.size + 2 := by
    have shows := post.nodeCount
    change branch.ready.entry.allocation.extra.nodes.size ≤ afterTree.nodes.size + 1 at shows
    have growth := nextCapacity.2
    change afterTree.nodes.size ≤ entry.allocation.extra.nodes.size + 1 at growth
    omega
  have counter : branch.ready.tracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat + 2 := by
    change post.branch.ready.tracker.global.nextPointerTag.value.toNat = _
    rw [post.nextTag, UInt64.toNat_add]
    have fits : next.global.nextPointerTag.value.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
      rw [secondValue]
      change tracker.global.nextPointerTag.value.toNat + 1 + 1 < 2 ^ 64
      omega
    rw [Nat.mod_eq_of_lt fits, secondValue]
    rfl
  have younger (index : UniIndex) (data : TreeNode)
      (found : branch.ready.entry.allocation.extra.nodeAt index = some data) :
      data.tag.value.toNat < branch.ready.tracker.global.nextPointerTag.value.toNat := by
    rw [counter]
    rcases post.nodeOrigin index data found with fromLen | ⟨prior, priorSaved, sourceTag⟩
    · rw [fromLen, secondValue]
      omega
    · rw [← sourceTag]
      have priorAt : afterTree.nodeAt index = some prior := priorSaved
      by_cases atShared : index = child
      · subst index
        have same := Option.some.inj (priorAt.symm.trans newFound)
        rw [same, newTagEq]
        omega
      · obtain ⟨original, originalLookup, sameTag, _⟩ := framed.olderNodes index prior atShared priorAt
        rw [← sameTag]
        have age := nodeAge index original originalLookup
        omega
  refine ⟨result, final, SuccessfulTrace.append leading suffix, ⟨?_⟩⟩
  exact {
    beforeRelease := post.graphBeforeRelease
    branch := branch
    frameExtra := post.extra.trans extraC
    place := post.place.trans placeC
    continuation := post.continuation.trans contC
    varargs := post.varargs.trans vaC
    localsIdentity := post.localsIdentity.trans localsIdC
    trackCallerArg := post.track.trans trackC
    bystanders := kept
    uncached7 := uncached7
    rootCache := fun rank => post.rootCache ((congrArg (·.userRelevance) extraC).trans rank)
    nodes := countNodes
    nextTag := counter
    protectors := post.protectedTags.trans protections
    keys := post.keys
    tagAge := younger }

#print axioms reachesRootLengthGuardOfSlice
end DuplicatePrefix.RootZeroShallowReturn

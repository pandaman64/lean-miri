import LengthBranchPrepared
import duplicate_prefix.SharedKeyResources
import ProtectedTagFresh
import duplicate_prefix.LenFrameGrant
import duplicate_prefix.LenEntryControl
import duplicate_prefix.LenRuntimeProfile
import duplicate_prefix.SharedHolderRead

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ArchiveForestProjection SourceDomain GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild
open PtrMetadataExecution PtrMetadataHelper PtrMetadataComplete Miri.Verification
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The observations shared by both branches following the actual Len call. -/
structure LengthCallResult (config : CanonicalConfigFacts.RootConfig)
    (older : Array CompilerFrameContext.ActualFrame) (outside anchor caller result : CompilerFrameContext.ActualFrame)
    (initial beforeMachine final : LenExitFacts.MachineState) (root : ActiveCaller older outside anchor initial)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (offset len count : UInt64) (old : MachineHooks.BorrowState) where
  graphBeforeRelease : BorrowTree
  branch : LengthBranchState config older outside anchor initial beforeMachine root entry graphBeforeRelease offset (offset+len) len count result final
  body : result.body = caller.body
  identity : result.bodyIdentity = caller.bodyIdentity
  instanceEq : result.functionInstance = caller.functionInstance
  extra : result.extra = caller.extra
  place : result.returnPlace = caller.returnPlace
  continuation : result.returnContinuation = caller.returnContinuation
  varargs : result.vaList = caller.vaList
  localsIdentity : result.localsIdentity = caller.localsIdentity
  track : result.trackCallerArg = caller.trackCallerArg
  locals : ∀ i, i ≠ 11 → result.locals[i]? = caller.locals[i]?
  nodeCount : branch.ready.entry.allocation.extra.nodes.size ≤ entry.allocation.extra.nodes.size + 1
  nextTag : branch.ready.tracker.global.nextPointerTag.value = old.global.nextPointerTag.value + 1
  protectedTags : branch.ready.tracker.global.protectedTags = old.global.protectedTags
  keys : RetagInsertionCapacity.Ready branch.ready.entry.allocation.extra
  nodeOrigin : ∀ index data, branch.ready.entry.allocation.extra.nodeAt index = some data →
    data.tag = old.global.nextPointerTag ∨
      ∃ prior, entry.allocation.extra.nodeAt index = some prior ∧ prior.tag = data.tag
  rootCache : caller.extra.userRelevance = 255 →
    ∃ thread, final.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some (older.push outside).size

/-- Execute the actual Len call and resume the root at its compiler-emitted guard. -/
theorem preparesFromLenCall
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1) (sizing : options.place.dynamicFuel = sizeFuel+1)
    (debug : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (older : Array CompilerFrameContext.ActualFrame) (outside caller anchor : CompilerFrameContext.ActualFrame)
    (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (old : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some old)
    (fresh : old.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none) (localClocks : caller.extra.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) caller machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) caller machine)).entries.any
      (·.value.ty == 2) = false)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag old.global.nextPointerTag = none)
    (freshNode : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ old.global.nextPointerTag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row old.global.protectedTags parent .Read)
      offset (offset+len) entry.allocation.extra.locations)
    (validDest : 11 < caller.locals.size) (oldDest : Immediate Provenance)
    (destLive : caller.locals[11].value = .live (.immediate oldDest))
    (destUncached : caller.locals[11].layout = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent (older.push outside) (LenUncachedFrontend.cachedCaller caller validDest) machine)
      (LocalPlaces.localRuntimePlace (older.push outside).size (LenUncachedFrontend.cachedCaller caller validDest) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent (older.push outside) (LenUncachedFrontend.cachedCaller caller validDest) machine)
      (LocalPlaces.localRuntimePlace (older.push outside).size (LenUncachedFrontend.cachedCaller caller validDest) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (validSource : 12 < caller.locals.size)
    (sourceCached : caller.locals[12].layout = some LenHelper.rawLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (rootReady : ActiveCaller older outside anchor initial)
    (sameId : id = rootReady.id) (sameRoot : root = rootReady.root)
    (rootMode : old.retagMode = .Default)
    (count : UInt64)
    (before : BeforeLengthReturn (LenUncachedFrontend.cachedCaller caller validDest) count)
    (destValue : oldDest = .uninit)
    (outerCont : caller.returnContinuation = anchor.returnContinuation)
    (outerPlace : caller.returnPlace = anchor.returnPlace)
    (outerArgs : caller.vaList = anchor.vaList)
    (outerLedger : caller.extra.borrowTracker = anchor.extra.borrowTracker)
    (cacheValid : ∀ i, thread.topUserRelevantFrame = some i → i < (older.push outside).size + 1)
    (cachedRoot : thread.topUserRelevantFrame = some (older.push outside).size)
    (keys : RetagInsertionCapacity.Ready entry.allocation.extra)
    (space : entry.allocation.extra.nodes.size+1 < 2^32)
    (freshUnheld : old.global.protectedTags.contains old.global.nextPointerTag = false)
    (holder : TreeNode) (holderFound : entry.allocation.extra.nodeAt rootReady.source = some holder)
    (holderIndex : entry.allocation.extra.indexOfTag rootReady.tag = some rootReady.source)
    (holderUnexposed : holder.isExposed = false)
    (ancestor : Ancestor entry.allocation.extra rootReady.source parent)
    (distinct : rootReady.source ≠ parent)
    (unheld : ∀ i data, entry.allocation.extra.nodeAt i = some data →
      Ancestor entry.allocation.extra i parent → ¬ Ancestor entry.allocation.extra i rootReady.source →
      old.global.protectedTags.contains data.tag = false)
    (scope : MaterializedWithin entry.allocation.extra rootReady.source offset (offset+len))
    (holderRights : OwnedOn (fun row => LocationRights entry.allocation.extra row old.global.protectedTags rootReady.source)
      offset (offset+len) entry.allocation.extra.locations) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    let value := (RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len LenHelper.rawLayout).imm
    caller.locals[12].value = .live (.immediate value) →
    ∃ result finalMachine, SuccessfulTrace.Trace cfg limits
      (Storage.withCurrent (older.push outside) caller beforeMachine)
      (Storage.withCurrent (older.push outside) result finalMachine) ∧
      Nonempty (LengthCallResult cfg older outside anchor caller result initial beforeMachine finalMachine
        rootReady entry offset len count old) := by
  intro cfg inner value supplied
  let frames := older.push outside
  let cf := LenUncachedFrontend.cachedCaller caller validDest
  let place := (LocalPlaces.localRuntimePlace frames.size cf 11 RootCompilerFacts.usizeLayout).stackView
  let callState := Storage.withCurrent frames cf machine
  have call := RootLenCurrentCall.stepWithFrame options limits remaining fuel sizeFuel span budget sizing debug preciseOff implicitOff
      frames caller machine id parentTag parent root base offset len entry old tracked fresh cached live allocationMut raceOff
      localClocks positive bounded memoryBounds notNull cmp metadata noAlias ghost shallow coherent parentNode parentStored
      roots parentFound depth rank tagFresh freshNode room aligned reuse clean bounds owners validDest oldDest destLive
      destUncached thread index current active top present sourceBody identity callee located source validSource
      sourceCached backend dispatch dispatchFuel beforeMachine machineEq unchecked noGc fixed supplied
  rcases call with ⟨frame, entered, step, bodyF, identityF, instanceF, locationF, slot1, slot0, slot2, sizeF,
    ledgerF, returnF, continuationF, clocksF, varargsF, tracker, actualTracker, mode, tags, reader, footprint, machineF⟩
  let currentTag := old.global.nextPointerTag
  let ledger := ({} : FrameState).addProtector id currentTag
  let offsetSize := Size.ofBytes offset
  let lengthSize := Size.ofBytes len
  let read := entry.allocation.extra.performNormalAccessRange parentTag offsetSize lengthSize .Read
    tracker.global.protectedTags .VisitChildrenOfAccessed
  let inside := DedupRangeMap.new lengthSize sharedState
  let afterTree := (read.tree.newChild offsetSize (.concrete parentTag) currentTag inside .Frozen true).tree
  let finalAllocation := {entry with allocation := entry.allocation.setExtra afterTree}
  obtain ⟨child, afterLive, coherentAfter, rootsAfter, heapSize, childIndex, ⟨childNode, childFound, childTag, _⟩, attached, afterReader⟩ :=
    CurrentLenFnEntry.releaseCertificates entered entry id parentTag currentTag parent root offset len
      tracker.global.protectedTags reader footprint
  have afterRestore : tracker.global.protectedTags.remove currentTag = old.global.protectedTags := by
    rw [tags]
    exact ProtectedTags.remove_insert_of_absent old.global.protectedTags currentTag .StrongProtector freshUnheld
  have readable : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row tracker.global.protectedTags parent .Read)
      offset (offset+len) entry.allocation.extra.locations := by
    intro i valid overlap starts ends
    unfold LocationAccessRights
    intro query node presentNode
    have keeps : tracker.global.protectedTags.contains node.tag = old.global.protectedTags.contains node.tag := by
      rw [tags]
      exact MutableReferenceRights.contains_insert_other old.global.protectedTags currentTag node.tag .StrongProtector
        (freshNode query node presentNode)
    rw [keeps]
    exact owners i valid overlap starts ends query node presentNode
  have vacant : OwnedOn (fun row => ∀ i, entry.allocation.extra.nodeAt i = none → row.perms.get i = none)
      offset (offset+len) entry.allocation.extra.locations := by
    intro pos valid _ _ _ i absent
    exact clean i absent pos valid
  have readRights : OwnedOn (fun row => LocationRights entry.allocation.extra row (tracker.global.protectedTags.remove currentTag)
      rootReady.source) offset (offset+len) entry.allocation.extra.locations := by
    rw [afterRestore]
    exact holderRights
  obtain ⟨_, _, _, _, rights, materializedRead⟩ :=
    SharedRelease.ranged_read_retains_holder_or_fresh entry.allocation.extra tracker.global.protectedTags parentTag currentTag
      parent rootReady.source root parentNode holder parentStored holderFound parentFound ancestor (.inl distinct)
      (by rw [afterRestore]; exact unheld)
      (fun i node presentNode same => (freshNode i node presentNode same).elim)
      coherent roots offsetSize lengthSize bounds readable readRights vacant
  have readHolder : read.tree.nodeAt rootReady.source = some holder := by rw [attached.readMetadata]; exact holderFound
  have holderNotChild : rootReady.source ≠ child := by
    intro equal
    have impossible : read.tree.nodeAt rootReady.source = none := equal ▸ attached.attached.fresh
    rw [readHolder] at impossible
    contradiction
  obtain ⟨actualHolder, actualHolderFound, _⟩ := attached.attached.oldEdges rootReady.source holder readHolder
  have actualHolderUnexposed : actualHolder.isExposed = false := by
    have same := attached.olderExposure rootReady.source holderNotChild
    rw [actualHolderFound, holderFound] at same
    exact (Option.some.inj same).trans holderUnexposed
  have tagsDistinct : rootReady.tag ≠ currentTag := by
    intro equal
    rw [equal, tagFresh] at holderIndex
    contradiction
  have actualHolderIndex := (attached.olderTags rootReady.tag tagsDistinct).trans holderIndex
  have materialized : MaterializedWithin afterTree rootReady.source offset (offset+len) :=
    attached.holderMaterialization rootReady.source holderNotChild _ _ (materializedRead _ scope)
  have extent : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ lengthSize.bytes.toNat := by
    intro segment member
    by_cases zero : lengthSize.bytes = 0
    · simp [inside, DedupRangeMap.new, DedupRangeMap.iterAll, zero] at member
    · simp [inside, DedupRangeMap.new, DedupRangeMap.iterAll, beq_iff_eq, zero] at member
      subst segment
      exact Nat.le_refl _
  obtain ⟨enteredRace, enteredAddress, enteredGhost, enteredShallow, enteredPayload, enteredFixed⟩ :=
    LenEntryControl.preserved options.userRelevantCrates callState place current entered machineF
  have host : entered.user.payload.payload.user.host = machine.user.payload.payload.user.host :=
    congrArg (·.host) enteredPayload
  have control := LenRuntimeProfile.control_of_host options (remaining+1) span machine entered host
  have userFlags := RootZeroCompleteState.tick_flags options remaining span beforeMachine
  have beforeUnchecked : (cfg.terminators.getControl machine.user).checkedArithmetic = false := by
    rw [machineEq]
    exact userFlags.1.trans unchecked
  have beforeNoGc : (cfg.terminators.getControl machine.user).gcInterval = 0 := by
    rw [machineEq]
    exact userFlags.2.trans noGc
  have fixedEnter : entered.threads.fixedScheduling = true := by
    rw [enteredFixed]
    change machine.threads.fixedScheduling = true
    rw [machineEq]
    exact fixed
  let receiveThread := PushThread.after thread callState.stack.frames.size
    (LenFrame.rawFrame options.userRelevantCrates (LenPush.fresh callState.machine).1 place
      (LenPush.fresh callState.machine).2).extra.userRelevance current.extra.userRelevance
  have receiveActive : entered.threads.activeThread? = some receiveThread :=
    LenEntryControl.active options.userRelevantCrates callState place current entered machineF thread active
  have receiveBound : ∀ i, receiveThread.topUserRelevantFrame = some i → i < (frames.push cf).size+1 :=
    LenEntryControl.cacheInBounds thread callState.stack.frames.size _ _ (by
      intro i saved
      have strictly := cacheValid i saved
      simp only [callState, Storage.withCurrent, frames, Array.size_push] at strictly ⊢
      omega)
  have metadataEnter : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push cf) frame entered)).metadata =
      PreparedReflection.actual.runtime := by
    change entered.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime
    rw [enteredPayload]
    exact metadata
  have aliasEnter : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push cf) frame entered)).entries.any
      (·.value.ty == 2) = false := by
    change (entered.user.payload.payload.user.types.entries.any (·.value.ty == 2)) = false
    rw [enteredPayload]
    exact noAlias
  let carrier : Pointer Provenance ⊕ UInt64 := .inl (Pointer.new (.concrete id currentTag) (Size.ofBytes (base+offset)))
  have carrierValid : SliceCarrier.Valid entered carrier len := by
    refine .positive id currentTag base offset len finalAllocation ?_ afterLive positive notNull ?_ memoryBounds
    · rw [enteredAddress]; exact cached
    · exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp bounded) (by decide)
  have fullSlot (i : Nat) (valid : i < frame.locals.size) {slot : LocalState Provenance LocalLayout}
      (found : frame.locals[i]? = some slot) : frame.locals[i] = slot :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans found)
  have l0 := fullSlot 0 (by omega) slot0
  have l1 := fullSlot 1 (by omega) slot1
  have l2 := fullSlot 2 (by omega) slot2
  have cfLive : (cf.locals[11]'(by rw [before.size]; decide)).value = .live (.immediate .uninit) := by
    simp [cf, LenUncachedFrontend.cachedCaller, LocalPlaces.cachePlaceLayout, destLive, destValue]
  have holderAfterId : entered.memory.live[rootReady.id]? = some finalAllocation := by
    rw [← sameId]
    exact afterLive
  have afterRoots : afterTree.roots = #[rootReady.root] := rootsAfter.trans (congrArg Array.singleton sameRoot)
  have listed : ledger.protectedTags = #[(rootReady.id, currentTag)] := by
    change #[(id, currentTag)] = _
    rw [sameId]
  have exactReturn : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size cf 11 RootCompilerFacts.usizeLayout := by
    rw [returnF]
    rfl
  obtain ⟨final, suffix, ⟨post⟩, topAfter, finalTracker⟩ :=
    preparesFromEnteredLength options limits remaining dispatch dispatchFuel span debug fuel budget older outside cf frame
      anchor initial entered carrier len carrierValid sizeF (congrArg (·.value) l0) (congrArg (·.layout) l0)
      (congrArg (·.value) l1) (congrArg (·.layout) l1) (congrArg (·.value) l2) (congrArg (·.layout) l2)
      bodyF identityF instanceF locationF clocksF tracker actualTracker (mode.trans rootMode)
      (enteredRace.trans raceOff) (by rw [enteredPayload]; exact backend)
      (enteredGhost.trans ghost) (enteredShallow.trans shallow) sizeFuel sizing source cmp metadataEnter aliasEnter
      (by rw [control]; exact beforeUnchecked) (by rw [control]; exact beforeNoGc) fixedEnter
      receiveThread receiveActive receiveBound ledger ledgerF count rootReady before outerCont outerPlace outerArgs
      outerLedger cfLive exactReturn continuationF varargsF finalAllocation holderAfterId entry.allocation.extra read.tree parent child
      currentTag offsetSize lengthSize inside attached listed coherentAfter afterRoots childIndex childNode childFound
      childTag ⟨holder, holderFound⟩ ancestor (by rw [afterRestore]; exact unheld) freshNode extent afterReader rights materialized
      actualHolderIndex actualHolder actualHolderFound actualHolderUnexposed
  let result := {writeFrame cf 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
    (by rw [before.size]; decide) with location := FrameLocation.mir ⟨3, 0⟩}
  have preCallStable : LenExitFacts.Stable beforeMachine machine := by
    rw [machineEq]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have entryStable : LenExitFacts.Stable machine entered :=
    ⟨enteredRace, enteredAddress, congrArg (·.types) enteredPayload,
      congrArg (·.backend) enteredPayload, congrArg (·.runtime.extras) enteredPayload⟩
  let branch : LengthBranchState cfg older outside anchor initial beforeMachine rootReady entry afterTree
      offset (offset+len) len count result final := {
    guard := post.guard
    ready := post.ready
    id := post.id
    source := post.source
    tag := post.tag
    origin := post.origin
    allocationData := post.allocationData
    graph := post.graph
    rangeCapacity := post.rangeCapacity.trans heapSize
    coherence := post.coherence
    writable := post.writable
    materialized := post.materialized
    vacant := post.vacant
    stable := preCallStable.trans (entryStable.trans post.stable)
    defaultMode := post.defaultMode
    gc := post.gc
    unchecked := post.unchecked }
  have rooted : caller.extra.userRelevance = 255 →
      ∃ currentThread, final.threads.activeThread? = some currentThread ∧
        currentThread.topUserRelevantFrame = some (older.push outside).size := by
    intro rank
    apply topAfter rank
    unfold receiveThread PushThread.after
    by_cases selects : current.extra.userRelevance ≤
        (LenFrame.rawFrame options.userRelevantCrates (LenPush.fresh callState.machine).1 place
          (LenPush.fresh callState.machine).2).extra.userRelevance
    · rw [ite_eq_left selects]
      exact Or.inr rfl
    · rw [ite_eq_right selects]
      exact Or.inl cachedRoot
  have nodesAfter : branch.ready.entry.allocation.extra.nodes = afterTree.nodes := by
    have same := congrArg BorrowTree.nodes post.graph
    exact same
  have sameTracker : branch.ready.tracker = {tracker with global := tracker.global.endCall ledger} :=
    Option.some.inj (post.ready.tracked.symm.trans finalTracker)
  have nextTag := CurrentLenFnEntry.consumedTag entered entry id parentTag currentTag parent offset len
    tracker.global.protectedTags tracker actualTracker footprint
  have storedNext : branch.ready.tracker.global.nextPointerTag.value = old.global.nextPointerTag.value + 1 := by
    rw [sameTracker]
    exact nextTag
  have storedProtectors : branch.ready.tracker.global.protectedTags = old.global.protectedTags := by
    rw [sameTracker]
    change (tracker.global.endCall ledger).protectedTags = _
    unfold TreeBorrows.GlobalState.endCall
    exact afterRestore
  have other (i : Nat) (different : i ≠ 11) : result.locals[i]? = caller.locals[i]? := by
    simp [result, writeFrame, cf, LenUncachedFrontend.cachedCaller, LocalPlaces.cachePlaceLayout, Ne.symm different]
  refine ⟨result, final, .next step suffix, ⟨afterTree, branch, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    other, ?_, storedNext, storedProtectors, ?_, ?_, rooted⟩⟩
  · rw [nodesAfter]
    exact (attached.readyAfterInsertion keys space tagFresh ⟨childNode, childFound, childTag⟩ (attached.extent extent).2).2
  · have next := attached.readyAfterInsertion keys space tagFresh ⟨childNode, childFound, childTag⟩ (attached.extent extent).2
    exact ready_following_release afterTree branch.ready.entry.allocation.extra post.graph next.1 post.vacant
  · intro index data actual
    have seen : afterTree.nodeAt index = some data := by
      unfold BorrowTree.nodeAt at actual ⊢
      rwa [nodesAfter] at actual
    by_cases matchChild : index = child
    · subst index
      have same := Option.some.inj (seen.symm.trans childFound)
      exact Or.inl ((congrArg TreeNode.tag same).trans childTag)
    · obtain ⟨previous, found, tag, _⟩ := attached.olderNodes index data matchChild seen
      exact Or.inr ⟨previous, found, tag⟩

#print axioms preparesFromLenCall
end DuplicatePrefix.RootZeroShallowReturn

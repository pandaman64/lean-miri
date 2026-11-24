import RootPhysicalAcceptedFromLength
import RootPhysicalRejectedFromLength
import VerifyZeroPhysicalCanonical

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open SourceDomain PreparedArguments ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild CanonicalCallDomain

set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

/-- Safety of the saved MIR through a disjoint physical Boolean output. -/
theorem allCountPhysical
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64)
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
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame machine)).entries.any
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
    (cacheValid : ∀ index, ready.thread.topUserRelevantFrame = some index → index < 1)
    (tagHeadroom : tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615)
    (pool : entry.allocation.extra.tagMapping.deassigned = #[])
    (keyShape : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (nodeRoom : entry.allocation.extra.nodes.size + 1 ≤ 4294967295)
    (keyAge : ∀ old i, entry.allocation.extra.indexOfTag old = some i → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (nodeAge : ∀ i data, entry.allocation.extra.nodeAt i = some data → data.tag.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectedAge : ∀ old, tracker.global.protectedTags.contains old = true → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (cachedRoot : ready.thread.topUserRelevantFrame = some 0)
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (storage : InitializedRegion (Storage.withCurrent #[] frame machine) len)
    (storageId : storage.id = id) (storageEntry : storage.entry = entry)
    (storageOffset : storage.relativeStart.bytes = offset)
    (initialKeys : RetagInsertionCapacity.Ready entry.allocation.extra)
    (keyBudget : entry.allocation.extra.nodes.size + 3 < 2^32)
    (tagBudget : tracker.global.nextPointerTag.value.toNat + 4 < 2^64)
    (statementFuel : limits.validation = fuel+1)
    (relevance : frame.extra.userRelevance = 255) (track : frame.trackCallerArg = none)
    (deadTail : ∀ i, 15 ≤ i → i ≤ 24 → frame.locals[i]? = some ⟨.dead,none⟩)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (maskLen : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (storageFits : entry.allocation.len+64 < 18446744073709551616)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) id)}))
    (pointer : Pointer (Option Provenance))
    (concrete : pointer.provenance = some (.concrete id parentTag))
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer len)
    (continues : frame.returnContinuation = .stop true)
    (admitted : Admitted program options remaining preparedTagHeadroom span
      (Storage.withCurrent #[] frame machine) frame pointer len n)
    (compiler : InitialCompilerControl (Storage.withCurrent #[] frame machine) frame) :
    GeneratedBodySafety.requiredForEveryChoiceAt (PreparedContracts.actualConfig options () (remaining+1) span)
      limits (Storage.withCurrent #[] frame machine) := by
  by_cases zero : n = 0
  · subst n
    exact CanonicalCallDomain.zeroCountPhysical program loaded options limits remaining span fuel fuelEq _ frame pointer len
      admitted compiler destination (by rfl) continues
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨result, final, beforeRun, ⟨post⟩⟩ :=
      reachesRootLengthGuardOfSlice options limits remaining sizeFuel span source debugOff fuel fuelEq #[] frame machine
        body identity callee location size n zero unused dead3 uncached3 dead4 dead5 uncached4 uncached5 live2 cached2
        noClocks all tracker tracked defaultMode ghost shallow unchecked noGc fixed sizing preciseOff implicitOff
        id parentTag parent root base offset len entry fresh cached live allocationMut raceOff positiveLen bounded memoryBounds
        notNull cmp metadata noAlias coherent parentNode parentStored roots parentFound depth rank tagFresh nodeFresh
        unheld room aligned reuse clean bounds owners extent sourceSlot ready sameId sameRoot sameHolder sameTag heldUnexposed
        resultSlot tempSlot backend dispatch dispatchFuel cacheValid tagHeadroom pool keyShape nodeRoom keyAge nodeAge protectedAge cachedRoot
  have pointerInStorage : pointer.provenance = some (.concrete storage.id ready.tag) := by
    rw [storageId,← sameTag]
    exact concrete
  have run : ∃ done, SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] result final) done ∧ done.stack.frames = #[] := by
    by_cases rejected : n > len/2
    · obtain ⟨done, trace, empty, _⟩ := post.rejectedPhysicalTrace options limits remaining fuel span fuelEq
        debugOff source rejected positiveLen pointer (by rw [← sameId,← sameTag]; exact concrete)
        tracker tracked rfl destination preparedTagHeadroom admitted.allocations raceOff backend continues admitted.stack.noVarargs
      exact ⟨done,trace,empty⟩
    · have positive : 0 < n.toNat := by
        have nonzero : n.toNat ≠ 0 := by
          intro empty
          apply zero
          exact UInt64.toNat.inj (by simp [empty])
        omega
      have slot2 : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ := by
        rw [Array.getElem?_eq_getElem (show 2 < frame.locals.size by omega)]
        congr 1
        cases current : frame.locals[2]
        rw [current] at live2 cached2
        simp_all
      have tagRoom : post.branch.ready.tracker.global.nextPointerTag.value ≠ 18446744073709551615 := by
        intro equal
        have next := post.nextTag
        rw [equal] at next
        simp at next
        omega
      obtain ⟨done,trace,empty,_⟩ := post.acceptedPhysicalTrace options limits remaining fuel sizeFuel span fuelEq sizing
        debugOff preciseOff implicitOff rejected positive positiveLen bounded storage (storageId.trans sameId) storageEntry
        storageOffset bounds initialKeys (by omega) tagRoom base (by rw [storageId]; exact cached) notNull metadata noAlias
        source dispatch dispatchFuel raceOff backend cmp statementFuel relevance track resultSlot
        (by rw [storageId,← sameTag]; exact sourceSlot) slot2 deadTail outerRank innerRank maskLen maskValid provenance
        storageFits (by rw [storageId]; exact extras) keyBudget tagBudget protectedAge tracked pointer pointerInStorage
        destination preparedTagHeadroom admitted.allocations admitted.stack.noVarargs continues
      exact ⟨done,trace,empty⟩
  obtain ⟨done,tail,empty⟩ := run
  exact GeneratedSafetyOfTrace.required program loaded cfg limits _ done admitted.entered (SuccessfulTrace.append beforeRun tail)
    (by simp [empty,Storage.withCurrent])

#print axioms allCountPhysical
end DuplicatePrefix.RootZeroShallowReturn

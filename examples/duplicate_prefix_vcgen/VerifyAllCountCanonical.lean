import VerifyAllCountGenerated
import CanonicalEntryFacts

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ArchiveForestProjection SourceDomain PreparedArguments GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild CanonicalCallDomain

set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

/-- The saved safety VC for every count on a nonempty initialized slice,
with a canonical nested cached Boolean destination and available retag resources. -/
theorem allCountsFromCanonicalAdmitted
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (outside frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (sizing : options.place.dynamicFuel = sizeFuel+1)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (positiveLen : 0 < len)
    (notNull : base + offset ≠ 0)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (extent : MaterializedWithin entry.allocation.extra parent offset (offset+len))
    (sourceSlot : frame.locals[1]? = some ⟨.live (.immediate (.scalarPair
      (.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len)))), some RootCompilerFacts.sliceLayout⟩)
    (ready : ActiveCaller older outside frame machine)
    (sameId : id = ready.id) (sameRoot : root = ready.root) (sameHolder : parent = ready.source)
    (sameTag : parentTag = ready.tag)
    (heldUnexposed : parentNode.isExposed = false)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (pool : entry.allocation.extra.tagMapping.deassigned = #[])
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (pointer : Pointer (Option Provenance))
    (admitted : Admitted program options remaining preparedTagHeadroom span
      (Storage.withCurrent (older.push outside) frame machine) frame pointer len n)
    (compiler : InitialCompilerControl (Storage.withCurrent (older.push outside) frame machine) frame)
    (storage : InitializedRegion (Storage.withCurrent (older.push outside) frame machine) len)
    (storageId : storage.id = id) (storageEntry : storage.entry = entry)
    (storageOffset : storage.relativeStart.bytes = offset)
    (initialKeys : RetagInsertionCapacity.Ready entry.allocation.extra)
    (keyBudget : entry.allocation.extra.nodes.size + 3 < 2^32)
    (statementFuel : limits.validation = fuel+1)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (maskLen : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (storageFits : entry.allocation.len+64 < 18446744073709551616)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) id)})) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent (older.push outside) frame machine) := by
  let profile := admitted.profile
  obtain ⟨selected, sameTracker, defaultMode⟩ := profile.mode
  have trackerEq : selected = tracker := Option.some.inj (sameTracker.symm.trans tracked)
  subst selected
  obtain ⟨thread, running, cache⟩ := admitted.stack.active
  have threadEq : thread = ready.thread := Option.some.inj (running.symm.trans ready.active)
  subst thread
  have cacheValid : ∀ index, ready.thread.topUserRelevantFrame = some index → index < (older.push outside).size + 1 := by
    intro index saved
    simpa only [Storage.withCurrent, Array.size_push] using cache index saved
  obtain ⟨bodyIdentity, body, location, size⟩ := admitted.emittedFrame loaded
  have callee := admitted.identity.trans (loadedRootInstance_eq loaded)
  have temporary (index : Nat) (low : 3 ≤ index) (high : index < 25)
      (dead : index ≠ 6 ∧ index ≠ 13 ∧ index ≠ 14) :
      frame.locals[index]? = some ⟨.dead,none⟩ := by
    have known := admitted.initialTemporarySlot loaded compiler index low high
    simpa [Array.contains, dead.1,dead.2.1,dead.2.2,Ne.symm dead.1,Ne.symm dead.2.1,Ne.symm dead.2.2] using known
  have checked (index : Nat) (valid : index < frame.locals.size) (low : 3 ≤ index)
      (dead : index ≠ 6 ∧ index ≠ 13 ∧ index ≠ 14) :
      frame.locals[index] = ⟨.dead,none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans (temporary index low (by omega) dead))
  have checked3 := checked 3 (by omega) (by decide) (by decide)
  have checked4 := checked 4 (by omega) (by decide) (by decide)
  have checked5 := checked 5 (by omega) (by decide) (by decide)
  obtain ⟨_,_,_,countSlot⟩ := admitted.initialArgumentSlots
  have checked2 := Option.some.inj ((Array.getElem?_eq_getElem (show 2 < frame.locals.size by omega)).symm.trans countSlot)
  have temp13 := admitted.initialTemporarySlot loaded compiler 13 (by decide) (by decide)
  have temp13' : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩ := by simpa using temp13
  obtain ⟨current,active,top⟩ := compiler.currentRelevant
  have threadEq : current = ready.thread := Option.some.inj (active.symm.trans ready.active)
  have cachedRoot : ready.thread.topUserRelevantFrame = some (older.push outside).size := by
    rw [← threadEq, top]
    simp [Storage.withCurrent]
  have live : machine.memory.live[id]? = some entry := by
    have actual := storage.live
    change machine.memory.live[storage.id]? = some storage.entry at actual
    simpa only [storageId,storageEntry] using actual
  have allocationMut : entry.allocation.mutability = .Mut := by
    simpa only [storageEntry] using storage.writable
  have memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    simpa only [storageOffset,storageEntry] using storage.fits
  have bounded : len ≤ 9223372036854775807 := by
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    have width := admitted.slice.addressable
    omega
  obtain ⟨borrow,_,trackedBorrow,_,_,tagBudget,oldProtections,_,oldNodes⟩ := admitted.allocations.ledger
  have borrowEq := Option.some.inj (trackedBorrow.symm.trans tracked)
  subst borrow
  change tracker.global.nextPointerTag.value.toNat + 4 < 2^64 at tagBudget
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat < 18446744073709551615; omega)
  have tagHeadroom : tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615 := by omega
  have keyShape : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size := by
    simpa [pool] using initialKeys.balanced
  have nodeRoom : entry.allocation.extra.nodes.size + 1 ≤ 4294967295 := by omega
  have nodeAge (i : UniIndex) (data : TreeNode) (found : entry.allocation.extra.nodeAt i = some data) :
      data.tag.value.toNat < tracker.global.nextPointerTag.value.toNat :=
    UInt64.lt_iff_toNat_lt.mp (oldNodes id entry i data live found)
  have keyAge (tag : BorTag) (i : UniIndex) (found : entry.allocation.extra.indexOfTag tag = some i) :
      tag.value.toNat < tracker.global.nextPointerTag.value.toNat := by
    unfold BorrowTree.indexOfTag UniKeyMap.get at found
    cases key : entry.allocation.extra.tagMapping.mapping.find? (fun row => row.1 == tag) with
    | none => simp [key] at found
    | some row =>
      have picked := beq_iff_eq.mp (Array.find?_some (p := fun row : BorTag × UniIndex => row.1 == tag) key)
      obtain ⟨node,atKey,tagEq⟩ := initialKeys.keys row (Array.mem_of_find?_eq_some key)
      rw [← picked, ← tagEq]
      exact nodeAge _ node atKey
  have protectedAge (tag : BorTag) (held : tracker.global.protectedTags.contains tag = true) :
      tag.value.toNat < tracker.global.nextPointerTag.value.toNat := by
    unfold ProtectedTags.contains ProtectedTags.get at held
    cases key : tracker.global.protectedTags.entries.find? (fun row => row.1 == tag) with
    | none => simp [key] at held
    | some row =>
      have picked := beq_iff_eq.mp (Array.find?_some (p := fun row : BorTag × ProtectorKind => row.1 == tag) key)
      rw [← picked]
      exact UInt64.lt_iff_toNat_lt.mp (oldProtections row (Array.mem_of_find?_eq_some key))
  have cap := RetagInsertionCapacity.derive _ parent root tracker.global.nextPointerTag coherent roots parentNode parentStored
    initialKeys (fun i node found collision => by
      have older := nodeAge i node found
      rw [collision] at older
      exact Nat.lt_irrefl _ older)
  obtain ⟨depth,rank⟩ := cap.ranked
  have unheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false := by
    cases held : tracker.global.protectedTags.contains tracker.global.nextPointerTag
    · rfl
    · exact False.elim (Nat.lt_irrefl _ (protectedAge _ held))
  exact allCountSafety options limits remaining sizeFuel span compilerSourceComparator profile.debugOff fuel fuelEq
    older outside frame machine body bodyIdentity callee location size n
    (fun index valid low high => checked index valid (by omega) (by omega))
    (congrArg (·.value) checked3) (congrArg (·.layout) checked3)
    (congrArg (·.value) checked4) (congrArg (·.value) checked5)
    (congrArg (·.layout) checked4) (congrArg (·.layout) checked5)
    (congrArg (·.value) checked2) (congrArg (·.layout) checked2)
    admitted.stack.calleeClocksOff admitted.immediateLocals tracker tracked defaultMode
    profile.ghostOff profile.shallow profile.unchecked profile.noGc profile.fixed sizing
    profile.preciseInteriorMutOff profile.implicitWritesOff id parentTag parent root base offset len entry fresh cached live
    allocationMut profile.raceOff positiveLen bounded memoryBounds notNull ProjectionMetadataFacts.nullComparator profile.compilerRuntime profile.noSyntheticSliceCache
    coherent parentNode parentStored roots parentFound depth rank cap.freshKey cap.freshNode unheld cap.room cap.aligned cap.reuse cap.clean bounds
    owners extent sourceSlot ready sameId sameRoot sameHolder sameTag heldUnexposed admitted.resultSlot temp13'
    profile.backendOff dispatch dispatchFuel cacheValid tagHeadroom pool keyShape nodeRoom keyAge nodeAge protectedAge cachedRoot
    program loaded admitted.entered storage storageId storageEntry storageOffset initialKeys keyBudget
    tagBudget statementFuel compiler.highestRelevance compiler.noTrackCaller
    (fun i low high => temporary i (by omega) (by omega) (by omega)) outerRank innerRank
    maskLen maskValid provenance storageFits extras

#print axioms allCountsFromCanonicalAdmitted
end DuplicatePrefix.RootZeroShallowReturn

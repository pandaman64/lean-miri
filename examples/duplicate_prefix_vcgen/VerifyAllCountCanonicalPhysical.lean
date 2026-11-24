import VerifyPhysicalAllCount
import CanonicalEntryFacts

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ArchiveForestProjection SourceDomain PreparedArguments GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild CanonicalCallDomain

set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem concreteSliceImmediate (pointer : Pointer (Option Provenance)) (id : AllocId) (tag : BorTag)
    (base offset length : UInt64) (concrete : pointer.provenance = some (.concrete id tag))
    (address : pointer.offset.bytes = base+offset) :
    Immediate.newSlice pointer length PreparedReflection.actual.runtime.target.base =
      .ok (.scalarPair (Scalar.fromPointer PreparedReflection.actual.runtime.target.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))) (.fromScalarInt (.ofUInt64 length))) := by
  obtain ⟨stored,provenance⟩ := pointer
  change provenance = _ at concrete
  subst provenance
  have offsetShape : stored = Size.ofBytes (base+offset) := by
    cases stored
    exact congrArg Size.ofBytes address
  subst stored
  have truncated := ScalarArithmetic.truncate_word length
  unfold ScalarInt.truncateFromUInt at truncated
  unfold Immediate.newSlice Scalar.fromMaybePointer Scalar.fromUInt ScalarInt.tryFromUInt
  change (show Except ImmediateError (Immediate Provenance) from do
    let ptrScalar ← (Except.ok (Scalar.fromPointer PreparedReflection.actual.runtime.target.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))) : Except ImmediateError (Scalar Provenance))
    let lenScalar ← _
    pure (.scalarPair ptrScalar lenScalar)) = _
  erw [truncated]
  rfl

/-- The saved safety VC for every count on a nonempty initialized slice,
with a canonical physical Boolean destination and available retag resources. -/
theorem allCountsFromCanonicalPhysical
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
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
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (pool : entry.allocation.extra.tagMapping.deassigned = #[])
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (pointer : Pointer (Option Provenance))
    (concrete : pointer.provenance = some (.concrete id parentTag))
    (addressOffset : pointer.offset.bytes = base + offset)
    (admitted : Admitted program options remaining preparedTagHeadroom span
      (Storage.withCurrent #[] frame machine) frame pointer len n)
    (compiler : InitialCompilerControl (Storage.withCurrent #[] frame machine) frame)
    (storage : InitializedRegion (Storage.withCurrent #[] frame machine) len)
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
      (Storage.withCurrent #[] frame machine) := by
  let profile := admitted.profile
  obtain ⟨selected, sameTracker, defaultMode⟩ := profile.mode
  have trackerEq : selected = tracker := Option.some.inj (sameTracker.symm.trans tracked)
  subst selected
  obtain ⟨thread, running, top⟩ := compiler.currentRelevant
  have cachedRoot : thread.topUserRelevantFrame = some 0 := by simpa [Storage.withCurrent] using top
  have cacheValid : ∀ index, thread.topUserRelevantFrame = some index → index < 1 := by
    intro index saved
    have equal := Option.some.inj (saved.symm.trans cachedRoot)
    omega
  obtain ⟨returnPlace, returns⟩ :
      PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer len ∧
        frame.returnContinuation = .stop true := by
    cases admitted.destination with
    | physicalRoot _ continuation destination => exact ⟨destination,continuation⟩
    | cachedCaller destination _ =>
      obtain ⟨earlier,outside,index,target,unwind,slot,value,frames,_⟩ := destination.localSlot
      have impossible := congrArg Array.size frames
      simp only [Storage.withCurrent, Array.size_push, Array.size_empty] at impossible
      omega
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
  obtain ⟨buffer, readBuffer, sourceValue, countSlot⟩ := admitted.initialArgumentSlots
  have sameBuffer := Except.ok.inj ((concreteSliceImmediate pointer id parentTag base offset len concrete addressOffset).symm.trans readBuffer)
  rw [← sameBuffer, ← actual_access_runtime options () (remaining+1) span] at sourceValue
  have sourceSlot := sourceValue
  have checked2 := Option.some.inj ((Array.getElem?_eq_getElem (show 2 < frame.locals.size by omega)).symm.trans countSlot)
  have temp13 := admitted.initialTemporarySlot loaded compiler 13 (by decide) (by decide)
  have temp13' : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩ := by simpa using temp13
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
  have heldUnexposed : parentNode.isExposed = false := by
    obtain ⟨witness,tag,address,loan,owned,withTag,_,_,_,_,_,⟨node,present,hidden⟩,_⟩ :=
      admitted.sliceProtector (fun empty => by rw [empty] at positiveLen; exact (UInt64.lt_irrefl _ positiveLen))
    have provenance := Option.some.inj (withTag.symm.trans concrete)
    injection provenance with sameId sameTag
    have arrived : machine.memory.live[witness.id]? = some witness.entry := witness.live
    rw [sameId,live] at arrived
    have sameEntry := Option.some.inj arrived
    have source := loan.tagKnown
    subst tag
    rw [← sameEntry,parentFound] at source
    have index := Option.some.inj source
    rw [← sameEntry,← index,parentStored] at present
    have sameNode := Option.some.inj present
    exact (congrArg TreeNode.isExposed sameNode).trans hidden
  let ready : RetainedSlice machine := {
    id := id, tag := parentTag, entry := entry, present := live, tracker := tracker, tracked := tracked,
    source := parent, root := root, indexed := parentFound, roots := roots, node := parentNode,
    found := parentStored, unexposed := heldUnexposed, thread := thread, active := running }
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
  exact allCountPhysical options limits remaining sizeFuel span compilerSourceComparator profile.debugOff fuel fuelEq
    frame machine body bodyIdentity callee location size n
    (fun index valid low high => checked index valid (by omega) (by omega))
    (congrArg (·.value) checked3) (congrArg (·.layout) checked3)
    (congrArg (·.value) checked4) (congrArg (·.value) checked5)
    (congrArg (·.layout) checked4) (congrArg (·.layout) checked5)
    (congrArg (·.value) checked2) (congrArg (·.layout) checked2)
    admitted.stack.calleeClocksOff admitted.immediateLocals tracker tracked defaultMode
    profile.ghostOff profile.shallow profile.unchecked profile.noGc profile.fixed sizing
    profile.preciseInteriorMutOff profile.implicitWritesOff id parentTag parent root base offset len entry fresh cached live
    allocationMut profile.raceOff positiveLen bounded memoryBounds notNull (show ProjectionMetadataFacts.NullComparator from by decide) profile.compilerRuntime profile.noSyntheticSliceCache
    coherent parentNode parentStored roots parentFound depth rank cap.freshKey cap.freshNode unheld cap.room cap.aligned cap.reuse cap.clean bounds
    owners extent sourceSlot ready rfl rfl rfl rfl heldUnexposed admitted.resultSlot temp13'
    profile.backendOff dispatch dispatchFuel cacheValid tagHeadroom pool keyShape nodeRoom keyAge nodeAge protectedAge cachedRoot
    program loaded storage storageId storageEntry storageOffset initialKeys keyBudget
    tagBudget statementFuel compiler.highestRelevance compiler.noTrackCaller
    (fun i low high => temporary i (by omega) (by omega) (by omega)) outerRank innerRank
    maskLen maskValid provenance storageFits extras pointer concrete returnPlace returns admitted compiler

#print axioms allCountsFromCanonicalPhysical
end DuplicatePrefix.RootZeroShallowReturn

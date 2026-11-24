import duplicate_prefix.ActualRootReferenceDeref
import duplicate_prefix.RootAcceptedAsMut
import duplicate_prefix.RootPositiveToCachedCaller
import duplicate_prefix.AsMutHolderScope
import SymbolicBounds
import duplicate_prefix.RootAcceptedAfterLen
import duplicate_prefix.RootAsMutReservation

namespace DuplicatePrefix.RootPositiveFromLength
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain RootPositiveCachedReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Original-root authority transported through the specific pure copy-carrier
tree. This is a predicate on tree data only and does not assume any interpreter
step or safety outcome. -/
structure HolderImage (tree : BorrowTree) (tags : ProtectedTags) (holder source : UniIndex)
    (parentTag : BorTag) (start : Size) (length : UInt64) : Prop where
  indexed : tree.indexOfTag parentTag = some holder
  hidden : ∃ node, tree.nodeAt holder = some node ∧ node.isExposed = false
  between : AsMutHolderScope.BetweenTags tree tags holder source
  footprint : CopyHolderRights.Footprint tree tags source holder start.bytes (start.bytes + length)

theorem cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (older : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length base : UInt64) (parentTag : BorTag)
    (positive : 0 < length) (bounded : length ≤ 9223372036854775807)
    (valid : 16 < frame.locals.size)
    (count : UInt64) (accepted : ¬ count > length / 2)
    (entry : RootZeroShallowReturn.RejectionEntry frame machine length count)
    (none7 : (frame.locals[7]'(by rw [entry.size]; decide)).layout = none)
    (slot15 : frame.locals[15]? = some ⟨.dead,none⟩)
    (slot16 : frame.locals[16]? = some ⟨.dead,none⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (noRace : machine.dataRace = none)
    (storage : InitializedRegion (Storage.withCurrent (older.push caller) frame machine) length)
    (loan : ExclusiveRegion (Storage.withCurrent (older.push caller) frame machine) length storage parentTag)
    (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id, base⟩)
    (nonnull : base + storage.relativeStart.bytes ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) frame machine)).entries.any
      (·.value.ty == 2) = false)
    (source : PreparedContracts.SourceComparator)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch + 1)
    (defaultMode : loan.tracker.retagMode = .Default)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ (older.push caller).size)
    (future : ∀ (global : TreeBorrows.GlobalState) (child : UniIndex),
      let parentTree := storage.entry.allocation.extra
      let newTag := loan.tracker.global.nextPointerTag
      let nextTree := ExclusiveTwoPhaseRetag.reservationTree parentTree parentTag newTag
        storage.relativeStart (Size.ofBytes length) loan.tracker.global.protectedTags
      loan.tracker.global.newPointerTag = .ok (global,newTag) →
      nextTree.indexOfTag newTag = some child →
      global.nextPointerTag.value ≠ 18446744073709551615 ∧
        CurrentTwoPhaseStructural.InsertionCapacity nextTree child root global.nextPointerTag)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (statementFuel : limits.validation = fuel+1)
    (countPositive : 0 < count.toNat)
    (rank : frame.extra.userRelevance = 255)
    (top : thread.topUserRelevantFrame = some (older.push caller).size)
    (track : frame.trackCallerArg = none)
    (countSlot : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (deadTail : ∀ i, 17 ≤ i → i ≤ 24 → frame.locals[i]? = some ⟨.dead,none⟩)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (maskLen : storage.entry.allocation.initializationMask.len = storage.entry.allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed storage.entry.allocation.initializationMask)
    (provenance : ProvenanceCopy.WellFormed storage.entry.allocation.provenanceMap storage.entry.allocation.len)
    (storageFits : storage.entry.allocation.len+64 < 18446744073709551616)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) =
      some (storage.id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) storage.id)}))
    (zeroSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (slot : CallerSlot older caller frame)
    (owned : FrameState) (ownership : frame.extra.borrowTracker = some owned)
    (ledger : owned.protectedTags = #[(storage.id,parentTag)]) (noVarargs : frame.vaList = #[])
    (image : let reservationTag := loan.tracker.global.nextPointerTag
      let finalTag := reservationTag.succ.getD reservationTag
      let tags := loan.tracker.global.protectedTags
      let reservation := ExclusiveTwoPhaseRetag.reservationTree storage.entry.allocation.extra parentTag reservationTag
        storage.relativeStart (Size.ofBytes length) tags
      let active := ExclusiveTypedRetag.protectedFrozenTree reservation tags reservationTag finalTag
        storage.relativeStart (Size.ofBytes length)
      let released := (active.releaseProtector finalTag (tags.insert finalTag .StrongProtector)).tree
      ∀ index, released.indexOfTag finalTag = some index →
        HolderImage released ((tags.insert finalTag .StrongProtector).remove finalTag)
          loan.source index parentTag storage.relativeStart length) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let oldPointer := Pointer.new (.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))
    let oldValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base oldPointer length RootCompilerFacts.sliceLayout).imm
    let newTag := loan.tracker.global.nextPointerTag
    let newPointer := Pointer.new (.concrete storage.id newTag) oldPointer.offset
    let newValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base newPointer length RootCompilerFacts.sliceLayout).imm
    (frame.locals[1]'(by omega)).value = .live (.immediate oldValue) →

    let tag := (loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag)
    let resumed := {RootZeroShallowReturn.putBool caller slot.index slot.valid true with location := .mir ⟨slot.target,0⟩}
    ∃ popped, SuccessfulTrace.Trace cfg limits (Storage.withCurrent (older.push caller) frame machine)
      (Storage.withCurrent older resumed popped) := by
  intro cfg oldPointer oldValue newTag newPointer newValue original tag resumed
  obtain ⟨rootFrame,rawMachine,rawStorage,rawRights,run,location,body,identity,callee,extra,trackEq,placeEq,contEq,
      varargsEq,localsEq,rawId,rawOffset,physical,roots,extentAfter,mode,rawTree,rawTags,size,slot15,slot0,slot2,tail,direct,slot16,addr,noDataRace,fixed,arithmetic,
      gc,nativeBackend,extrasPreserved,_,ghost,shallow,cached⟩ :=
    RootAcceptedAsMut.completes options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
      (older.push caller) frame machine length base parentTag positive bounded valid count accepted entry none7 ‹frame.locals[15]? = _›
      ‹frame.locals[16]? = _› sourceCached noRace storage loan root capacity tagRoom extent address nonnull metadata noAlias source
      dispatch dispatchFuel defaultMode backend unchecked noGc thread active relevant future cmp original
  obtain ⟨rootThread,activeThread,rootTop⟩ := cached rank top
  have disjoint : count.toNat+count.toNat ≤ length.toNat := SymbolicBounds.usize_guard accepted
  have countFits : count.toNat < 2^63 := by
    have lengthFits : length.toNat ≤ 9223372036854775807 := UInt64.le_iff_toNat_le.mp bounded
    omega
  have targetBound : count ≤ cfg.projection.maxSizeOfVal.bytes := by
    obtain ⟨place, pointers, table, _, projection, _⟩ :=
      (CanonicalConfigFacts.actual_fields options () (remaining+1) span).placeConstruction
    have maximum := ActualRootReferenceDeref.constructor_maximum options (remaining+1) span place pointers table projection
    have projectionMaximum : cfg.projection.maxSizeOfVal = place.maxSizeOfVal := by
      dsimp only [cfg]
      rw [projection]
      rfl
    rw [projectionMaximum,maximum]
    apply UInt64.le_iff_toNat_le.mpr
    change count.toNat ≤ 9223372036854775807
    omega
  have callerRank : rootFrame.extra.userRelevance > 0 := by rw [extra,rank]; decide
  have ready16 := (Array.getElem?_eq_some_iff.mp slot16).2
  have afterPointer : rootFrame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base
      (.new (.concrete rawStorage.id tag) (Size.ofBytes (base+rawStorage.relativeStart.bytes)))))),some CopyCompilerFacts.destPointerLayout⟩ := by
    rw [rawId,rawOffset]
    exact slot15
  have maskLength : rawStorage.entry.allocation.initializationMask.len = rawStorage.entry.allocation.byteSize := by
    rw [physical]
    exact maskLen
  have maskShape : InitMaskCopy.WellFormed rawStorage.entry.allocation.initializationMask := by
    rw [physical]
    exact maskValid
  have provShape : ProvenanceCopy.WellFormed rawStorage.entry.allocation.provenanceMap rawStorage.entry.allocation.len := by
    rw [physical]
    exact provenance
  have rawFits : rawStorage.entry.allocation.len + 64 < 18446744073709551616 := by
    rw [physical]
    exact storageFits
  let newSlot : CallerSlot older caller rootFrame :=
    {slot with continuation := contEq.trans slot.continuation, place := placeEq.trans slot.place}
  have selected := rawRights.tagKnown
  rw [rawTree] at selected
  have carried : HolderImage rawStorage.entry.allocation.extra rawRights.tracker.global.protectedTags loan.source
      rawRights.source parentTag rawStorage.relativeStart length := by
    rw [rawTree,rawTags,rawOffset]
    exact image rawRights.source selected
  obtain ⟨rawNode,atRaw,_⟩ := rawRights.sourcePresent
  obtain ⟨oldNode,atHolder,unexposed⟩ := carried.hidden
  let holder : Holder rawStorage.entry.allocation.extra rawRights.tracker.global.protectedTags tag rawRights.source
      rawStorage.relativeStart length :=
    { root := root, roots := roots, sourceNode := rawNode, atSource := atRaw, atCopyTag := rawRights.tagKnown
      tag := parentTag, index := loan.source, node := oldNode, atHolder := atHolder, atHolderTag := carried.indexed
      unexposed := unexposed, coherent := rawRights.coherent, lineage := carried.between.1
      unheld := carried.between.2, fits := extentAfter, retained := carried.footprint }
  exact RootPositiveToCachedCaller.completes options limits remaining span debugOff fuel budget statementFuel older caller rootFrame
      _ rawMachine run length count base tag rawStorage rawRights countPositive countFits disjoint
      (by rw [addr,rawId]; exact address) size afterPointer newValue (by rw [ready16])
      (slot2.trans countSlot) (fun i bound lo hi => by
        have lookup := (tail i lo).trans (deadTail i lo (by omega))
        exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans lookup))
      ((tail 24 (by decide)).trans (deadTail 24 (by decide) (by decide))) (body.trans entry.body)
      (identity.trans entry.identity) (callee.trans entry.callee) location (by rw [extra]; exact entry.noClocks)
      mode ghost shallow direct noDataRace (trackEq.trans track) rootThread activeThread rootTop callerRank dispatch dispatchFuel
      nativeBackend arithmetic gc fixed source (by rw [extra]; exact outerRank) (by rw [extra]; exact innerRank)
      maskLength maskShape provShape rawFits root roots extentAfter targetBound
      (by rw [extrasPreserved,rawId]; exact extras) (slot0.trans zeroSlot) newSlot holder owned
      (by rw [extra]; exact ownership) (by rw [rawId]; exact ledger) (varargsEq.trans noVarargs)

end DuplicatePrefix.RootPositiveFromLength

#print axioms DuplicatePrefix.RootPositiveFromLength.cached

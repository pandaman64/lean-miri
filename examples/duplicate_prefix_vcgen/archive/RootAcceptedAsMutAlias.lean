import duplicate_prefix.AsMutAliasDefs
import duplicate_prefix.RootAcceptedAsMut
import duplicate_prefix.AsMutDisjointByte

namespace DuplicatePrefix.RootAcceptedAsMutAlias

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open Miri.Verification.RangeModifyLaw
open CanonicalConfigFacts PreparedArguments SourceDomain ArchiveForestProjection NonemptyReturnWatch AsMutHolderScope

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

/-- The real accepted path from the post-length guard to bb7 frames the
aliased output byte and preserves the source holder's active footprint. -/
theorem completes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
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
    (storage : InitializedRegion (Storage.withCurrent older frame machine) length)
    (loan : ExclusiveRegion (Storage.withCurrent older frame machine) length storage parentTag)
    (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id, base⟩)
    (nonnull : base + storage.relativeStart.bytes ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).entries.any
      (·.value.ty == 2) = false)
    (source : PreparedContracts.SourceComparator)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch + 1)
    (defaultMode : loan.tracker.retagMode = .Default)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ older.size)
    (keyReady : RetagInsertionCapacity.Ready storage.entry.allocation.extra)
    (keySpace : storage.entry.allocation.extra.nodes.size+1 < 2^32)
    (inputAge : ∀ i node, storage.entry.allocation.extra.nodeAt i = some node →
      node.tag.value.toNat < loan.tracker.global.nextPointerTag.value.toNat)
    (activeAge : ∀ old, loan.tracker.global.protectedTags.contains old = true →
      old.value.toNat < loan.tracker.global.nextPointerTag.value.toNat)
    (tagBudget : loan.tracker.global.nextPointerTag.value.toNat+2 < 2^64)
    (sourceNode : TreeNode) (sourceAt : storage.entry.allocation.extra.nodeAt loan.source = some sourceNode)
    (hidden : sourceNode.isExposed = false)
    (sourceScope : AccessedWithin storage.entry.allocation.extra loan.source storage.relativeStart.bytes
      (storage.relativeStart.bytes+length))
    (observed : ReturnWatch storage.entry.allocation.extra loan.source storage.relativeStart.bytes
      (storage.relativeStart.bytes+length))
    (cmp : ProjectionMetadataFacts.NullComparator) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let oldPointer := Pointer.new (.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))
    let oldValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base oldPointer length RootCompilerFacts.sliceLayout).imm
    let newTag := loan.tracker.global.nextPointerTag
    let newPointer := Pointer.new (.concrete storage.id newTag) oldPointer.offset
    let newValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base newPointer length RootCompilerFacts.sliceLayout).imm
    (frame.locals[1]'(by omega)).value = .live (.immediate oldValue) →
    ∃ (afterFrame : CompilerFrameContext.ActualFrame)
        (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
        (next : InitializedRegion (Storage.withCurrent older afterFrame afterMachine) length)
        (rights : ExclusiveRegion (Storage.withCurrent older afterFrame afterMachine) length next
          (loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag)),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent older frame machine)
        (Storage.withCurrent older afterFrame afterMachine) ∧
      afterFrame.location = .mir ⟨7,0⟩ ∧
      afterFrame.body = frame.body ∧ afterFrame.bodyIdentity = frame.bodyIdentity ∧
      afterFrame.functionInstance = frame.functionInstance ∧ afterFrame.extra = frame.extra ∧
      afterFrame.trackCallerArg = frame.trackCallerArg ∧
      afterFrame.returnPlace = frame.returnPlace ∧ afterFrame.returnContinuation = frame.returnContinuation ∧
      afterFrame.vaList = frame.vaList ∧ afterFrame.localsIdentity = frame.localsIdentity ∧
      next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
      next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } ∧
      next.entry.allocation.extra.roots = #[root] ∧
      next.relativeStart.bytes.toNat + length.toNat ≤ next.entry.allocation.extra.locations.size.bytes.toNat ∧
      rights.tracker.retagMode = .Default ∧
      next.entry.allocation.extra = AsMutDisjointByte.released storage.entry.allocation.extra loan.tracker.global parentTag
        storage.relativeStart (Size.ofBytes length) ∧
      next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
      rights.tracker.global.protectedTags = loan.tracker.global.protectedTags ∧
      afterFrame.locals.size = 25 ∧
      afterFrame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base
        (.new (.concrete storage.id (loan.tracker.global.nextPointerTag.succ.getD loan.tracker.global.nextPointerTag))
          (Size.ofBytes (base+storage.relativeStart.bytes)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      afterFrame.locals[0]? = frame.locals[0]? ∧ afterFrame.locals[2]? = frame.locals[2]? ∧
      (∀ i, 17 ≤ i → afterFrame.locals[i]? = frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate afterFrame ∧
      afterFrame.locals[16]? = some ⟨.live (.immediate newValue),some RootCompilerFacts.sliceLayout⟩ ∧
      afterMachine.user.addresses = machine.user.addresses ∧ afterMachine.dataRace = none ∧
      afterMachine.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl afterMachine.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl afterMachine.user).gcInterval = 0 ∧
      afterMachine.user.payload.payload.user.backend = .none ∧
      afterMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∀ key, key ≠ storage.id → afterMachine.memory.live[key]? = machine.memory.live[key]?) ∧
      afterMachine.user.payload.ghost = false ∧ afterMachine.user.payload.validation = .Shallow ∧
      (frame.extra.userRelevance = 255 → thread.topUserRelevantFrame = some older.size →
        ∃ reported, afterMachine.threads.activeThread? = some reported ∧ reported.topUserRelevantFrame = some older.size) ∧
      ActiveImage next.entry.allocation.extra loan.tracker.global.protectedTags loan.source rights.source parentTag
        storage.relativeStart.bytes (storage.relativeStart.bytes+length) ∧
      observed.After next.entry.allocation.extra rights.source loan.tracker.global.nextPointerTag
        (AsMutDisjointByte.rawTag loan.tracker.global) := by
  intro cfg oldPointer oldValue newTag newPointer newValue args
  let data := AsMutDisjointByte.reservationInputs storage parentTag loan root capacity extent
  have future := RetagSuccessorCapacity.afterReservationWithData storage.entry.allocation.extra loan.tracker.global
    parentTag loan.source root storage.relativeStart (Size.ofBytes length) data keyReady keySpace inputAge tagBudget
  obtain ⟨raw,image⟩ := carrierImage storage.entry.allocation.extra loan.tracker.global parentTag
    loan.source root storage.relativeStart (Size.ofBytes length) observed data keyReady keySpace inputAge
    activeAge tagBudget sourceNode sourceAt hidden sourceScope
  obtain ⟨result,final,next,rights,trace,loc,body,identity,callee,extra,track,saved,cont,argsEq,locals,nextId,nextOffset,
    physical,roots,extentAfter,mode,tree,maskAfter,slots,pointerSlot,s0,s2,tail,immediate,s16,addresses,race,fixed,
    noArithmetic,noGcAfter,noBackend,extras,unrelated,ghost,shallow,cache⟩ :=
    RootAcceptedAsMut.completes options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
      older frame machine length base parentTag positive bounded valid count accepted entry none7 slot15 slot16
      sourceCached noRace storage loan root capacity tagRoom extent address nonnull metadata noAlias source dispatch dispatchFuel
      defaultMode backend unchecked noGc thread active relevant future cmp args
  have treeEq : next.entry.allocation.extra = AsMutDisjointByte.released storage.entry.allocation.extra
      loan.tracker.global parentTag storage.relativeStart (Size.ofBytes length) := by
    unfold AsMutDisjointByte.released AsMutDisjointByte.installed AsMutDisjointByte.reserved
      AsMutDisjointByte.mask AsMutDisjointByte.rawTag
    exact tree
  have selected : rights.source = raw := by
    apply Option.some.inj
    have key := rights.tagKnown
    rw [treeEq] at key
    exact key.symm.trans image.rawKey
  have restored : rights.tracker.global.protectedTags = loan.tracker.global.protectedTags :=
    maskAfter.trans (RawHolderScope.fresh_mask_restored loan.tracker.global.protectedTags
      (AsMutDisjointByte.rawTag loan.tracker.global) .StrongProtector image.tagAbsent)
  refine ⟨result,final,next,rights,trace,loc,body,identity,callee,extra,track,saved,cont,argsEq,locals,nextId,nextOffset,
    physical,roots,extentAfter,mode,treeEq,?_,restored,slots,pointerSlot,s0,s2,tail,immediate,s16,addresses,race,fixed,
    noArithmetic,noGcAfter,noBackend,extras,unrelated,ghost,shallow,cache,?_,?_⟩
  · rw [treeEq]
    exact image.size
  · rw [treeEq,selected]
    exact image.active
  · rw [treeEq,selected]
    exact image.output

end DuplicatePrefix.RootAcceptedAsMutAlias

#print axioms DuplicatePrefix.RootAcceptedAsMutAlias.completes

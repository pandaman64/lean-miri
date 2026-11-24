import ActiveRootSliceRegion
import duplicate_prefix.RootAcceptedAsMutAlias

namespace DuplicatePrefix.RootZeroShallowReturn

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain ArchiveForestProjection
open RootAcceptedAsMutAlias NonemptyReturnWatch

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Exact root and heap state at bb7, including the independent output
protector and both source-derived raw and original slice authorities. -/
structure RawAfterActiveLength (cfg : RootConfig) (entry result : CompilerFrameContext.ActualFrame)
    (before final : LenExitFacts.MachineState) (source : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (length count offset base : UInt64)
    (holder : UniIndex) (holderTag reservationTag rawTag : BorTag) (tags : ProtectedTags)
    (watch : ReturnWatch source.allocation.extra holder offset (offset+length)) where
  region : InitializedRegion (Storage.withCurrent #[] result final) length
  rights : ExclusiveRegion (Storage.withCurrent #[] result final) length region rawTag
  location : result.location = .mir ⟨7,0⟩
  body : result.body = RootBody.reflected.body.body
  identity : result.bodyIdentity = RootBody.reflected.body.identity
  callee : result.functionInstance = RootBody.reflected.functionInstance
  extra : result.extra = entry.extra
  track : result.trackCallerArg = entry.trackCallerArg
  place : result.returnPlace = entry.returnPlace
  continuation : result.returnContinuation = entry.returnContinuation
  varargs : result.vaList = entry.vaList
  localsIdentity : result.localsIdentity = entry.localsIdentity
  sourceId : region.id = id
  relative : region.relativeStart = Size.ofBytes offset
  allocationData : region.entry = {source with allocation := source.allocation.setExtra region.entry.allocation.extra}
  roots : ∃ root, region.entry.allocation.extra.roots = #[root]
  allocationSize : region.entry.allocation.extra.locations.size = source.allocation.extra.locations.size
  span : offset.toNat + length.toNat ≤ region.entry.allocation.extra.locations.size.bytes.toNat
  mode : rights.tracker.retagMode = .Default
  protections : rights.tracker.global.protectedTags = tags
  size : result.locals.size = 25
  countSlot : result.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  resultSlot : result.locals[0]? = entry.locals[0]?
  tail : ∀ i, 17 ≤ i → result.locals[i]? = entry.locals[i]?
  direct : CopyHelperCleanup.AllImmediate result
  pointer : result.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base
    (.new (.concrete id rawTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩
  reservedSlot : result.locals[16]? = some ⟨.live (.immediate
    (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (.new (.concrete id reservationTag) (Size.ofBytes (base+offset))) length RootCompilerFacts.sliceLayout).imm),
    some RootCompilerFacts.sliceLayout⟩
  addresses : final.user.addresses = before.user.addresses
  extras : final.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras
  raceOff : final.dataRace = none
  fixed : final.threads.fixedScheduling = true
  unchecked : (cfg.terminators.getControl final.user).checkedArithmetic = false
  noGC : (cfg.terminators.getControl final.user).gcInterval = 0
  noBackend : final.user.payload.payload.user.backend = .none
  ghost : final.user.payload.ghost = false
  shallow : final.user.payload.validation = .Shallow
  current : ∃ thread, final.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0
  unrelated : ∀ key, key ≠ id → final.memory.live[key]? = before.memory.live[key]?
  original : ActiveImage region.entry.allocation.extra tags holder rights.source holderTag offset (offset+length)
  output : watch.After region.entry.allocation.extra rights.source reservationTag rawTag

/-- Execute the current root from the actual length checkpoint through
its accepted decision, mutable helper frame, retags and return to bb7. -/
theorem RootLengthOfActiveSlice.toAliasedRaw
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1) (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false) (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    {initialFrame frame : CompilerFrameContext.ActualFrame}
    {initial final : LenExitFacts.MachineState} {root : RetainedSlice initial}
    {allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind} {offset len count : UInt64}
    {tracker : MachineHooks.BorrowState}
    (post : RootLengthOfActiveSlice (PreparedContracts.actualConfig options () (remaining+1) span)
      #[] initialFrame frame initial final root allocation offset len count tracker)
    (accepted : ¬ count > len/2) (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (before : InitializedRegion (Storage.withCurrent #[] initialFrame initial) len)
    (sameId : before.id = root.id) (sameAllocation : before.entry = allocation)
    (sameStart : before.relativeStart.bytes = offset)
    (originalExtent : offset.toNat + len.toNat ≤ allocation.allocation.extra.locations.size.bytes.toNat)
    (space : allocation.allocation.extra.nodes.size+3 < 2^32)
    (tagBudget : tracker.global.nextPointerTag.value.toNat+4 < 2^64)
    (protectedAge : ∀ tag, tracker.global.protectedTags.contains tag = true →
      tag.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (base : UInt64)
    (address : initial.user.addresses.baseAddr.find? (fun row => row.allocId == before.id) = some ⟨before.id,base⟩)
    (nonnull : base + offset ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] initialFrame initial)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] initialFrame initial)).entries.any
      (·.value.ty == 2) = false)
    (source : PreparedContracts.SourceComparator) (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (noRace : initial.dataRace = none) (backend : initial.user.payload.payload.user.backend = .none)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (rank : initialFrame.extra.userRelevance = 255)
    (slot1 : initialFrame.locals[1]? = some ⟨.live (.immediate (.scalarPair
      (.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete before.id root.tag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.sliceLayout⟩)
    (slot2 : initialFrame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (dead : ∀ i, 15 ≤ i → i ≤ 24 → initialFrame.locals[i]? = some ⟨.dead,none⟩)
    (watch : ReturnWatch post.branch.ready.entry.allocation.extra post.branch.ready.source offset (offset+len)) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let global := post.branch.ready.tracker.global
    ∃ result done,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame final)
        (Storage.withCurrent #[] result done) ∧ Nonempty
        (RawAfterActiveLength cfg initialFrame result initial done post.branch.ready.entry before.id len count offset base
          post.branch.ready.source post.branch.ready.tag global.nextPointerTag (AsMutDisjointByte.rawTag global)
          global.protectedTags watch) := by
  intro cfg global
  let storage := post.storageAtOffset before sameId sameAllocation sameStart
  obtain ⟨checked,sourceEq,trackerEq⟩ := post.loanAtOffset before sameId sameAllocation sameStart originalExtent
  let ready := post.branch.ready
  let loan : ExclusiveRegion (Storage.withCurrent #[] frame final) len storage ready.tag := {
    checked with
    tracker := ready.tracker
    tracked := ready.tracked
    source := ready.source
    tagKnown := ready.indexed
    sourcePresent := ⟨ready.node,ready.found,ArchiveForestProjection.ready_tag_at _ post.keys _ _ _
      ready.indexed ready.found⟩
    exclusive := by simpa only [sourceEq,trackerEq] using checked.exclusive }
  obtain ⟨thread, active, top⟩ := post.rootCache rank
  have relevant : ∀ i, thread.topUserRelevantFrame = some i → i ≤ 0 := by
    intro i h
    have equal := Option.some.inj (h.symm.trans top)
    change i = 0 at equal
    omega
  have valid : 16 < frame.locals.size := by rw [post.branch.guard.size]; decide
  have field1 : frame.locals[1]? = _ := (post.bystanders 1 (.inl (by decide))).trans slot1
  have value1 := Option.some.inj ((Array.getElem?_eq_getElem (show 1 < frame.locals.size by omega)).symm.trans field1)
  have capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source ready.root
      loan.tracker.global.nextPointerTag := post.insertionCapacity
  have range : storage.relativeStart.bytes.toNat + len.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat := by
    change offset.toNat + len.toNat ≤ post.branch.ready.entry.allocation.extra.locations.size.bytes.toNat
    rw [post.branch.rangeCapacity]
    exact originalExtent
  have metadataFinal : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame final)).metadata =
      PreparedReflection.actual.runtime := by
    change final.user.payload.payload.user.types.metadata = _
    rw [post.branch.stable.types]
    exact metadata
  have noAliasFinal : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame final)).entries.any
      (·.value.ty == 2) = false := by
    change final.user.payload.payload.user.types.entries.any _ = _
    rw [post.branch.stable.types]
    exact noAlias
  have tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615 := by
    change ready.tracker.global.nextPointerTag.value ≠ 18446744073709551615
    intro equal
    have next := post.nextTag
    rw [equal] at next
    simp at next
    omega
  have keyRoom : storage.entry.allocation.extra.nodes.size+1 < 2^32 := by
    change post.branch.ready.entry.allocation.extra.nodes.size+1 < 2^32
    have growth := post.nodes
    omega
  have tagSpace : loan.tracker.global.nextPointerTag.value.toNat+2 < 2^64 := by
    change post.branch.ready.tracker.global.nextPointerTag.value.toNat+2 < 2^64
    rw [post.nextTag]
    omega
  have protectionAge (tag : BorTag) (active : loan.tracker.global.protectedTags.contains tag = true) :
      tag.value.toNat < loan.tracker.global.nextPointerTag.value.toNat := by
    change post.branch.ready.tracker.global.protectedTags.contains tag = true at active
    rw [post.protectors] at active
    change tag.value.toNat < post.branch.ready.tracker.global.nextPointerTag.value.toNat
    rw [post.nextTag]
    have older := protectedAge tag active
    omega
  obtain ⟨result,done,rawStorage,rawRights,trace,loc,body,identity,callee,extra,track,saved,cont,argsEq,locals,nextId,
    nextOffset,physical,roots,extentAfter,mode,_,allocationSize,sameTags,size,pointerSlot,s0,s2,kept,direct,s16,addresses,race,
    fixed,unchecked,noGC,noBackend,extras,unrelated,ghost,shallow,cached,original,output⟩ :=
    RootAcceptedAsMutAlias.completes options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
      #[] frame final len base ready.tag positive bounded valid count accepted post.branch.guard post.uncached7
      ((post.bystanders 15 (.inr (by decide))).trans (dead 15 (by decide) (by decide)))
      ((post.bystanders 16 (.inr (by decide))).trans (dead 16 (by decide) (by decide)))
      (congrArg LocalState.layout value1) (post.branch.stable.race.trans noRace)
      storage loan ready.root capacity tagRoom range (by change final.user.addresses.baseAddr.find? _ = some ⟨before.id,base⟩; rw [post.branch.stable.addresses]; exact address)
      nonnull metadataFinal noAliasFinal source dispatch dispatchFuel
      post.branch.defaultMode (post.branch.stable.backend.trans backend)
      post.branch.unchecked post.branch.gc thread active relevant post.keys keyRoom
      post.tagAge protectionAge tagSpace ready.node
      ready.found ready.unexposed post.branch.activeScope watch cmp
      (by
        change (frame.locals[1]'(by omega)).value = .live (.immediate (.scalarPair
          (.fromPointer cfg.access.runtime.base (Pointer.new (.concrete before.id ready.tag) (Size.ofBytes (base+offset))))
          (.fromScalarInt (.ofUInt64 len))))
        rw [show ready.tag = root.tag from post.branch.tag]
        exact congrArg LocalState.value value1)
  refine ⟨result,done,trace,⟨{
    region := rawStorage
    rights := rawRights
    location := loc
    body := body.trans post.branch.guard.body
    identity := identity.trans post.branch.guard.identity
    callee := callee.trans post.branch.guard.callee
    extra := extra.trans post.frameExtra
    track := track.trans post.trackCallerArg
    place := saved.trans post.place
    continuation := cont.trans post.continuation
    varargs := argsEq.trans post.varargs
    localsIdentity := locals.trans post.localsIdentity
    sourceId := nextId
    relative := nextOffset
    allocationData := physical
    roots := ⟨ready.root,roots⟩
    allocationSize := allocationSize
    span := by
      rw [nextOffset] at extentAfter
      exact extentAfter
    mode := mode
    protections := sameTags
    size := size
    countSlot := s2.trans ((post.bystanders 2 (.inl (by decide))).trans slot2)
    resultSlot := s0.trans (post.bystanders 0 (.inl (by decide)))
    tail := fun i bound => (kept i bound).trans (post.bystanders i (.inr (by omega)))
    direct := direct
    pointer := pointerSlot
    reservedSlot := s16
    addresses := addresses.trans post.branch.stable.addresses
    extras := extras.trans post.branch.stable.extras
    raceOff := race
    fixed := fixed
    unchecked := unchecked
    noGC := noGC
    noBackend := noBackend
    ghost := ghost
    shallow := shallow
    current := cached (by rw [post.frameExtra]; exact rank) top
    unrelated := fun key distinct => (unrelated key distinct).trans
      (post.branch.unrelated key (by rwa [← sameId]))
    original := original
    output := output }⟩⟩

end DuplicatePrefix.RootZeroShallowReturn

#print axioms DuplicatePrefix.RootZeroShallowReturn.RootLengthOfActiveSlice.toAliasedRaw

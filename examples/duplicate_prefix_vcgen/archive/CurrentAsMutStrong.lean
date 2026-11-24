import duplicate_prefix.CurrentAsMutFnEntry
import duplicate_prefix.CurrentTwoPhaseStructural
import duplicate_prefix.RetagReleaseFootprint

namespace DuplicatePrefix.CurrentAsMutStrong
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures
open Miri.Verification.MutableTypedRetag
open CanonicalConfigFacts PreparedArguments SourceDomain MutableSliceRights ExclusiveTypedRetag
open ArchiveForestProjection GeneralRangeMapOrigins CurrentTwoPhaseStructural

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem retag
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (reference : LocalLayout) (referenceTy : reference.ty = 1)
    (before : RootState) (length base : UInt64) (parentTag : BorTag)
    (storage : InitializedRegion before length) (loan : ExclusiveRegion before length storage parentTag)
    (mode : loan.tracker.retagMode = .FnEntry)
    (frame : CompilerFrameContext.ActualFrame) (ledger : FrameState)
    (current : before.stack.currentFrame? = some frame)
    (frameLedger : frame.extra.borrowTracker = some ledger)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (address : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) =
      some ⟨storage.id, base⟩)
    (positive : 0 < length) (bounded : length ≤ 9223372036854775807)
    (room : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (raceOff : before.machine.dataRace = none)
    (root : UniIndex)
    (capacity : InsertionCapacity storage.entry.allocation.extra loan.source root loan.tracker.global.nextPointerTag)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get before).metadata = PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get before).entries.any (·.value.ty == 2) = false) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let tag := loan.tracker.global.nextPointerTag
    let atAddress := Size.ofBytes (base + storage.relativeStart.bytes)
    let input := RetagReferencePlace.sliceValue cfg.access.runtime.base (Pointer.new (.concrete storage.id parentTag) atAddress)
      length reference
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base (Pointer.new (.concrete storage.id tag) atAddress)
      length reference
    ∃ after : RootState, cfg.validity.retagPointer () input reference.ty before = .ok (some output) after ∧
      after.stack = ⟨before.stack.frames.pop.push
        {frame with extra := {frame.extra with borrowTracker := some (ledger.addProtector storage.id tag)}}⟩ ∧
      after.machine.user = before.machine.user ∧ after.machine.dataRace = none ∧
      after.machine.threads = before.machine.threads ∧
      (∀ key, key ≠ storage.id → after.machine.memory.live[key]? = before.machine.memory.live[key]?) ∧
      ∃ (next : InitializedRegion after length) (region : ExclusiveRegion after length next tag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        next.entry.allocation.extra.roots = #[root] ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        (∃ node, next.entry.allocation.extra.nodeAt region.source = some node ∧ node.tag = tag ∧ node.isExposed = false) ∧
        RetagReleaseFootprint.MaterializedWithin next.entry.allocation.extra region.source
          next.relativeStart.bytes (next.relativeStart.bytes + length) ∧
        RetagReleaseFootprint.VacantRows next.entry.allocation.extra ∧
        next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } ∧
        next.entry.allocation.extra = ExclusiveTypedRetag.protectedFrozenTree storage.entry.allocation.extra
          loan.tracker.global.protectedTags parentTag tag storage.relativeStart (Size.ofBytes length) ∧
        region.tracker.global.protectedTags = loan.tracker.global.protectedTags.insert tag .StrongProtector := by
  intro cfg tag atAddress input output
  have facts := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, table, discriminant, globals, validity, arithmetic, wiring, ensure, sync⟩ := facts.validitySources
  let h := CurrentMutableRetag.adapted cfg pointers
  have hooked : cfg.validity.retagPointer () = TypedRetag.machineRetagPtrValue h options.limits.retag := by
    dsimp only [h, cfg, CurrentMutableRetag.adapted]
    rw [validity]
    rfl
  let prep := CurrentMutableRetag.compiler
  have sources : TypedRetagFields.SourceFields h prep cfg.access cfg.validity.projection cfg.validity.vtable pointers () := by
    apply TypedRetagFields.adapted_sources
    · exact facts.retagLog
    · rw [facts.retagPrecise, preciseOff]
    · rw [facts.retagImplicit, implicitOff]
  have width : pointers.arithmetic = ⟨Size.ofBytes 8⟩ := arithmetic
  obtain ⟨global, allocated⟩ := allocate_tag loan.tracker.global room
  have sameProtectors : global.protectedTags = loan.tracker.global.protectedTags := by
    unfold GlobalState.newPointerTag at allocated
    split at allocated
    · contradiction
    · cases allocated
      rfl
  let tracker := {loan.tracker with global}
  let allocatedState : RootState := {before with machine := {before.machine with borrowTracker := some tracker}}
  let source : InitializedRegion allocatedState length :=
    {id := storage.id, relativeStart := storage.relativeStart, entry := storage.entry,
      live := storage.live, writable := storage.writable, backed := storage.backed,
      fits := storage.fits, initialized := storage.initialized}
  let oldPointer : Pointer Provenance := Pointer.new (.concrete storage.id parentTag) atAddress
  let place := RetagReferencePlace.slicePlace oldPointer length ProjectionMetadataFacts.sliceLayout
  have signed : length.toNat < 2^63 :=
    Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp bounded) (by decide)
  obtain ⟨checked, resolved⟩ := cached_pointer_inputs h pointers cfg.access allocatedState place length base parentTag
    source sources.check sources.resolve wiring width address rfl positive signed
  let location : RetagPipeline.ResolvedLocation := ⟨storage.id, storage.relativeStart, .concrete parentTag⟩
  let registered := withStrongProtector allocatedState location tag frame ledger tracker
  have ensureLive : h.ensureTreeExtra storage.id registered = .ok () registered := by
    rw [sources.ensure, ensure]
    apply ensure_live .global globals storage.id registered storage.entry storage.live
    rw [sync]
  have known := loan.sourcePresent
  obtain ⟨node, parentNode, _⟩ := known
  have constantFreeze : h.typeIsFreeze place.layout.ty = pure true := by
    change h.typeIsFreeze ProjectionMetadataFacts.sliceLayout.ty = _
    rw [ProjectionMetadataFacts.slice_layout_shape.1]
    with_unfolding_all rfl
  have nonempty : (Size.ofBytes length).bytes ≠ 0 := by
    intro zero
    change length = 0 at zero
    subst length
    exact (by decide : ¬ (0 : UInt64) < 0) positive
  obtain ⟨depth, rank⟩ := capacity.ranked
  have owners := ownedOn before length parentTag storage loan extent
  have allocationOwners : OwnedOn (fun location => LocationRights storage.entry.allocation.extra location
      tracker.global.protectedTags loan.source) storage.relativeStart.bytes
      (storage.relativeStart.bytes + length) storage.entry.allocation.extra.locations := by
    simpa only [tracker, sameProtectors] using owners
  obtain ⟨after, tree, child, reborrowed, live, tracked, _, sizeEq, coherent, roots, childKey,
    ⟨childData, childNode, childTag, childUnexposed⟩, scope, emptyRows, stack, user, race, threads, childOwners, _, frozenTree, unrelated⟩ :=
    ExclusiveTypedRetag.reborrow_exclusive_region_with_footprint h options.limits.retag place (Size.ofBytes length) tag parentTag location
      allocatedState allocatedState allocatedState allocatedState frame ledger tracker storage.entry loan.source root node
      checked resolved (by rw [sources.log]; rfl) rfl current frameLedger rfl storage.live storage.writable
      sources.precise constantFreeze nonempty ensureLive raceOff loan.coherent parentNode capacity.roots loan.tagKnown
      depth rank capacity.freshKey capacity.freshNode capacity.room capacity.aligned capacity.reuse capacity.clean extent allocationOwners
  have completed := CurrentAsMutFnEntry.completedPointer options remaining span fuel fuelEq pointers reference referenceTy
    storage.id parentTag tag (base + storage.relativeStart.bytes) length bounded before after loan.tracker global
    loan.tracked mode implicitOff frame current callee allocated cmp metadata noAlias reborrowed
  have referenceEffect : cfg.validity.retagPointer () input reference.ty before = .ok (some output) after := by
    rw [hooked]
    exact completed
  have nextExtent : storage.relativeStart.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat := by
    rwa [sizeEq]
  obtain ⟨next, idEq, offsetEq, allocEq, ⟨rights⟩⟩ := region_from_cached_reborrow before after length storage tree tag child
    (registeredTracker tracker tag) live tracked coherent childKey ⟨childData, childNode, childTag⟩ nextExtent childOwners
  have sourceEq : rights.source = child := by
    have key := rights.tagKnown
    rw [allocEq] at key
    change tree.indexOfTag tag = some rights.source at key
    exact Option.some.inj (key.symm.trans childKey)
  refine ⟨after, referenceEffect, stack, user, race.trans raceOff, threads, unrelated, next, rights, idEq, offsetEq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [allocEq]
    exact roots
  · rw [allocEq]
    exact sizeEq
  · rw [allocEq, sourceEq]
    exact ⟨childData, childNode, childTag, childUnexposed⟩
  · rw [allocEq, sourceEq, offsetEq]
    exact scope
  · rw [allocEq]
    exact emptyRows
  · rw [allocEq]
    rfl
  · rw [allocEq]
    have tags : tracker.global.protectedTags = loan.tracker.global.protectedTags := sameProtectors
    simpa only [Allocation.setExtra, Allocation.mapExtra, tags, location] using frozenTree
  · have exactTracker : rights.tracker = registeredTracker tracker tag :=
      Option.some.inj (rights.tracked.symm.trans tracked)
    rw [exactTracker]
    exact congrArg (·.insert tag .StrongProtector) sameProtectors

end DuplicatePrefix.CurrentAsMutStrong

#print axioms DuplicatePrefix.CurrentAsMutStrong.retag

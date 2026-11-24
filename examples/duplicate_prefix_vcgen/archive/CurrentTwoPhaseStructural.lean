import duplicate_prefix.CurrentMutableRetag
import duplicate_prefix.ExclusiveTypedRetag
import duplicate_prefix.ExclusiveTwoPhaseRetag

namespace DuplicatePrefix.CurrentTwoPhaseStructural
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures
open Miri.Verification.MutableTypedRetag
open CanonicalConfigFacts PreparedArguments SourceDomain MutableSliceRights ExclusiveTypedRetag
open ArchiveForestProjection GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem ownedOn (before : RootState) (length : UInt64) (tag : BorTag)
    (storage : InitializedRegion before length) (loan : ExclusiveRegion before length storage tag)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat) :
    OwnedOn (fun location => LocationRights storage.entry.allocation.extra location
      loan.tracker.global.protectedTags loan.source) storage.relativeStart.bytes
      (storage.relativeStart.bytes + length) storage.entry.allocation.extra.locations := by
  intro position present positive start stop index node found
  let tree := storage.entry.allocation.extra
  let segment := tree.locations.entries[position]
  let lower := storage.relativeStart.bytes.toNat
  have noWrap : lower + length.toNat < 2^64 :=
    Nat.lt_of_le_of_lt extent tree.locations.size.bytes.toNat_lt
  have upper : (storage.relativeStart.bytes + length).toNat = lower + length.toNat := by
    simp [lower, UInt64.toNat_add, Nat.mod_eq_of_lt noWrap]
  have segmentPositive := (GeneralRangeMapGeometry.facts tree.locations loan.coherent.ranges (Nat.ne_of_gt (Nat.zero_lt_of_lt present))).2.1 position present
  let distance := max lower segment.range.start.toNat - lower
  have inRange : distance < length.toNat := by
    dsimp only [distance]
    change segment.range.start.toNat < _ at start
    omega
  have fromStart : segment.range.start.toNat ≤ lower + distance := by
    dsimp only [distance]
    omega
  have beforeStop : lower + distance < segment.range.stop.toNat := by
    change lower < segment.range.stop.toNat at stop
    change segment.range.start.toNat < segment.range.stop.toNat at segmentPositive
    dsimp only [distance]
    omega
  obtain ⟨state, value, ownLocal, ownForeign⟩ := loan.exclusive distance inRange segment
    (Array.mem_iff_getElem.mpr ⟨position, present, rfl⟩) fromStart beforeStop index node found
  exact ⟨state, value, ownLocal, ownForeign⟩

/-- Non-consuming tag allocator and forest data needed to install the next
child. This predicate speaks only about pre-state metadata. -/
structure InsertionCapacity (tree : BorrowTree) (parent root : UniIndex) (tag : BorTag) : Prop where
  roots : tree.roots = #[root]
  ranked : ∃ depth : BorrowTree.ZeroProtection.ParentDepth tree.nodes, depth.depth parent < tree.nodes.size
  freshKey : tree.indexOfTag tag = none
  freshNode : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag
  room : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295
  aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.size
  reuse : ∀ index, tree.tagMapping.deassigned.back? = some index →
    index.toNat < tree.nodes.size ∧ tree.nodeAt index = none
  clean : ∀ index, tree.nodeAt index = none →
    ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none

theorem retag
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (reference : LocalLayout) (referenceTy : reference.ty = 1)
    (before : RootState) (length base : UInt64) (parentTag : BorTag)
    (storage : InitializedRegion before length) (loan : ExclusiveRegion before length storage parentTag)
    (mode : loan.tracker.retagMode = .TwoPhase)
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
      after.stack = before.stack ∧ after.machine.user = before.machine.user ∧ after.machine.dataRace = none ∧
      after.machine.threads = before.machine.threads ∧
      ∃ (next : InitializedRegion after length) (right : ExclusiveRegion after length next tag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        next.entry.allocation.extra.roots = #[root] ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        right.tracker.retagMode = loan.tracker.retagMode := by
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
  have ensureLive : h.ensureTreeExtra storage.id allocatedState = .ok () allocatedState := by
    rw [sources.ensure, ensure]
    apply ensure_live .global globals storage.id allocatedState storage.entry storage.live
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
  let location : RetagPipeline.ResolvedLocation := ⟨storage.id, storage.relativeStart, .concrete parentTag⟩
  obtain ⟨after, tree, child, reborrowed, live, tracked, stack, user, race, threads, sizeEq, coherent, roots, childKey,
    childNode, childOwners⟩ :=
    ExclusiveTwoPhaseRetag.reborrow_exclusive h options.limits.retag place (Size.ofBytes length) tag parentTag location
      allocatedState allocatedState allocatedState allocatedState tracker storage.entry loan.source root node
      checked resolved (by rw [sources.log]; rfl) rfl rfl storage.live storage.writable
      sources.precise constantFreeze nonempty ensureLive raceOff loan.coherent parentNode capacity.roots loan.tagKnown
      depth rank capacity.freshKey capacity.freshNode capacity.room capacity.aligned capacity.reuse capacity.clean extent allocationOwners
  have samePolicy : ExclusiveTwoPhaseRetag.policy = RootMutableReborrow.policy := rfl
  have completed := CurrentMutableRetag.completedPointer options remaining span fuel fuelEq pointers reference referenceTy
    storage.id parentTag tag (base + storage.relativeStart.bytes) length bounded before after loan.tracker global
    loan.tracked mode allocated cmp metadata noAlias (samePolicy ▸ reborrowed)
  have referenceEffect : cfg.validity.retagPointer () input reference.ty before = .ok (some output) after := by
    rw [hooked]
    exact completed
  have nextExtent : storage.relativeStart.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat := by
    rwa [sizeEq]
  obtain ⟨next, idEq, offsetEq, allocEq, ⟨rights⟩⟩ := region_from_cached_reborrow before after length storage tree tag child tracker
    live tracked coherent childKey childNode nextExtent childOwners
  refine ⟨after, referenceEffect, stack, user, race.trans raceOff, threads, next, rights, idEq, offsetEq, ?_, ?_, ?_⟩
  · rw [allocEq]
    exact roots
  · rw [allocEq]
    exact sizeEq
  · have known := rights.tracked
    change after.machine.borrowTracker = some rights.tracker at known
    rw [tracked] at known
    have trackedEq := Option.some.inj known
    rw [← trackedEq]

end DuplicatePrefix.CurrentTwoPhaseStructural

#print axioms DuplicatePrefix.CurrentTwoPhaseStructural.retag

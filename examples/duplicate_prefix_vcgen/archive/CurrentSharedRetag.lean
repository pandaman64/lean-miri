import duplicate_prefix.RootSharedRef
import duplicate_prefix.TypedSharedReborrow
import duplicate_prefix.SharedReborrowContinuity
import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.ProjectionMetadataFacts
import duplicate_prefix.ReferenceMetadataFacts
import duplicate_prefix.TypedRetagFields
import duplicate_prefix.RetagReferencePlace
import duplicate_prefix.ActualCurrentSlice

namespace DuplicatePrefix.CurrentSharedRetag
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts
open Miri.Verification
open Miri.DataStructures Miri.TreeBorrows.Tree
open ArchiveForestProjection SourceDomain GeneralRangeMapOrigins RetagSharedChild

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev compiler := ReferenceMetadataFacts.prepared
noncomputable abbrev runtime := PreparedReflection.actual.compiler.lifecycle.calls.runtime

noncomputable abbrev adapted (cfg : RootConfig) (pointers : RootPointers) :=
  TypedValidityProviders.retagHooks compiler runtime cfg.access cfg.validity.projection
    cfg.validity.vtable pointers () cfg.retag

theorem completedPointer
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (pointers : RootPointers) (reference : LocalLayout) (referenceTy : reference.ty = 7)
    (id : AllocId) (oldTag tag : BorTag) (address length : UInt64)
    (bounded : length ≤ 9223372036854775807)
    (before after : RootState) (borrow : MachineHooks.BorrowState)
    (global : GlobalState) (tracker : before.machine.borrowTracker = some borrow)
    (mode : borrow.retagMode = .Default)
    (fresh : borrow.global.newPointerTag = .ok (global,tag))
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get before).metadata = PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get before).entries.any (·.value.ty == 2) = false) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let h := adapted cfg pointers
    let oldPointer := Pointer.new (.concrete id oldTag) (Size.ofBytes address)
    let newPointer := Pointer.new (.concrete id tag) (Size.ofBytes address)
    let input := RetagReferencePlace.sliceValue cfg.access.runtime.base oldPointer length reference
    let result := RetagReferencePlace.sliceValue cfg.access.runtime.base newPointer length reference
    let place := RetagReferencePlace.slicePlace oldPointer length ProjectionMetadataFacts.sliceLayout
    TypedRetag.reborrow h options.limits.retag place (Size.ofBytes length) RootSharedRef.policy tag
      {before with machine := {before.machine with borrowTracker := some {borrow with global}}} =
      .ok (some (.concrete id tag)) after →
    TypedRetag.machineRetagPtrValue h options.limits.retag input reference.ty before =
      .ok (some result) after := by
  intro cfg h oldPointer newPointer input result place reborrowed
  have q : TypedRetagFields.ReferenceQueries h 1 2 := by
    apply TypedRetagFields.adapted_reference_queries
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
    · with_unfolding_all rfl
  have constructed : h.immPtrToMPlace input before = .ok place before := by
    change PointerPlaceMachine.fromImmediate cfg.access (CompilerExecutionProviders.pointerCompiler compiler) ()
      input before = _
    have deref : CompilerFacts.builtinDeref compiler.context reference.ty true = .ok (some place.layout.ty) := by
      rw [referenceTy, show place.layout.ty = 2 from ProjectionMetadataFacts.slice_layout_shape.1]
      with_unfolding_all rfl
    have layout : CompilerFacts.layoutOf compiler.context place.layout.ty = .ok place.layout := by
      rw [show place.layout.ty = 2 from ProjectionMetadataFacts.slice_layout_shape.1]
      exact ActualCurrentSlice.compilerLayout
    exact congrFun (RetagReferencePlace.canonical_from_immediate cfg.access compiler ()
      oldPointer length reference place.layout deref layout ProjectionMetadataFacts.slice_layout_shape.2.2) before
  have configFields := CanonicalConfigFacts.actual_fields options () remaining span
  have sameDynamic : PlaceDynamic.withVTable cfg.validity.projection.dynamic cfg.validity.vtable =
      PlaceDynamic.withVTable cfg.projection.dynamic cfg.validity.vtable := by
    obtain ⟨_, _, _, exactValidity⟩ := configFields.validity
    dsimp only [cfg]
    rw [exactValidity]
    rfl
  have sameFuel : cfg.validity.projection.dynamicFuel = cfg.projection.dynamicFuel := by
    obtain ⟨_, _, _, exactValidity⟩ := configFields.validity
    dsimp only [cfg]
    rw [exactValidity]
    rfl
  obtain ⟨sourceTable, maximum, maximumEq, dynamicEq⟩ := configFields.projectionDynamic
  have maxValue : maximum = Size.ofBytes 9223372036854775807 := by
    have computed : CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target =
        .ok (Size.ofBytes 9223372036854775807) := by rfl
    exact Except.ok.inj (maximumEq.symm.trans computed)
  have sizing : h.sizeAndAlign place before = .ok (some (Size.ofBytes length, Align.ONE)) before := by
    change DynamicLayout.sizeAndAlignFromMeta
      (PlaceDynamic.withVTable cfg.validity.projection.dynamic cfg.validity.vtable) ()
      cfg.validity.projection.dynamicFuel place.mplace.metadata place.layout before = _
    rw [sameDynamic, sameFuel, configFields.projectionDynamicFuel, fuelEq, dynamicEq]
    apply ProjectionMetadataFacts.with_vtable_size_at cmp _ sourceTable cfg.validity.vtable
      () before fuel length metadata noAlias
    simpa only [maxValue, Size.ofBytes] using bounded
  have styled := Miri.Verification.MutableTypedRetag.retag_place h options.limits.retag place
    (Size.ofBytes length) Align.ONE RootSharedRef.policy before before after borrow global tag
    (.concrete id oldTag) (.concrete id tag) sizing tracker fresh rfl reborrowed
  apply RootSharedRef.retagSharedPointer h options.limits.retag input result reference.ty 2
    before before before before after after place (Miri.Verification.MutableTypedRetag.taggedPlace place (.concrete id tag))
    borrow tracker mode
  · rw [referenceTy]
    with_unfolding_all rfl
  · rw [referenceTy]
    with_unfolding_all rfl
  · rw [q.unpin]
    rfl
  · rw [q.unsafeUnpin]
    rfl
  · rw [q.freeze]
    rfl
  · exact constructed
  · exact styled
  · rfl

/-- Observations of the actual shared retag, including its selected new
allocation tree and the read authority used to enter the length helper. -/
def ReadGrant (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (tag : BorTag) (root : UniIndex) (offset len : UInt64)
    (protectors : ProtectedTags) : Prop :=
  ∃ tree child,
    machine.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra tree} ∧
    CoherentForest tree ∧ tree.roots = #[root] ∧
    tree.locations.size = entry.allocation.extra.locations.size ∧
    tree.indexOfTag tag = some child ∧
    (∃ node, tree.nodeAt child = some node ∧ node.tag = tag ∧ node.defaultInitialPermission = .Frozen) ∧
    ∀ point : UInt64, offset.toNat ≤ point.toNat → point.toNat < (offset+len).toNat →
      ∀ row, ValueAt tree.locations point row → LocationAccessRights tree row protectors child .Read

private theorem uniform_partition (offset length capacity : Size)
    (bounds : offset.bytes.toNat + length.bytes.toNat ≤ capacity.bytes.toNat) :
    ∀ segment ∈ (DedupRangeMap.new length sharedState).iterAll.toList,
      (segment.range.start ≤ segment.range.stop ∧
        offset.bytes.toNat + segment.range.stop.toNat ≤ capacity.bytes.toNat) ∧
      segment.data = sharedState := by
  intro segment member
  by_cases empty : length.bytes = 0
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, empty] at member
  · simp [DedupRangeMap.new, DedupRangeMap.iterAll, beq_iff_eq, empty] at member
    subst segment
    exact ⟨⟨by simp, bounds⟩, rfl⟩

set_option maxHeartbeats 1200000 in
/-- Actual retagging of a cached, nonempty shared byte-slice. Address checks,
allocation resolution, the fresh tag counter, and both Tree Borrows edits
are executed by the production hooks from these independent heap premises. -/
theorem runDetailed
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (reference : LocalLayout) (referenceTy : reference.ty = 7)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (borrow : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some borrow) (mode : borrow.retagMode = .Default)
    (fresh : borrow.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (tagEq : tag = borrow.global.nextPointerTag)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 2) = false)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row borrow.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let parentPtr := Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
    let childPtr := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    let input := RetagReferencePlace.sliceValue cfg.access.runtime.base parentPtr len reference
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base childPtr len reference
    ∃ after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      cfg.validity.retagPointer () input reference.ty (Storage.withCurrent frames frame machine) =
        .ok (some output) (Storage.withCurrent frames frame after) ∧
      after.user = machine.user ∧
      ∃ newTracker, after.borrowTracker = some newTracker ∧ newTracker.retagMode = .Default ∧
        newTracker.global.protectedTags = borrow.global.protectedTags ∧
        ReadGrant after entry id tag root offset len borrow.global.protectedTags ∧
        after = {machine with memory := after.memory, borrowTracker := after.borrowTracker} := by
  intro cfg parentPtr childPtr input output
  let initial := Storage.withCurrent frames frame machine
  have roomForTag : borrow.global.nextPointerTag.value ≠ 18446744073709551615 := by
    intro impossible
    rw [impossible] at fresh
    simp at fresh
  obtain ⟨nextGlobal, allocation⟩ := MutableTypedRetag.allocate_tag borrow.global roomForTag
  have protections : nextGlobal.protectedTags = borrow.global.protectedTags := by
    unfold GlobalState.newPointerTag at allocation
    split at allocation
    · contradiction
    · have pair := Except.ok.inj allocation
      exact (congrArg (fun data : GlobalState × BorTag => data.1.protectedTags) pair).symm
  let nextTracker : MachineHooks.BorrowState := {borrow with global := nextGlobal}
  let allocatedState : RootState := {initial with machine := {initial.machine with borrowTracker := some nextTracker}}
  let info : RetagPipeline.ResolvedLocation := ⟨id, Size.ofBytes offset, .concrete parentTag⟩
  have allocated : borrow.global.newPointerTag = .ok (nextGlobal, tag) := by
    rw [tagEq]
    exact allocation
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, table, discr, globals, validity, arithmetic, resolver, ensure, synchronize⟩ := fields.validitySources
  let h := adapted cfg pointers
  have sources : TypedRetagFields.SourceFields h compiler cfg.access cfg.validity.projection
      cfg.validity.vtable pointers () := by
    apply TypedRetagFields.adapted_sources
    · exact fields.retagLog
    · rw [fields.retagPrecise, preciseOff]
    · rw [fields.retagImplicit, implicitOff]
  have callback : cfg.validity.retagPointer () = TypedRetag.machineRetagPtrValue h options.limits.retag := by
    dsimp only [h, cfg, adapted]
    rw [validity]
    rfl
  let place := RetagReferencePlace.slicePlace parentPtr len ProjectionMetadataFacts.sliceLayout
  have width : pointers.arithmetic = ⟨Size.ofBytes 8⟩ := by
    rw [arithmetic]
    rfl
  have signedFits : len.toNat < 9223372036854775808 := by
    exact Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp bounded) (by decide)
  have checked : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) allocatedState = .ok () allocatedState := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_access_cached pointers cfg.access allocatedState id parentTag
      base offset len entry resolver width cached live positive signedFits memoryBounds
  have resolved : h.resolveAllocation place.mplace.ptr allocatedState = .ok (some info) allocatedState := by
    rw [sources.resolve]
    exact RetagPointerChecks.resolve_allocation_cached pointers allocatedState id parentTag base offset width cached
  have log : h.logCreation place (Size.ofBytes len) RootSharedRef.policy tag (some info) allocatedState = .ok () allocatedState := by
    rw [sources.log]
    rfl
  have enteredLive : allocatedState.machine.memory.live[id]? = some entry := live
  have ensuredStock : GlobalAllocationMachine.ensure MiriMemoryKind.global globals id allocatedState =
      .ok () allocatedState :=
    RetagPointerChecks.ensure_tree_live MiriMemoryKind.global globals synchronize allocatedState id entry enteredLive
  have ensureHeap : h.ensureTreeExtra id allocatedState = .ok () allocatedState := by
    rw [sources.ensure, ensure]
    exact ensuredStock
  have freeze : h.typeIsFreeze place.layout.ty = pure true := by
    rw [show place.layout.ty = 2 from ProjectionMetadataFacts.slice_layout_shape.1]
    with_unfolding_all rfl
  have nonempty : len ≠ 0 := by
    intro empty
    rw [empty] at positive
    simp at positive
  have enteredRights : OwnedOn (fun row => LocationRights entry.allocation.extra row
      nextTracker.global.protectedTags parent) offset (offset+len) entry.allocation.extra.locations := by
    simpa only [nextTracker, protections] using owners
  have reborrowed := typed_shared_reborrow h options.limits.retag place (Size.ofBytes len) tag parentTag
    parent root info allocatedState allocatedState allocatedState allocatedState entry nextTracker checked resolved log rfl rfl live allocationMut
    sources.precise freeze nonempty ensureHeap raceOff coherent parentNode parentStored roots parentFound
    depth rank tagFresh room aligned reuse clean bounds enteredRights
  let read := entry.allocation.extra.performBorrowAccessRange info.parentProvenance info.baseOffset
    (Size.ofBytes len) .Read nextTracker.global.protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild info.baseOffset info.parentProvenance tag
    (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen false
  let afterState := MutableTypedRetag.withTree (MutableTypedRetag.withTree allocatedState id entry read.tree)
    id {entry with allocation := entry.allocation.setExtra read.tree} child.tree
  let after := afterState.machine
  have scopedExact : afterState = Storage.withCurrent frames frame after := rfl
  have inner : TypedRetag.reborrow h options.limits.retag place (Size.ofBytes len) RootSharedRef.policy tag allocatedState =
      .ok (some (.concrete id tag)) (Storage.withCurrent frames frame after) :=
    reborrowed.1.trans (congrArg (fun state => EStateM.Result.ok (some (Provenance.concrete id tag)) state) scopedExact)
  have whole := completedPointer options remaining span fuel fuelEq pointers reference referenceTy
    id parentTag tag (base+offset) len bounded initial (Storage.withCurrent frames frame after)
    borrow nextGlobal tracked mode allocated cmp metadata noAlias inner
  have afterLive : after.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra child.tree} := by
    have exactLookup := MutableTypedRetag.withTree_live
      (MutableTypedRetag.withTree allocatedState id entry read.tree)
      id {entry with allocation := entry.allocation.setExtra read.tree} child.tree
    exact exactLookup
  have readable : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row
      borrow.global.protectedTags parent .Read) offset (offset+len) entry.allocation.extra.locations := by
    intro position valid overlap starts ends
    exact LocationRights.readRights (owners position valid overlap starts ends)
  have split := uniform_partition (Size.ofBytes offset) (Size.ofBytes len) _ bounds
  obtain ⟨_, _, sizeEq, rooted, sameRoots, childIndex, key, node, preserves⟩ :=
    concrete_shared_readable_reborrow entry.allocation.extra borrow.global.protectedTags parentTag tag
      parent root (Size.ofBytes offset) (Size.ofBytes len) (DedupRangeMap.new (Size.ofBytes len) sharedState) false
      coherent parentNode parentStored roots parentFound depth rank tagFresh room aligned reuse clean
      (fun segment member => (split segment member).1)
      (fun segment member => (split segment member).2) bounds readable
  let normal := entry.allocation.extra.performNormalAccessRange parentTag (Size.ofBytes offset) (Size.ofBytes len)
    .Read borrow.global.protectedTags .VisitChildrenOfAccessed
  let expected := normal.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen false
  have exactTree : child = expected := by
    simp only [child, read, info, nextTracker, protections, expected, normal, BorrowTree.performNormalAccessRange]
  refine ⟨after, by rw [callback]; exact whole, rfl, nextTracker, rfl, mode, protections, ?_, rfl⟩
  refine ⟨expected.tree, childIndex, ?_, rooted, sameRoots, sizeEq, key, ?_, preserves⟩
  · rwa [exactTree] at afterLive
  · obtain ⟨found, live, value, _, perm⟩ := node
    exact ⟨found, live, value, perm⟩

theorem runWithRights
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (reference : LocalLayout) (referenceTy : reference.ty = 7)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (borrow : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some borrow) (mode : borrow.retagMode = .Default)
    (fresh : borrow.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (tagEq : tag = borrow.global.nextPointerTag)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 2) = false)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row borrow.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let parentPtr := Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
    let childPtr := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    let input := RetagReferencePlace.sliceValue cfg.access.runtime.base parentPtr len reference
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base childPtr len reference
    ∃ after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      cfg.validity.retagPointer () input reference.ty (Storage.withCurrent frames frame machine) =
        .ok (some output) (Storage.withCurrent frames frame after) ∧
      after.user = machine.user ∧
      ∃ newTracker, after.borrowTracker = some newTracker ∧ newTracker.retagMode = .Default ∧
        newTracker.global.protectedTags = borrow.global.protectedTags ∧
        ReadGrant after entry id tag root offset len borrow.global.protectedTags := by
  intro cfg parentPtr childPtr input output
  obtain ⟨after, executed, preserved, newTracker, installed, modeAfter, protections, grant, _⟩ :=
    runDetailed options remaining span fuel fuelEq preciseOff implicitOff frames frame machine
      reference referenceTy id parentTag parent root base offset len entry borrow tracked mode fresh tag tagEq cached live
      allocationMut raceOff positive bounded memoryBounds cmp metadata noAlias coherent parentNode parentStored roots
      parentFound depth rank tagFresh room aligned reuse clean bounds owners
  exact ⟨after, executed, preserved, newTracker, installed, modeAfter, protections, grant⟩


theorem run
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (reference : LocalLayout) (referenceTy : reference.ty = 7)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (borrow : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some borrow) (mode : borrow.retagMode = .Default)
    (fresh : borrow.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (tagEq : tag = borrow.global.nextPointerTag)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (raceOff : machine.dataRace = none)
    (positive : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 2) = false)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes) (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row borrow.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let parentPtr := Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
    let childPtr := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    let input := RetagReferencePlace.sliceValue cfg.access.runtime.base parentPtr len reference
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base childPtr len reference
    ∃ after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      cfg.validity.retagPointer () input reference.ty (Storage.withCurrent frames frame machine) =
        .ok (some output) (Storage.withCurrent frames frame after) ∧
      after.user = machine.user ∧
      ∃ newTracker, after.borrowTracker = some newTracker ∧ newTracker.retagMode = .Default := by
  intro cfg parentPtr childPtr input output
  obtain ⟨after, executed, preserved, newTracker, installed, modeAfter, _, _⟩ :=
    runWithRights options remaining span fuel fuelEq preciseOff implicitOff frames frame machine
      reference referenceTy id parentTag parent root base offset len entry borrow tracked mode fresh tag tagEq cached live
      allocationMut raceOff positive bounded memoryBounds cmp metadata noAlias coherent parentNode parentStored roots
      parentFound depth rank tagFresh room aligned reuse clean bounds owners
  exact ⟨after, executed, preserved, newTracker, installed, modeAfter⟩

end DuplicatePrefix.CurrentSharedRetag

#print axioms DuplicatePrefix.CurrentSharedRetag.completedPointer
#print axioms DuplicatePrefix.CurrentSharedRetag.runDetailed
#print axioms DuplicatePrefix.CurrentSharedRetag.runWithRights
#print axioms DuplicatePrefix.CurrentSharedRetag.run

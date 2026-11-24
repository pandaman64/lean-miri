import duplicate_prefix.CurrentSharedRetag
import duplicate_prefix.ProtectedSharedReborrow
import duplicate_prefix.HelperCompilerFacts

namespace DuplicatePrefix.CurrentLenFnEntry
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts CurrentSharedRetag ArchiveForestProjection
open Miri.DataStructures Miri.TreeBorrows.Tree Miri.Verification SourceDomain GeneralRangeMapOrigins RetagSharedChild

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem completedPointer
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (pointers : RootPointers) (reference : LocalLayout) (referenceTy : reference.ty = 7)
    (id : AllocId) (oldTag tag : BorTag) (address length : UInt64)
    (bounded : length ≤ 9223372036854775807)
    (before after : RootState) (borrow : MachineHooks.BorrowState)
    (global : GlobalState) (tracker : before.machine.borrowTracker = some borrow)
    (mode : borrow.retagMode = .FnEntry)
    (implicitOff : options.retag.implicitWrites = false)
    (frame : CompilerFrameContext.ActualFrame)
    (current : before.stack.currentFrame? = some frame)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee)
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
    TypedRetag.reborrow h options.limits.retag place (Size.ofBytes length) protectedShared tag
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
    (Size.ofBytes length) Align.ONE protectedShared before before after borrow global tag
    (.concrete id oldTag) (.concrete id tag) sizing tracker fresh rfl reborrowed
  have implicitWrites : h.implicitWrites before = .ok false before := by
    change cfg.retag.implicitWrites before = _
    rw [configFields.retagImplicit, implicitOff]
    rfl
  have definition : h.instanceDefinition frame.functionInstance before = .ok 1 before := by
    change cfg.retag.instanceDefinition frame.functionInstance before = _
    obtain ⟨_, _, _, _, source, _⟩ := configFields.retagConstruction
    dsimp only [cfg]
    rw [source, callee]
    with_unfolding_all rfl
  have unpin : h.isUnpin 2 before = .ok true before := by rw [q.unpin]; rfl
  have unsafeUnpin : h.isUnsafeUnpin 2 before = .ok true before := by rw [q.unsafeUnpin]; rfl
  have freeze : h.typeIsFreeze 2 before = .ok true before := by rw [q.freeze]; rfl
  have permission : TypedRetag.newPermission h 2 .Shared .FnEntry before =
      .ok (some protectedShared) before := by
    simp [TypedRetag.newPermission, unpin, unsafeUnpin, freeze, implicitWrites, MachineHooks.currentFrame,
      current, definition, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rfl
  have shaped : h.typeShape reference.ty before = .ok RetagPipeline.RetagTypeShape.reference before := by
    rw [referenceTy]
    with_unfolding_all rfl
  have queried : h.referencePointee reference.ty before = .ok (2, .Not) before := by
    rw [referenceTy]
    with_unfolding_all rfl
  have reassemble : h.reconstruct input
      (Miri.Verification.MutableTypedRetag.taggedPlace place (.concrete id tag)) after = .ok result after := rfl
  simp [TypedRetag.machineRetagPtrValue, TypedRetag.retagPtrValue, RetagPipeline.RetagTypeShape.reference,
    RetagPipeline.RetagTypeShape.classify, tracker, mode, shaped, queried, permission,
    constructed, styled, reassemble, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- The actual shared receiver tree and its surviving attachment facts. -/
def FrameGrant (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    {originalMemory : MemoryState Provenance BorrowTree MiriMemoryKind}
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (parentTag tag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (protectors : ProtectedTags) : Prop :=
  let read := entry.allocation.extra.performNormalAccessRange parentTag (Size.ofBytes offset)
    (Size.ofBytes len) .Read protectors .VisitChildrenOfAccessed
  let inside := DedupRangeMap.new (Size.ofBytes len) sharedState
  let result := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag inside .Frozen true
  let installed := {entry with allocation := entry.allocation.setExtra result.tree}
  ∃ index, machine.memory.live[id]? = some installed ∧
    result.tree.indexOfTag tag = some index ∧
    SharedChildFrame entry.allocation.extra read.tree result.tree parent index tag (Size.ofBytes offset)
      (Size.ofBytes len) inside ∧
    machine.borrowTracker.map (fun tracker => tracker.global.nextPointerTag.value) = some (tag.value + 1) ∧
    machine.memory = {originalMemory with live := originalMemory.live.insert id installed}

private theorem uniform_slot (offset length capacity : Size)
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

private theorem successor_value (tag next : BorTag) (chosen : BorTag.succ tag = some next) :
    next.value = tag.value + 1 := by
  unfold BorTag.succ BorTag.ofUInt64 at chosen
  split at chosen
  · contradiction
  · split at chosen
    · contradiction
    · exact (congrArg BorTag.value (Option.some.inj chosen)).symm

set_option maxHeartbeats 1200000 in
theorem runWithFrame
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ledger : FrameState) (frameLedger : frame.extra.borrowTracker = some ledger)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee)
    (reference : LocalLayout) (referenceTy : reference.ty = 7)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (borrow : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some borrow) (mode : borrow.retagMode = .FnEntry)
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
    (freshNode : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ tag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row borrow.global.protectedTags parent .Read)
      offset (offset+len) entry.allocation.extra.locations) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let parentPtr := Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
    let childPtr := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    let input := RetagReferencePlace.sliceValue cfg.access.runtime.base parentPtr len reference
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base childPtr len reference
    let tagged := {frame with extra := {frame.extra with borrowTracker := some (ledger.addProtector id tag)}}
    ∃ after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      cfg.validity.retagPointer () input reference.ty (Storage.withCurrent frames frame machine) =
        .ok (some output) (Storage.withCurrent frames tagged after) ∧
      after.user = machine.user ∧
      ∃ newTracker, after.borrowTracker = some newTracker ∧ newTracker.retagMode = .FnEntry ∧
        newTracker.global.protectedTags = borrow.global.protectedTags.insert tag .StrongProtector ∧
        ReadGrant after entry id tag root offset len newTracker.global.protectedTags ∧
        after = {machine with memory := after.memory, borrowTracker := after.borrowTracker} ∧
        FrameGrant after (originalMemory := machine.memory) entry id parentTag tag parent offset len newTracker.global.protectedTags := by
  intro cfg parentPtr childPtr input output tagged
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
  have counter : nextGlobal.nextPointerTag.value = borrow.global.nextPointerTag.value + 1 := by
    have step := allocation
    cases selected : BorTag.succ borrow.global.nextPointerTag with
    | none => simp only [GlobalState.newPointerTag, selected, reduceCtorEq] at step
    | some next =>
      simp only [GlobalState.newPointerTag, selected] at step
      have actual := congrArg (fun data : GlobalState × BorTag => data.1.nextPointerTag.value) (Except.ok.inj step)
      exact actual.symm.trans (successor_value borrow.global.nextPointerTag next selected)
  let nextTracker : MachineHooks.BorrowState := {borrow with global := nextGlobal}
  let allocatedState : RootState := {initial with machine := {initial.machine with borrowTracker := some nextTracker}}
  let info : RetagPipeline.ResolvedLocation := ⟨id, Size.ofBytes offset, .concrete parentTag⟩
  have current : allocatedState.stack.currentFrame? = some frame := by
    simp [allocatedState, initial, Storage.withCurrent, Stack.currentFrame?]
  let entered := MutableTypedRetag.withStrongProtector allocatedState info tag frame ledger nextTracker
  let active := MutableTypedRetag.registeredTracker nextTracker tag
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
  have log : h.logCreation place (Size.ofBytes len) protectedShared tag (some info) allocatedState = .ok () allocatedState := by
    rw [sources.log]
    rfl
  have enteredLive : entered.machine.memory.live[id]? = some entry := live
  have ensuredStock : GlobalAllocationMachine.ensure MiriMemoryKind.global globals id entered =
      .ok () entered :=
    RetagPointerChecks.ensure_tree_live MiriMemoryKind.global globals synchronize entered id entry enteredLive
  have ensureHeap : h.ensureTreeExtra id entered = .ok () entered := by
    rw [sources.ensure, ensure]
    exact ensuredStock
  have freeze : h.typeIsFreeze place.layout.ty = pure true := by
    rw [show place.layout.ty = 2 from ProjectionMetadataFacts.slice_layout_shape.1]
    with_unfolding_all rfl
  have nonempty : len ≠ 0 := by
    intro empty
    rw [empty] at positive
    simp at positive
  have enteredRights : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row
      nextTracker.global.protectedTags parent .Read) offset (offset+len) entry.allocation.extra.locations := by
    simpa only [nextTracker, protections] using owners
  have reborrowed := typed_shared_fn_entry h options.limits.retag place (Size.ofBytes len) tag parentTag
    parent root info allocatedState allocatedState allocatedState allocatedState frame ledger current frameLedger
    entry nextTracker checked resolved log rfl rfl live allocationMut sources.precise freeze nonempty ensureHeap
    raceOff coherent parentNode parentStored roots parentFound depth rank tagFresh freshNode room aligned reuse
    clean bounds enteredRights
  let read := entry.allocation.extra.performBorrowAccessRange info.parentProvenance info.baseOffset
    (Size.ofBytes len) .Read active.global.protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild info.baseOffset info.parentProvenance tag
    (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen true
  let afterState := MutableTypedRetag.withTree (MutableTypedRetag.withTree entered id entry read.tree)
    id {entry with allocation := entry.allocation.setExtra read.tree} child.tree
  let after := afterState.machine
  have scopedExact : afterState = Storage.withCurrent frames tagged after := by
    have stack : afterState.stack = (Storage.withCurrent frames tagged after).stack := by
      simp [afterState, MutableTypedRetag.withTree, entered, MutableTypedRetag.withStrongProtector,
        allocatedState, initial, Storage.withCurrent, GlobalState.addProtector, tagged, info]
    exact congrArg (fun stack => ({ stack, machine := after } : RootState)) stack
  have inner : TypedRetag.reborrow h options.limits.retag place (Size.ofBytes len) protectedShared tag allocatedState =
      .ok (some (.concrete id tag)) (Storage.withCurrent frames tagged after) :=
    reborrowed.1.trans (congrArg (fun state => EStateM.Result.ok (some (Provenance.concrete id tag)) state) scopedExact)
  have whole := completedPointer options remaining span fuel fuelEq pointers reference referenceTy
    id parentTag tag (base+offset) len bounded initial (Storage.withCurrent frames tagged after)
    borrow nextGlobal tracked mode implicitOff frame
    (by simp [initial, Storage.withCurrent, Stack.currentFrame?]) callee allocated cmp metadata noAlias inner
  have afterLive : after.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra child.tree} := by
    have exactLookup := MutableTypedRetag.withTree_live
      (MutableTypedRetag.withTree entered id entry read.tree)
      id {entry with allocation := entry.allocation.setExtra read.tree} child.tree
    exact exactLookup
  obtain ⟨sizeEq, good, sameRoots, selected, found, node, owned⟩ := reborrowed.2
  have trackerAfter : after.borrowTracker = some active := rfl
  have newProtections : active.global.protectedTags =
      borrow.global.protectedTags.insert tag .StrongProtector := by
    simp only [active, MutableTypedRetag.registeredTracker, nextTracker, protections]
  refine ⟨after, by rw [callback]; exact whole, rfl, active, trackerAfter, mode, newProtections, ?_, rfl, ?_⟩
  · refine ⟨child.tree, selected, afterLive, good, sameRoots, sizeEq, found, ?_, owned⟩
    obtain ⟨fresh, present, tagged, _, frozen⟩ := node
    exact ⟨fresh, present, tagged, frozen⟩
  · have allowed : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row
        active.global.protectedTags parent .Read) offset (offset+len) entry.allocation.extra.locations := by
      intro position valid linear first last index node present
      obtain ⟨state, lookup, self, foreign⟩ := owners position valid linear first last index node present
      have unchanged : active.global.protectedTags.contains node.tag = borrow.global.protectedTags.contains node.tag := by
        rw [newProtections]
        exact Miri.Verification.MutableReferenceRights.contains_insert_other _ _ _ _ (freshNode index node present)
      exact ⟨state, lookup, by rw [unchanged]; exact self, by rw [unchanged]; exact foreign⟩
    have each := uniform_slot (Size.ofBytes offset) (Size.ofBytes len) _ bounds
    obtain ⟨_, _, _, _, _, index, lookup, _, framed, _⟩ :=
      concrete_shared_readable_reborrow_with_frame entry.allocation.extra active.global.protectedTags parentTag tag
        parent root (Size.ofBytes offset) (Size.ofBytes len) (DedupRangeMap.new (Size.ofBytes len) sharedState) true
        coherent parentNode parentStored roots parentFound depth rank tagFresh room aligned reuse clean
        (fun segment member => (each segment member).1)
        (fun segment member => (each segment member).2) bounds allowed
    refine ⟨index, afterLive, lookup, framed, ?_, ?_⟩
    · rw [trackerAfter, tagEq]
      exact congrArg some counter
    · exact MemoryCopyBridge.live_update_twice machine.memory id
        {entry with allocation := entry.allocation.setExtra read.tree}
        {entry with allocation := entry.allocation.setExtra child.tree}

theorem run
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ledger : FrameState) (frameLedger : frame.extra.borrowTracker = some ledger)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee)
    (reference : LocalLayout) (referenceTy : reference.ty = 7)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (borrow : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some borrow) (mode : borrow.retagMode = .FnEntry)
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
    (freshNode : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ tag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationAccessRights entry.allocation.extra row borrow.global.protectedTags parent .Read)
      offset (offset+len) entry.allocation.extra.locations) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let parentPtr := Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))
    let childPtr := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    let input := RetagReferencePlace.sliceValue cfg.access.runtime.base parentPtr len reference
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base childPtr len reference
    let tagged := {frame with extra := {frame.extra with borrowTracker := some (ledger.addProtector id tag)}}
    ∃ after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      cfg.validity.retagPointer () input reference.ty (Storage.withCurrent frames frame machine) =
        .ok (some output) (Storage.withCurrent frames tagged after) ∧
      after.user = machine.user ∧
      ∃ newTracker, after.borrowTracker = some newTracker ∧ newTracker.retagMode = .FnEntry ∧
        newTracker.global.protectedTags = borrow.global.protectedTags.insert tag .StrongProtector ∧
        ReadGrant after entry id tag root offset len newTracker.global.protectedTags := by
  intro cfg oldPtr newPtr input output tagged
  obtain ⟨after, action, user, next, tracker, modeAfter, protectedAfter, read, _, _⟩ :=
    runWithFrame options remaining span fuel fuelEq preciseOff implicitOff frames frame machine ledger frameLedger
      callee reference referenceTy id parentTag parent root base offset len entry borrow tracked mode fresh tag tagEq
      cached live allocationMut raceOff positive bounded memoryBounds cmp metadata noAlias coherent parentNode
      parentStored roots parentFound depth rank tagFresh freshNode room aligned reuse clean bounds owners
  exact ⟨after, action, user, next, tracker, modeAfter, protectedAfter, read⟩

end DuplicatePrefix.CurrentLenFnEntry

#print axioms DuplicatePrefix.CurrentLenFnEntry.completedPointer
#print axioms DuplicatePrefix.CurrentLenFnEntry.runWithFrame
#print axioms DuplicatePrefix.CurrentLenFnEntry.run

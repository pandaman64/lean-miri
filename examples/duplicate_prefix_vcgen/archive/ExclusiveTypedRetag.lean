import duplicate_prefix.ConcreteFrozenReborrow
import Miri.Verification.MutableTypedRetag
import duplicate_prefix.RetagPointerChecks

namespace DuplicatePrefix.ExclusiveTypedRetag

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.TreeBorrows
open Miri.TreeBorrows.RetagPolicy Miri.Verification Miri.Verification.MutableTypedRetag
open DuplicatePrefix.SourceDomain DuplicatePrefix.MutableSliceRights DuplicatePrefix.PreparedArguments
open DuplicatePrefix.ArchiveForestProjection DuplicatePrefix.RetagFrozenChild GeneralRangeMapOrigins

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "BorrowFrame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- The source frozen mutable policy when implicit FnEntry writes are disabled. -/
def readPolicy : NewPermission :=
  ⟨.ReservedFrz false, .ReservedFrz false, .ReservedFrz false, some .StrongProtector⟩

theorem readPolicy_selected :
    create ⟨true, true, true⟩ .Mutable .FnEntry ⟨false, false⟩ = some readPolicy := rfl

def readState : Tree.LocationState := ⟨.ReservedFrz false, true, .None⟩

private theorem strong_insert_repeat (tags : ProtectedTags) (tag : BorTag) :
    (tags.insert tag .StrongProtector).insert tag .StrongProtector =
      tags.insert tag .StrongProtector := by
  simp [ProtectedTags.insert, Array.filter_filter]

private theorem grants_during_registration (tree : BorrowTree) (tags : ProtectedTags)
    (source : UniIndex) (freshTag : BorTag) (lower upper : UInt64)
    (fresh : ∀ index node, tree.nodeAt index = some node → node.tag ≠ freshTag)
    (owned : OwnedOn (fun location => LocationRights tree location tags source) lower upper tree.locations) :
    OwnedOn (fun location => LocationRights tree location (tags.insert freshTag .StrongProtector) source)
      lower upper tree.locations := by
  intro position valid positive start stop index node found
  have same := MutableReferenceRights.contains_insert_other tags freshTag node.tag .StrongProtector
    (fresh index node found)
  obtain ⟨state, current, localRight, foreignRight⟩ := owned position valid positive start stop index node found
  exact ⟨state, current, (by simpa only [same] using localRight),
    (by simpa only [same] using foreignRight)⟩

/-- Discharge the actual pointer leaves from the allocation and address
cache metadata of a live initialized slice on the pinned 64-bit target. -/
theorem cached_pointer_inputs {K U : Type} [DecidableEq K]
    (hooks : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (before : ValidityMachine.State K U)
    (place : MPlaceTy Provenance) (length base : UInt64) (tag : BorTag)
    (storage : InitializedRegion before length)
    (checkSource : hooks.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveSource : hooks.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) =
      some ⟨storage.id, base⟩)
    (address : place.mplace.ptr = Pointer.new (some (.concrete storage.id tag))
      (Size.ofBytes (base + storage.relativeStart.bytes)))
    (positive : (0 : UInt64) < length) (addressable : length.toNat < 2 ^ 63) :
    hooks.checkPtrAccess place.mplace.ptr (Size.ofBytes length) before = .ok () before ∧
      hooks.resolveAllocation place.mplace.ptr before =
        .ok (some ⟨storage.id, storage.relativeStart, .concrete tag⟩) before := by
  constructor
  · rw [checkSource, address]
    exact RetagPointerChecks.check_pointer_access_cached pointers access before storage.id tag base
      storage.relativeStart.bytes length storage.entry wiring width cached storage.live positive addressable storage.fits
  · rw [resolveSource, address]
    exact RetagPointerChecks.resolve_allocation_cached pointers before storage.id tag base
      storage.relativeStart.bytes width cached

/-- Package the actual live write-back and the child's per-byte grant as
the source-domain resource consumed by a subsequent helper. Allocation bytes,
address-relative extent and initialization are the original physical witnesses. -/
theorem region_from_cached_reborrow (before after : State) (length : UInt64)
    (storage : InitializedRegion before length)
    (tree : BorrowTree) (tag : BorTag) (source : UniIndex) (tracker : MachineHooks.BorrowState)
    (live : after.machine.memory.live[storage.id]? =
      some {storage.entry with allocation := storage.entry.allocation.setExtra tree})
    (tracked : after.machine.borrowTracker = some tracker)
    (coherent : CoherentForest tree)
    (known : tree.indexOfTag tag = some source)
    (present : ∃ node, tree.nodeAt source = some node ∧ node.tag = tag)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : ∀ point : UInt64, storage.relativeStart.bytes.toNat ≤ point.toNat →
      point.toNat < (storage.relativeStart.bytes + length).toNat →
      ∀ row, ValueAt tree.locations point row → OwnsByte tree row tracker.global.protectedTags source) :
    ∃ next : InitializedRegion after length,
      next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
      next.entry = {storage.entry with allocation := storage.entry.allocation.setExtra tree} ∧
      Nonempty (ExclusiveRegion after length next tag) := by
  let next : InitializedRegion after length := {
    id := storage.id
    relativeStart := storage.relativeStart
    entry := {storage.entry with allocation := storage.entry.allocation.setExtra tree}
    live
    writable := storage.writable
    backed := storage.backed
    fits := storage.fits
    initialized := storage.initialized }
  let region : ExclusiveRegion after length next tag := {
    tracker, tracked, coherent, source, tagKnown := known, sourcePresent := present
    covers := by
      intro distance positive
      let address := storage.relativeStart.bytes.toNat + distance
      have fit : address < tree.locations.size.bytes.toNat := by dsimp [address]; omega
      have in64 : address < 2 ^ 64 := Nat.lt_trans fit tree.locations.size.bytes.toNat_lt
      let point := UInt64.ofNat address
      have exactPoint : point.toNat = address := by
        simp [point, Nat.mod_eq_of_lt in64]
      have inside : point.toNat < tree.locations.size.bytes.toNat := exactPoint ▸ fit
      obtain ⟨position, bounded, start, stop⟩ :=
        GeneralRangeMapGeometry.covered tree.locations coherent.ranges point inside
      exact ⟨tree.locations.entries[position], Array.mem_iff_getElem.mpr ⟨position, bounded, rfl⟩,
        by simpa only [exactPoint] using start, by simpa only [exactPoint] using stop⟩
    exclusive := by
      intro distance positive segment member start stop index node found
      let address := storage.relativeStart.bytes.toNat + distance
      have fit : address < tree.locations.size.bytes.toNat := by dsimp [address]; omega
      have in64 : address < 2 ^ 64 := Nat.lt_trans fit tree.locations.size.bytes.toNat_lt
      have endFits : storage.relativeStart.bytes.toNat + length.toNat < 2 ^ 64 :=
        Nat.lt_of_le_of_lt extent tree.locations.size.bytes.toNat_lt
      have endNat : (storage.relativeStart.bytes + length).toNat =
          storage.relativeStart.bytes.toNat + length.toNat := by
        simp [UInt64.toNat_add, Nat.mod_eq_of_lt endFits]
      let point := UInt64.ofNat address
      have exactPoint : point.toNat = address := by
        simp [point, Nat.mod_eq_of_lt in64]
      obtain ⟨position, bounded, same⟩ := Array.mem_iff_getElem.mp member
      have actualSame : tree.locations.entries[position]'bounded = segment := same
      have row : ValueAt tree.locations point segment.data := by
        refine ⟨position, bounded, ?_, ?_, congrArg RangeMapSegment.data actualSame⟩
        · rw [actualSame, exactPoint]
          exact start
        · rw [actualSame, exactPoint]
          exact stop
      have lower : storage.relativeStart.bytes.toNat ≤ point.toNat := by rw [exactPoint]; dsimp [address]; omega
      have upper : point.toNat < (storage.relativeStart.bytes + length).toNat := by
        rw [exactPoint, endNat]
        dsimp [address]
        omega
      obtain ⟨state, lookup, localRight, foreignRight⟩ := owned point lower upper segment.data row index node found
      exact ⟨state, lookup, fun path => (localOwns_iff _ _).mpr (localRight path),
        fun path => (foreignCompatible_iff _ _).mpr (foreignRight path)⟩ }
  exact ⟨next, rfl, rfl, rfl, ⟨region⟩⟩

/-- The live typed mutable reborrow in the read-associated frozen profile
hands the actual new tag's exclusive rights to its caller. The argument
extent, live cache entry, compiler/pointer leaves, tag allocator and initial
byte ownership are input facts. The associated tree read and child
constructor are discharged here from the same initial ownership. -/
theorem reborrow_exclusive_region [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (tag parentTag : BorTag)
    (location : RetagPipeline.ResolvedLocation) (before pointed resolved logged : State)
    (frame : BorrowFrame) (frameLedger : FrameState) (borrow : MachineHooks.BorrowState)
    (entry : LocalAllocation Provenance BorrowTree K) (parent root : UniIndex)
    (parentNode : TreeNode)
    (check : hooks.checkPtrAccess place.mplace.ptr size before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place size readPolicy tag (some location) resolved = .ok () logged)
    (parentProvenance : location.parentProvenance = .concrete parentTag)
    (current : logged.stack.currentFrame? = some frame)
    (ledger : frame.extra.borrowTracker = some frameLedger)
    (tracked : logged.machine.borrowTracker = some borrow)
    (live : logged.machine.memory.live[location.allocId]? = some entry)
    (mutable : entry.allocation.mutability = .Mut)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (nonempty : size.bytes ≠ 0)
    (ensure : let registered := withStrongProtector logged location tag frame frameLedger borrow
      hooks.ensureTreeExtra location.allocId registered = .ok () registered)
    (raceOff : logged.machine.dataRace = none)
    (coherent : CoherentForest entry.allocation.extra)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root])
    (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes)
    (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (fresh : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ tag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none →
      entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none →
      entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : location.baseOffset.bytes.toNat + size.bytes.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationRights entry.allocation.extra location
      borrow.global.protectedTags parent) location.baseOffset.bytes (location.baseOffset.bytes + size.bytes)
      entry.allocation.extra.locations) :
    ∃ (after : State) (tree : BorrowTree) (child : UniIndex),
      TypedRetag.reborrow hooks budget place size readPolicy tag before =
        .ok (some (.concrete location.allocId tag)) after ∧
      after.machine.memory.live[location.allocId]? =
        some {entry with allocation := entry.allocation.setExtra tree} ∧
      after.machine.borrowTracker = some (registeredTracker borrow tag) ∧
      after.stack.currentFrame? =
        some {frame with extra := {frame.extra with borrowTracker := some (frameLedger.addProtector location.allocId tag)}} ∧
      tree.locations.size = entry.allocation.extra.locations.size ∧ CoherentForest tree ∧
      tree.roots = #[root] ∧ tree.indexOfTag tag = some child ∧
      (∃ node, tree.nodeAt child = some node ∧ node.tag = tag) ∧
      (∀ point : UInt64, location.baseOffset.bytes.toNat ≤ point.toNat →
        point.toNat < (location.baseOffset.bytes + size.bytes).toNat →
        ∀ row, ValueAt tree.locations point row →
          OwnsByte tree row (registeredTracker borrow tag).global.protectedTags child) ∧
      (∀ storage : InitializedRegion logged size.bytes,
        storage.id = location.allocId → storage.relativeStart = location.baseOffset → storage.entry = entry →
        ∃ next : InitializedRegion after size.bytes,
          next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
          next.entry = {storage.entry with allocation := storage.entry.allocation.setExtra tree} ∧
          Nonempty (ExclusiveRegion after size.bytes next tag)) := by
  let tree := entry.allocation.extra
  let inside := DedupRangeMap.new size readState
  let active := registeredTracker borrow tag
  let tags := active.global.protectedTags
  let registered := withStrongProtector logged location tag frame frameLedger borrow
  let read := tree.performNormalAccessRange parentTag location.baseOffset size .Read tags
    .VisitChildrenOfAccessed
  let raced := withTree registered location.allocId entry read.tree
  let child := read.tree.newChild location.baseOffset (.concrete parentTag) tag inside (.ReservedFrz false) true
  let updated := {entry with allocation := entry.allocation.setExtra read.tree}
  let after := withTree raced location.allocId updated child.tree
  have rights := grants_during_registration tree borrow.global.protectedTags parent tag
    location.baseOffset.bytes (location.baseOffset.bytes + size.bytes) fresh owners
  have laws := uniform_segments location.baseOffset size tree.locations.size readState bounds (.inl rfl)
  obtain ⟨readOk, childOk, capacity, childCoherent, childRoots, index, key, node, owned⟩ :=
    coherent_frozen_reborrow_with_mode tree tags parentTag tag parent root location.baseOffset size inside true
      coherent parentNode parentStored roots parentFound depth rank tagFresh fresh room aligned reuse clean
      (fun segment mem => (laws segment mem).1) (fun segment mem => (laws segment mem).2) bounds rights
  have parentAccess : (tree.performBorrowAccessRange location.parentProvenance location.baseOffset size .Read tags
      .VisitChildrenOfAccessed).status = .Completed := by
    rw [parentProvenance]
    exact readOk
  have checkedChild : ((tree.performBorrowAccessRange location.parentProvenance
      location.baseOffset size .Read tags .VisitChildrenOfAccessed).tree.newChild
        location.baseOffset location.parentProvenance tag inside readPolicy.outsidePermission
        readPolicy.protector.isSome).outcome = .ok () := by
    rw [parentProvenance]
    exact childOk
  have race : retagRace location.allocId .Read location.baseOffset size raced = .ok () raced :=
    retagRace_disabled location.allocId .Read location.baseOffset size raced raceOff
  have raceForOperation : retagRace location.allocId .Read location.baseOffset size
      (withTree registered location.allocId entry
        (tree.performBorrowAccessRange location.parentProvenance location.baseOffset size .Read tags
          .VisitChildrenOfAccessed).tree) = .ok () raced := by
    rw [parentProvenance]
    exact race
  have execution := uniform_live_reborrow hooks budget place size readPolicy tag location
    before pointed resolved logged raced frame frameLedger borrow readState entry .Read check resolve log
    rfl current ledger tracked live mutable imprecise freeze rfl rfl nonempty ensure
    parentAccess raceForOperation checkedChild
  have actual : TypedRetag.reborrow hooks budget place size readPolicy tag before =
      .ok (some (.concrete location.allocId tag)) after := by
    simpa only [parentProvenance, after, updated, child, read, tree, tags, active, inside,
      BorrowTree.performNormalAccessRange, readPolicy, Option.isSome_some] using execution
  have selectedLive : after.machine.memory.live[location.allocId]? =
      some {entry with allocation := entry.allocation.setExtra child.tree} :=
    withTree_live raced location.allocId updated child.tree
  have byteGrant : ∀ point : UInt64, location.baseOffset.bytes.toNat ≤ point.toNat →
      point.toNat < (location.baseOffset.bytes + size.bytes).toNat →
      ∀ row, ValueAt child.tree.locations point row →
        OwnsByte child.tree row (registeredTracker borrow tag).global.protectedTags index := by
    intro point lo hi row member
    have next := owned point lo hi row member
    have same : tags.insert tag .StrongProtector = tags :=
      strong_insert_repeat borrow.global.protectedTags tag
    simpa only [childProtections, Bool.true_eq, ↓reduceIte, same] using next
  refine ⟨after, child.tree, index, actual, selectedLive, rfl, ?_, capacity, childCoherent,
    childRoots, key, node, byteGrant, ?_⟩
  · simp [after, raced, registered, withTree, withStrongProtector, GlobalState.addProtector, Stack.currentFrame?]
  · intro storage sameId sameOffset sameEntry
    apply region_from_cached_reborrow logged after size.bytes storage child.tree tag index (registeredTracker borrow tag)
      ?_ rfl childCoherent key node ?_ ?_
    · simpa only [sameId, sameEntry] using selectedLive
    · rw [sameOffset, capacity]
      exact bounds
    · simpa only [sameOffset] using byteGrant

/-- The reborrow's cached byte and permission update, projected from its
coherent returned region. -/
theorem reborrow_exclusive [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (tag parentTag : BorTag)
    (location : RetagPipeline.ResolvedLocation) (before pointed resolved logged : State)
    (frame : BorrowFrame) (frameLedger : FrameState) (borrow : MachineHooks.BorrowState)
    (entry : LocalAllocation Provenance BorrowTree K) (parent root : UniIndex)
    (parentNode : TreeNode)
    (check : hooks.checkPtrAccess place.mplace.ptr size before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place size readPolicy tag (some location) resolved = .ok () logged)
    (parentProvenance : location.parentProvenance = .concrete parentTag)
    (current : logged.stack.currentFrame? = some frame)
    (ledger : frame.extra.borrowTracker = some frameLedger)
    (tracked : logged.machine.borrowTracker = some borrow)
    (live : logged.machine.memory.live[location.allocId]? = some entry)
    (mutable : entry.allocation.mutability = .Mut)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (nonempty : size.bytes ≠ 0)
    (ensure : let registered := withStrongProtector logged location tag frame frameLedger borrow
      hooks.ensureTreeExtra location.allocId registered = .ok () registered)
    (raceOff : logged.machine.dataRace = none)
    (coherent : CoherentForest entry.allocation.extra)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root])
    (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes)
    (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tag = none)
    (fresh : ∀ index node, entry.allocation.extra.nodeAt index = some node → node.tag ≠ tag)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none →
      entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none →
      entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : ∀ index, entry.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
        entry.allocation.extra.locations.entries[position].data.perms.get index = none)
    (bounds : location.baseOffset.bytes.toNat + size.bytes.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun location => LocationRights entry.allocation.extra location
      borrow.global.protectedTags parent) location.baseOffset.bytes (location.baseOffset.bytes + size.bytes)
      entry.allocation.extra.locations) :
    ∃ (after : State) (tree : BorrowTree) (child : UniIndex),
      TypedRetag.reborrow hooks budget place size readPolicy tag before =
        .ok (some (.concrete location.allocId tag)) after ∧
      after.machine.memory.live[location.allocId]? =
        some {entry with allocation := entry.allocation.setExtra tree} ∧
      after.machine.borrowTracker = some (registeredTracker borrow tag) ∧
      after.stack.currentFrame? =
        some {frame with extra := {frame.extra with borrowTracker := some (frameLedger.addProtector location.allocId tag)}} ∧
      tree.locations.size = entry.allocation.extra.locations.size ∧ tree.locations.WellFormed ∧
      tree.indexOfTag tag = some child ∧
      (∃ node, tree.nodeAt child = some node ∧ node.tag = tag) ∧
      ∀ point : UInt64, location.baseOffset.bytes.toNat ≤ point.toNat →
        point.toNat < (location.baseOffset.bytes + size.bytes).toNat →
        ∀ row, ValueAt tree.locations point row →
          OwnsByte tree row (registeredTracker borrow tag).global.protectedTags child := by
  obtain ⟨after, tree, child, executed, cached, borrowAfter, frameAfter, sizeAfter, forest,
      _, found, node, rights, _⟩ :=
    reborrow_exclusive_region hooks budget place size tag parentTag location before pointed resolved logged
      frame frameLedger borrow entry parent root parentNode check resolve log parentProvenance current ledger
      tracked live mutable imprecise freeze nonempty ensure raceOff coherent parentStored roots parentFound
      depth rank tagFresh fresh room aligned reuse clean bounds owners
  exact ⟨after, tree, child, executed, cached, borrowAfter, frameAfter, sizeAfter, forest.ranges,
    found, node, rights⟩

/-- Carry a proved exclusive reborrow through the actual FnEntry pointer
retag. The machine allocates the tag and passes the original address,
layout and metadata to reference reconstruction. -/
theorem machine_entry_of_reborrow [DecidableEq K] (hooks : TypedRetag.Hooks K U) (budget : Nat)
    (value : RvalueImmTy Provenance) (ty pointee : Miri.MIR.TyId)
    (before shapeState pointeeState policyState placeState layoutState : State)
    (place : MPlaceTy Provenance) (size : Size) (alignment : Align)
    (entryBorrow currentBorrow : MachineHooks.BorrowState)
    (id : AllocId) (old : Provenance) (ready : State → Prop)
    (entryTracked : before.machine.borrowTracker = some entryBorrow)
    (mode : entryBorrow.retagMode = .FnEntry)
    (shape : hooks.typeShape ty before = .ok RetagPipeline.RetagTypeShape.reference shapeState)
    (reference : hooks.referencePointee ty shapeState = .ok (pointee, .Mut) pointeeState)
    (policy : TypedRetag.newPermission hooks pointee .Mutable .FnEntry pointeeState =
      .ok (some readPolicy) policyState)
    (position : hooks.immPtrToMPlace value policyState = .ok place placeState)
    (layout : hooks.sizeAndAlign place placeState = .ok (some (size, alignment)) layoutState)
    (tracked : layoutState.machine.borrowTracker = some currentBorrow)
    (room : currentBorrow.global.nextPointerTag.value ≠ 18446744073709551615)
    (parent : place.mplace.ptr.provenance = some old)
    (borrowed : ∀ global,
      currentBorrow.global.newPointerTag = .ok (global, currentBorrow.global.nextPointerTag) →
      let staged := {layoutState with machine := {layoutState.machine with
        borrowTracker := some {currentBorrow with global}}}
      ∃ after, TypedRetag.reborrow hooks budget place size readPolicy currentBorrow.global.nextPointerTag staged =
        .ok (some (.concrete id currentBorrow.global.nextPointerTag)) after ∧ ready after)
    (reconstruct : ∀ after, ready after →
      ∃ output, hooks.reconstruct value (taggedPlace place (.concrete id currentBorrow.global.nextPointerTag))
        after = .ok output after) :
    ∃ output after, TypedRetag.machineRetagPtrValue hooks budget value ty before =
      .ok (some output) after ∧ ready after := by
  obtain ⟨global, tagAllocated⟩ := allocate_tag currentBorrow.global room
  obtain ⟨after, execution, resource⟩ := borrowed global tagAllocated
  obtain ⟨output, rebuilt⟩ := reconstruct after resource
  have retagged := retag_place hooks budget place size alignment readPolicy placeState layoutState after
    currentBorrow global currentBorrow.global.nextPointerTag old
    (.concrete id currentBorrow.global.nextPointerTag) layout tracked tagAllocated parent execution
  refine ⟨output, after, ?_, resource⟩
  exact machine_retag_mutable_pointer hooks budget value output ty pointee before shapeState pointeeState
    policyState placeState after after place (taggedPlace place (.concrete id currentBorrow.global.nextPointerTag))
    entryBorrow readPolicy entryTracked mode shape reference policy position retagged rebuilt

end DuplicatePrefix.ExclusiveTypedRetag

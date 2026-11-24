import duplicate_prefix.EmptySharedTree
import duplicate_prefix.EmptyReferenceAllocation
import duplicate_prefix.TypedRetagPolicyFields
import duplicate_prefix.RetagReferencePlace

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyBackedPointer
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open EmptyReferenceAllocation
theorem retag_place_at_of_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (size : Size) (align : Align)
    (before after : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (original : Provenance)
    (provenance : place.mplace.ptr.provenance = some original)
    (sizing : h.sizeAndAlign place before = .ok (some (size, align)) before)
    (reborrow : TypedRetag.reborrow h budget place size policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok (some (.concrete id tracker.global.nextPointerTag)) after) :
    TypedRetag.retagPlace h budget place policy before =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) after := by
  unfold TypedRetag.retagPlace
  simp only [bind, EStateM.bind]
  rw [sizing]
  simp only [pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [provenance, bind, EStateM.bind, pure, EStateM.pure]
  rfl

theorem unprotected_live_zero_pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base offset : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = none)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live[id]? = some entry)
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩)
    (reference : LocalLayout) (mutability : Miri.MIR.Mutability) (mode : RetagPolicy.RetagMode)
    (created : RetagPolicy.create ⟨true,true,true⟩ (if mutability == .Mut then .Mutable else .Shared)
      mode ⟨false,false⟩ = some policy)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,mutability))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames frame
        {allocatedMachine machine tracker fresh
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  have definitionReady : mode = .FnEntry → ∃ definition, h.instanceDefinition frame.functionInstance = pure definition := by
    intro same
    exact False.elim (TypedRetagPolicyFields.unprotected_not_fn_entry mutability mode policy created protection same)
  subst tag
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames frame
    {allocatedMachine machine tracker fresh
      with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO allocated = .ok () allocated := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr allocated
  have resolve : h.resolveAllocation place.mplace.ptr allocated =
      .ok (some ⟨id,Size.ofBytes offset,.concrete parentTag⟩) allocated := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers allocated id parentTag base offset width cached
  let location : RetagPipeline.ResolvedLocation := ⟨id, Size.ofBytes offset, .concrete parentTag⟩
  have log : h.logCreation place Size.ZERO policy tracker.global.nextPointerTag (some location) allocated = .ok () allocated := by
    rw [sources.log]
    rfl
  have register : Miri.Verification.TypedRetagWP.registerProtector location policy tracker.global.nextPointerTag allocated =
      .ok () allocated := by
    simp [Miri.Verification.TypedRetagWP.registerProtector, protection, pure, EStateM.pure]
  have ensure : h.ensureTreeExtra id allocated = .ok () allocated := by
    rw [sources.ensure,extraWiring]
    exact RetagPointerChecks.ensure_tree_live globalKind globals synchronize allocated id entry present
  have completed := congrArg BorrowTree.ChildInsertResult.outcome child
  have reborrow := EmptySharedTree.reborrow h budget place policy tracker.global.nextPointerTag location
    allocated allocated allocated allocated allocated entry initial check resolve log register present sources.precise
    frozen initialState ensure completed
  have committed : Miri.Verification.MutableTypedRetag.withTree allocated id entry
      (entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
        (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome).tree = after := by
    rw [child]
    rfl
  rw [committed] at reborrow
  have retag := retag_place_at_of_reborrow h budget place policy Size.ZERO Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty
    (if mutability == .Mut then .Mutable else .Shared) mode before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer 0 reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer 0 place.layout := by rw [placeShape]; rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer 0 place.layout
  exact EmptyReferenceSteps.reference_pointer_of_steps h budget value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) place.layout.ty mutability mode policy
    before after shape pointeeQuery permission construct retag reconstruct

#print axioms unprotected_live_zero_pointer
def registeredGlobal (tracker : MachineHooks.BorrowState) (tag : BorTag) : GlobalState :=
  {tracker.global with protectedTags := tracker.global.protectedTags.insert tag .StrongProtector}

def registeredTracker (tracker : MachineHooks.BorrowState) (tag : BorTag) : MachineHooks.BorrowState :=
  {tracker with global := registeredGlobal tracker tag}

def registeredFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState) (id : AllocId) (tag : BorTag) :=
  TypedRetagEntry.frameWithBorrow frame (borrowFrame.addProtector id tag)

def registeredMachine {K U : Type} (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (tag : BorTag) : MachineHooks.MachineState K U :=
  {machine with borrowTracker := some (registeredTracker tracker tag)}

theorem protected_live_zero_pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base offset : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live[id]? = some entry)
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩)
    (reference : LocalLayout) (mutability : Miri.MIR.Mutability) (mode : RetagPolicy.RetagMode)
    (created : RetagPolicy.create ⟨true,true,true⟩ (if mutability == .Mut then .Mutable else .Shared)
      mode ⟨false,false⟩ = some policy)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,mutability))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine))
    (definitionReady : mode = .FnEntry → ∃ definition, h.instanceDefinition frame.functionInstance = pure definition := by
      first | assumption | (intro _; assumption) | exact ⟨_, by with_unfolding_all rfl⟩) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
        {registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  subst tag
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    {registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tracker.global.nextPointerTag
      with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO allocated = .ok () allocated := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr allocated
  have resolve : h.resolveAllocation place.mplace.ptr allocated =
      .ok (some ⟨id,Size.ofBytes offset,.concrete parentTag⟩) allocated := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers allocated id parentTag base offset width cached
  let location : RetagPipeline.ResolvedLocation := ⟨id, Size.ofBytes offset, .concrete parentTag⟩
  let registered := Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    (registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
  have log : h.logCreation place Size.ZERO policy tracker.global.nextPointerTag (some location) allocated = .ok () allocated := by
    rw [sources.log]
    rfl
  have register : Miri.Verification.TypedRetagWP.registerProtector location policy tracker.global.nextPointerTag allocated =
      .ok () registered := by
    have reg := Miri.Verification.MutableTypedRetag.register_strong location policy tracker.global.nextPointerTag
      allocated frame borrowFrame (allocatedTracker tracker fresh) protection
      (by simp [allocated, Storage.withCurrent, Stack.currentFrame?]) frameBorrow rfl
    simpa [registered, allocated, Miri.Verification.MutableTypedRetag.withStrongProtector,
      registeredFrame, registeredMachine, registeredTracker, registeredGlobal, TypedRetagEntry.frameWithBorrow,
      GlobalState.addProtector, Storage.withCurrent, location] using reg
  have ensure : h.ensureTreeExtra id registered = .ok () registered := by
    rw [sources.ensure,extraWiring]
    exact RetagPointerChecks.ensure_tree_live globalKind globals synchronize registered id entry present
  have completed := congrArg BorrowTree.ChildInsertResult.outcome child
  have reborrow := EmptySharedTree.reborrow h budget place policy tracker.global.nextPointerTag location
    allocated allocated allocated allocated registered entry initial check resolve log register present sources.precise
    frozen initialState ensure completed
  have committed : Miri.Verification.MutableTypedRetag.withTree registered id entry
      (entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
        (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome).tree = after := by
    rw [child]
    rfl
  rw [committed] at reborrow
  have retag := retag_place_at_of_reborrow h budget place policy Size.ZERO Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty
    (if mutability == .Mut then .Mutable else .Shared) mode before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer 0 reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer 0 place.layout := by rw [placeShape]; rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer 0 place.layout
  exact EmptyReferenceSteps.reference_pointer_of_steps h budget value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) place.layout.ty mutability mode policy
    before after shape pointeeQuery permission construct retag reconstruct

#print axioms protected_live_zero_pointer
end DuplicatePrefix.EmptyBackedPointer

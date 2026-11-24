import duplicate_prefix.CurrentMutableRetag
import duplicate_prefix.ExclusiveTypedRetag
import duplicate_prefix.HelperCompilerFacts

namespace DuplicatePrefix.CurrentAsMutFnEntry
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts CurrentMutableRetag

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem completedPointer
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (fuel : Nat)
    (fuelEq : options.place.dynamicFuel = fuel+1)
    (pointers : RootPointers) (reference : LocalLayout) (referenceTy : reference.ty = 1)
    (id : AllocId) (oldTag tag : BorTag) (address length : UInt64)
    (bounded : length ≤ 9223372036854775807)
    (before after : RootState) (borrow : MachineHooks.BorrowState)
    (global : GlobalState) (tracker : before.machine.borrowTracker = some borrow)
    (mode : borrow.retagMode = .FnEntry)
    (implicitOff : options.retag.implicitWrites = false)
    (frame : CompilerFrameContext.ActualFrame)
    (current : before.stack.currentFrame? = some frame)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
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
    TypedRetag.reborrow h options.limits.retag place (Size.ofBytes length) ExclusiveTypedRetag.readPolicy tag
      {before with machine := {before.machine with borrowTracker := some {borrow with global}}} =
      .ok (some (.concrete id tag)) after →
    TypedRetag.machineRetagPtrValue h options.limits.retag input reference.ty before =
      .ok (some result) after := by
  intro cfg h oldPointer newPointer input result place reborrowed
  have q : TypedRetagFields.ReferenceQueries h reference.ty 2 := by
    apply TypedRetagFields.adapted_reference_queries
    · rw [referenceTy]
      with_unfolding_all rfl
    · rw [referenceTy]
      with_unfolding_all rfl
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
    (Size.ofBytes length) Align.ONE ExclusiveTypedRetag.readPolicy before before after borrow global tag
    (.concrete id oldTag) (.concrete id tag) sizing tracker fresh rfl reborrowed
  have implicitWrites : h.implicitWrites before = .ok false before := by
    change cfg.retag.implicitWrites before = _
    rw [configFields.retagImplicit, implicitOff]
    rfl
  have definition : h.instanceDefinition frame.functionInstance before = .ok 3 before := by
    change cfg.retag.instanceDefinition frame.functionInstance before = _
    obtain ⟨_, _, _, _, source, _⟩ := configFields.retagConstruction
    dsimp only [cfg]
    rw [source, callee]
    with_unfolding_all rfl
  have unpin : h.isUnpin 2 before = .ok true before := by rw [q.unpin]; rfl
  have unsafeUnpin : h.isUnsafeUnpin 2 before = .ok true before := by rw [q.unsafeUnpin]; rfl
  have freeze : h.typeIsFreeze 2 before = .ok true before := by rw [q.freeze]; rfl
  have permission := Miri.Verification.MutableTypedRetag.new_mutable_permission h 2
    before before before before before before before frame 3 false false
    unpin unsafeUnpin freeze implicitWrites current definition ⟨rfl,rfl⟩
  apply Miri.Verification.MutableTypedRetag.machine_retag_mutable_pointer h options.limits.retag
    input result reference.ty 2 before before before before before after after place
    (Miri.Verification.MutableTypedRetag.taggedPlace place (.concrete id tag)) borrow
    ExclusiveTypedRetag.readPolicy tracker mode
  · rw [q.shape]
    rfl
  · rw [q.pointee_eq]
    rfl
  · exact permission
  · exact constructed
  · exact styled
  · rfl

end DuplicatePrefix.CurrentAsMutFnEntry

#print axioms DuplicatePrefix.CurrentAsMutFnEntry.completedPointer

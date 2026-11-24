import CanonicalEntryFacts
import duplicate_prefix.EmptyIntegerPrefix
import duplicate_prefix.RootLocalBoolReturn
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Verification
open EmptyIntegerLength EmptyReferenceAllocation
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

private theorem noProvenanceSlice (pointer : Pointer (Option Provenance))
    (noProvenance : pointer.provenance = none) :
    Immediate.newSlice pointer 0 PreparedReflection.actual.runtime.target.base =
      .ok (RetagReferencePlace.integerSliceValue pointer.offset.bytes 0 EmptyReferenceMetadata.reference).imm := by
  obtain ⟨offset,provenance⟩ := pointer
  change provenance = none at noProvenance
  subst provenance
  unfold Immediate.newSlice
  change (show Except ImmediateError (Immediate Provenance) from do
    let scalar ← (Scalar.fromMaybePointer PreparedReflection.actual.runtime.target.base
      (Pointer.withoutProvenance offset.bytes) : Except ScalarError (Scalar Provenance)).mapError ImmediateError.scalar
    let length ← (Scalar.fromUInt (BitVec.ofNat 128 (0 : UInt64).toNat)
      (Size.fromBits PreparedReflection.actual.runtime.target.base.pointerWidth.bits) : Except ScalarError (Scalar Provenance)).mapError ImmediateError.scalar
    pure (.scalarPair scalar length)) = _
  rw [RetagReferencePlace.integer_from_pointer _ offset.bytes (by with_unfolding_all rfl)]
  with_unfolding_all rfl

/-- The saved safety condition holds for every nonzero count on a prepared
non-null no-provenance empty slice, when returning to a cached Boolean local. -/
theorem emptyIntegerRejects
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (noProvenance : pointer.provenance = none) (positive : count ≠ 0)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer 0 count)
    (compiler : InitialCompilerControl before frame) (destination : CachedBoolDestination before frame) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  obtain ⟨older, caller, index, target, unwind, original, oldBool, stack, continuation, targetFits,
    saved, callerType, found, cached, live, callerClocks⟩ := destination.localSlot
  let frames := older.push caller
  let machine := before.machine
  have state : before = Storage.withCurrent frames frame machine := by
    cases before with
    | mk callStack original =>
      cases callStack with
      | mk data =>
        change data = (older.push caller).push frame at stack
        cases stack
        rfl
  obtain ⟨identity, body, location, size⟩ := admitted.emittedFrame loaded
  have callee := admitted.identity.trans (loadedRootInstance_eq loaded)
  obtain ⟨argument, representation, slot1, slot2⟩ := admitted.initialArgumentSlots
  have argumentEq := Except.ok.inj (representation.symm.trans (noProvenanceSlice pointer noProvenance))
  rw [argumentEq] at slot1
  have unused (id : Nat) (bound : id < frame.locals.size) (lo : 7 ≤ id) (hi : id ≤ 12) :
      frame.locals[id] = ⟨.dead, none⟩ := by
    have actual := admitted.initialTemporarySlot loaded compiler id (by omega) (by omega)
    have notImplicit : #[6,13,14].contains id = false := by
      have idCases : id = 7 ∨ id = 8 ∨ id = 9 ∨ id = 10 ∨ id = 11 ∨ id = 12 := by omega
      rcases idCases with h | h | h | h | h | h <;> subst id <;> decide +kernel
    rw [notImplicit] at actual
    exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans actual)
  let profile := admitted.profile
  obtain ⟨tracker, tracked, mode⟩ := profile.mode
  obtain ⟨stored, owned, storedTracker, ownedFrame, rows, headroom, passed⟩ := admitted.allocations.ledger
  have agree : stored = tracker := Option.some.inj (storedTracker.symm.trans tracked)
  subst stored
  have noRows : owned.protectedTags = #[] := by
    cases admitted.destination with
    | physicalRoot root _ _ =>
      have spans := congrArg Array.size (root.symm.trans stack)
      simp at spans
    | cachedCaller _ ledger =>
      obtain ⟨actual, present, savedRows⟩ := ledger
      have same : actual = owned := Option.some.inj (present.symm.trans ownedFrame)
      subst actual
      exact savedRows.trans (by simp [argumentLedger, noProvenance])
  have capacity : tracker.global.nextPointerTag.value.toNat + 4 < 2^64 := headroom
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat < 18446744073709551615; omega)
  have freshAgain : (allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (tracker.global.nextPointerTag.value + 1).toNat < 18446744073709551615
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)]
    omega
  obtain ⟨thread, active, cacheBound⟩ := admitted.stack.active
  have within (i : Nat) (position : thread.topUserRelevantFrame = some i) : i < frames.size+1 := by
    have bound := cacheBound i position
    simpa [stack, frames, Array.size_push] using bound
  have k3 := admitted.initialTemporarySlot loaded compiler 3 (by decide) (by decide)
  have k4 := admitted.initialTemporarySlot loaded compiler 4 (by decide) (by decide)
  have k5 := admitted.initialTemporarySlot loaded compiler 5 (by decide) (by decide)
  have k13 := admitted.initialTemporarySlot loaded compiler 13 (by decide) (by decide)
  obtain ⟨result, final, trace, resultBody, resultIdentity, resultFn, pc, boolValue, resultExtra,
    resultPlace, resultContinue, resultArgs, immediate, memory, tracking, ghost, shallow, race, fixed, unchecked,
    noGc, addresses, types, backend, extras, finalActive⟩ :=
    EmptyIntegerPrefix.reaches_return options limits remaining dispatch calling span profile.preciseInteriorMutOff
      profile.implicitWritesOff profile.debugOff cmp compilerSourceComparator
      dynamicFuel fuel sizing validation frames frame machine pointer.offset.bytes count admitted.slice.nonnull positive
      body identity callee location size unused admitted.resultSlot slot1 slot2
      (by simpa using k3) (by simpa using k4) (by simpa using k5) (by simpa using k13)
      admitted.immediateLocals tracker tracked mode fresh freshAgain admitted.stack.calleeClocksOff
      profile.ghostOff profile.shallow profile.raceOff profile.backendOff thread active within
      profile.compilerRuntime profile.noSyntheticSliceCache profile.unchecked profile.noGc profile.fixed
  obtain ⟨bound, localResult⟩ := Array.getElem?_eq_some_iff.mp boolValue
  obtain ⟨destBound, dest⟩ := Array.getElem?_eq_some_iff.mp found
  obtain ⟨threadAfter, activeAfter⟩ := finalActive
  let finalTracker := allocatedTracker (allocatedTracker tracker fresh) freshAgain
  have noRelease : StackPopRelease.Plan finalTracker.global.protectedTags owned.protectedTags.toList final.memory final.memory := by
    rw [noRows]
    exact .nil _
  have returnStep := RootLocalBoolReturn.step_with_plan options limits remaining span profile.debugOff fuel validation
    older caller result final false (resultBody.trans body) pc bound (congrArg LocalState.value localResult)
    (congrArg LocalState.layout localResult) ((congrArg (·.dataRace) resultExtra).trans admitted.stack.calleeClocksOff)
    index destBound oldBool ((congrArg LocalState.value dest).trans live) ((congrArg LocalState.layout dest).trans cached)
    callerClocks (by rw [resultPlace, saved]; rfl) target unwind (resultContinue.trans continuation) immediate
    (resultArgs.trans admitted.stack.noVarargs) finalTracker owned tracking (by rw [resultExtra]; exact ownedFrame)
    final.memory noRelease threadAfter activeAfter unchecked noGc fixed ghost shallow
  rw [state]
  apply DuplicatePrefix.GeneratedSafetyOfTrace.required program loaded _ limits _ _ (state ▸ admitted.entered)
    (SuccessfulTrace.append trace (.next returnStep (.refl _)))
  simp [Storage.withCurrent, frames]

#print axioms emptyIntegerRejects
end
end DuplicatePrefix.CanonicalCallDomain

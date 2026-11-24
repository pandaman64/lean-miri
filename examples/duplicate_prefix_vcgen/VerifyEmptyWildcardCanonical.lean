import CanonicalEntryFacts
import CanonicalPhysicalWindow
import VerifyZeroPhysicalCanonical
import PhysicalEndCall
import duplicate_prefix.EmptyWildcardPrefix
import duplicate_prefix.RootLocalBoolReturn
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.Concurrency Miri.DataStructures Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Verification
open EmptyWildcardLength EmptyReferenceAllocation ArchiveForestProjection GeneralRangeMapOrigins SourceDomain
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

private theorem wildcardSlice (pointer : Pointer (Option Provenance))
    (wildcard : pointer.provenance = some .wildcard) :
    Immediate.newSlice pointer 0 PreparedReflection.actual.runtime.target.base =
      .ok (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
        (Pointer.new .wildcard (Size.ofBytes pointer.offset.bytes)) 0 EmptyReferenceMetadata.reference).imm := by
  obtain ⟨⟨address⟩,provenance⟩ := pointer
  change provenance = some .wildcard at wildcard
  subst provenance
  with_unfolding_all rfl

/-- The saved safety condition holds for every nonzero count on a prepared
non-null unresolved wildcard-provenance empty slice, when returning to a cached Boolean local. -/
theorem emptyWildcardRejectsCached
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (wildcard : pointer.provenance = some .wildcard)
    (unresolved : EmptyWildcardLocalValidator.Unresolved before.machine.user.addresses before.machine.memory pointer.offset.bytes) (positive : count ≠ 0)
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
  have argumentEq := Except.ok.inj (representation.symm.trans (wildcardSlice pointer wildcard))
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
      exact savedRows.trans (by simp [argumentLedger, wildcard])
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
    EmptyWildcardPrefix.reaches_return options limits remaining dispatch calling span profile.preciseInteriorMutOff
      profile.implicitWritesOff profile.debugOff ProjectionMetadataFacts.nullComparator compilerSourceComparator
      dynamicFuel fuel sizing validation frames frame machine pointer.offset.bytes count admitted.slice.nonnull positive unresolved
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

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser

private theorem zeroTickFields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineState) :
    let after := PtrMetadataReturn.accountedMachine options remaining span machine
    after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
      after.threads = machine.threads ∧ after.dataRace = machine.dataRace ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.ghost = machine.user.payload.ghost ∧
      after.user.payload.validation = machine.user.payload.validation ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  dsimp only
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem grantForByte {tree : BorrowTree} {start : Size} {source : UniIndex}
    {tags : ProtectedTags} (grant : ByteWriteGrant tree start.bytes source tags)
    (extent : ReleaseRange tree source start 1) :
    OwnedOn (fun row => LocationRights tree row tags source)
      start.bytes (start.bytes + 1) tree.locations := by
  have fits : start.bytes.toNat + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt extent.extent tree.locations.size.bytes.toNat_lt
  have endByte : (start.bytes + 1).toNat = start.bytes.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  intro position inside _ starts stops
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  have below : segment.range.start ≤ start.bytes := by
    rw [UInt64.le_iff_toNat_le]
    change segment.range.start.toNat < (start.bytes + 1).toNat at starts
    omega
  exact grant segment member below (UInt64.lt_iff_toNat_lt.mpr stops)

theorem emptyWildcardRejectsPhysical
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (wildcard : pointer.provenance = some .wildcard)
    (unresolved : EmptyWildcardLocalValidator.Unresolved before.machine.user.addresses before.machine.memory pointer.offset.bytes) (positive : count ≠ 0)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer 0 count)
    (compiler : InitialCompilerControl before frame) (physical : PhysicalBoolDestination before frame pointer 0)
    (stack : before.stack.frames = #[frame]) (continuation : frame.returnContinuation = .stop true) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  let frames : Array CompilerFrameContext.ActualFrame := #[]
  let machine := before.machine
  have state : before = Storage.withCurrent frames frame machine := withFrames stack
  obtain ⟨identity, body, location, size⟩ := admitted.emittedFrame loaded
  have callee := admitted.identity.trans (loadedRootInstance_eq loaded)
  obtain ⟨argument, representation, slot1, slot2⟩ := admitted.initialArgumentSlots
  have argumentEq := Except.ok.inj (representation.symm.trans (wildcardSlice pointer wildcard))
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
  obtain ⟨place, id, allocation, relative, tag, base, stored, owned, source, returnTag, holder,
    saved, layout, aligned, live, mutable, storage, mask, maskLength, provenance, fits, ptr, _,
    address, addressFits, cached, storedTracker, trackedFrame, ledger, _, coherent, sourceKey,
    sourceNode, holderKey, holderNode, extent, writeGrant, _, separated⟩ := physical.storage
  have agree : stored = tracker := Option.some.inj (storedTracker.symm.trans tracked)
  subst stored
  obtain ⟨ledgerTracker, ledgerOwner, ledgerTracked, ledgerFrame, rows, headroom, passed⟩ := admitted.allocations.ledger
  have corresponding : ledgerTracker = tracker := Option.some.inj (ledgerTracked.symm.trans tracked)
  subst ledgerTracker
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
    EmptyWildcardPrefix.reaches_return options limits remaining dispatch calling span profile.preciseInteriorMutOff
      profile.implicitWritesOff profile.debugOff ProjectionMetadataFacts.nullComparator compilerSourceComparator
      dynamicFuel fuel sizing validation frames frame machine pointer.offset.bytes count admitted.slice.nonnull positive unresolved
      body identity callee location size unused admitted.resultSlot slot1 slot2
      (by simpa using k3) (by simpa using k4) (by simpa using k5) (by simpa using k13)
      admitted.immediateLocals tracker tracked mode fresh freshAgain admitted.stack.calleeClocksOff
      profile.ghostOff profile.shallow profile.raceOff profile.backendOff thread active within
      profile.compilerRuntime profile.noSyntheticSliceCache profile.unchecked profile.noGc profile.fixed
  obtain ⟨bound0, localResult⟩ := Array.getElem?_eq_some_iff.mp boolValue
  obtain ⟨threadAfter, activeAfter⟩ := finalActive
  let finalTracker := allocatedTracker (allocatedTracker tracker fresh) freshAgain
  have oneRow : owned.protectedTags = #[(id,returnTag)] := by simpa [argumentLedger, wildcard] using ledger
  have ownedTag : returnTag ∈ owned.protectedTags.toList.map Prod.snd := by rw [oneRow]; simp
  obtain ⟨node, atNode, nodeTag, parent, hidden⟩ := holderNode
  obtain ⟨afterTree, outputReleased, treeFrame, afterCoherent, treeSize, owners⟩ :=
    physicalReleasePreservesParent allocation.allocation.extra finalTracker.global owned returnTag holder source
      node relative holderKey atNode nodeTag parent hidden coherent extent ownedTag (grantForByte writeGrant extent)
  let charged := PtrMetadataReturn.accountedMachine options remaining span final
  have ticked := zeroTickFields options remaining span final
  have heap : charged.memory = machine.memory := ticked.1.trans memory
  have trackerNow : charged.borrowTracker = some finalTracker := ticked.2.1.trans tracking
  have liveThread : charged.threads.activeThread? = some threadAfter := by rw [ticked.2.2.1]; exact activeAfter
  let finalHeap := StackPopRelease.commitTree charged.memory id allocation afterTree
  have legalRelease : StackPopRelease.Plan finalTracker.global.protectedTags owned.protectedTags.toList
      charged.memory finalHeap := by
    rw [oneRow]
    exact .live id returnTag allocation afterTree [] charged.memory finalHeap
      (by rw [heap]; exact live) outputReleased (.nil finalHeap)
  have outputLive := StackPopRelease.lookup_commit_same charged.memory id allocation afterTree
  let released := ActualPopPlan.released charged finalHeap finalTracker owned
  let passed := GenericPopFrame.afterRelevanceAt #[] result released (threadAfter.topUserRelevantFrame.getD 0)
  let retState : State := ⟨⟨#[]⟩, passed⟩
  have resultHeap : retState.machine.memory = finalHeap := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  let poppedTracker := {finalTracker with global := finalTracker.global.endCall owned}
  have resultTracker : retState.machine.borrowTracker = some poppedTracker := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultUser : retState.machine.user = charged.user := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultRace : retState.machine.dataRace = charged.dataRace := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have outputAddresses : retState.machine.user.addresses = machine.user.addresses :=
    (congrArg (·.addresses) resultUser).trans (ticked.2.2.2.2.1.trans addresses)
  have extrasPreserved : retState.machine.user.payload.payload.user.runtime.extras =
      machine.user.payload.payload.user.runtime.extras :=
    (congrArg (·.payload.payload.user.runtime.extras) resultUser).trans (ticked.2.2.2.2.2.2.2.2.trans extras)
  have finalRace : retState.machine.dataRace = none := resultRace.trans (ticked.2.2.2.1.trans race)
  have finalBackend : retState.machine.user.payload.payload.user.backend = .none :=
    (congrArg (·.payload.payload.user.backend) resultUser).trans (ticked.2.2.2.2.2.2.2.1.trans (backend.trans profile.backendOff))
  have beforeGhost : charged.user.payload.ghost = false := ticked.2.2.2.2.2.1.trans ghost
  have finalGhost : retState.machine.user.payload.ghost = false :=
    (congrArg (·.payload.ghost) resultUser).trans beforeGhost
  have finalShallow : retState.machine.user.payload.validation = .Shallow :=
    (congrArg (·.payload.validation) resultUser).trans (ticked.2.2.2.2.2.2.1.trans shallow)
  let window := physicalWindowAfterRelease retState.machine place id tag base relative allocation afterTree
    layout aligned (by rw [resultHeap]; exact outputLive) (by rw [outputAddresses]; exact cached)
    mutable storage mask maskLength provenance fits ptr address addressFits
  have newKey : window.entry.allocation.extra.indexOfTag window.tag = some source := by
    change afterTree.indexOfTag tag = some source
    rw [treeFrame]
    exact sourceKey
  obtain ⟨originalSource, sourceHere, _⟩ := sourceNode
  have newNode : window.entry.allocation.extra.nodeAt source = some originalSource := by
    change afterTree.nodeAt source = some originalSource
    rw [treeFrame]
    exact sourceHere
  obtain ⟨root, rootEq⟩ := extent.root (by decide)
  have roots : window.entry.allocation.extra.roots = #[root] := by
    change afterTree.roots = #[root]
    rw [treeFrame]
    exact rootEq
  have bound : window.offset.toNat + 1 ≤ window.entry.allocation.extra.locations.size.bytes.toNat := by
    change relative.bytes.toNat + 1 ≤ afterTree.locations.size.bytes.toNat
    rw [treeSize]
    exact extent.extent
  have effects := ordinaryPhysicalExtras admitted retState.machine id allocation live extrasPreserved
  have addressBound : place.mplace.ptr.offset.bytes.toNat + 1 < 2^64 := by
    have overflow := addressFits
    have within := UInt64.lt_iff_toNat_lt.mp fits
    omega
  obtain ⟨updated, returned, stopped, _, _, _⟩ :=
    RootWindowPhysicalReturn.return_step_terminal options remaining span limits fuel validation
      admitted.profile.debugOff result final charged rfl unchecked noGc fixed
      finalTracker owned trackerNow (by rw [resultExtra]; exact trackedFrame) finalHeap legalRelease threadAfter liveThread
      retState rfl (resultBody.trans body) pc bound0 false
      (congrArg LocalState.value localResult) (congrArg LocalState.layout localResult)
      ((congrArg MachineHooks.FrameExtra.dataRace resultExtra).trans admitted.stack.calleeClocksOff) beforeGhost
      (resultContinue.trans continuation) immediate (resultArgs.trans admitted.stack.noVarargs)
      place window (by rw [resultPlace,saved]; rfl) poppedTracker resultTracker finalRace finalBackend finalGhost finalShallow
      source root originalSource newNode newKey roots afterCoherent bound owners effects addressBound
  rw [state]
  apply GeneratedSafetyOfTrace.required program loaded _ limits _ _ (state ▸ admitted.entered)
    (SuccessfulTrace.append trace (.next returned (.refl _)))
  simp [CanonicalCopy.replaceAllocation, retState, Storage.withCurrent, frames]

#print axioms emptyWildcardRejectsPhysical

/-- The saved safety VC for every positive count and admitted destination of
an empty wildcard slice whose zero-width lookup is unresolved. -/
theorem emptyWildcardRejects
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (wildcard : pointer.provenance = some .wildcard)
    (unresolved : EmptyWildcardLocalValidator.Unresolved before.machine.user.addresses before.machine.memory pointer.offset.bytes) (positive : count ≠ 0)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer 0 count)
    (compiler : InitialCompilerControl before frame) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  cases admitted.destination with
  | physicalRoot stack continuation physical =>
    exact emptyWildcardRejectsPhysical program loaded options limits remaining dynamicFuel fuel dispatch span
      sizing validation calling before frame pointer count wildcard unresolved positive admitted compiler physical stack continuation
  | cachedCaller destination _ =>
    exact emptyWildcardRejectsCached program loaded options limits remaining dynamicFuel fuel dispatch span
      sizing validation calling before frame pointer count wildcard unresolved positive admitted compiler destination

/-- Every admitted count for a prepared empty wildcard argument with a
successful unresolved lookup satisfies the original saved safety VC. -/
theorem allCountsEmptyWildcard
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (wildcard : pointer.provenance = some .wildcard)
    (unresolved : EmptyWildcardLocalValidator.Unresolved before.machine.user.addresses before.machine.memory pointer.offset.bytes)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer 0 count)
    (compiler : InitialCompilerControl before frame) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  by_cases zero : count = 0
  · subst count
    exact zeroCount program loaded options limits remaining span fuel validation before frame pointer 0 admitted compiler
  · exact emptyWildcardRejects program loaded options limits remaining dynamicFuel fuel dispatch span
      sizing validation calling before frame pointer count wildcard unresolved zero admitted compiler

#print axioms allCountsEmptyWildcard

#print axioms emptyWildcardRejects

#print axioms emptyWildcardRejectsCached
end
end DuplicatePrefix.CanonicalCallDomain

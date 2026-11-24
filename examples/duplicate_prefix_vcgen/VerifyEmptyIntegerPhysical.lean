import duplicate_prefix.EmptyIntegerPrefix
import VerifyZeroCachedCanonical
import ZeroCanonicalPhysicalPlan

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open Miri.TreeBorrows Miri.Verification
open EmptyReferenceAllocation
open RootZeroShallowReturn SourceDomain ArchiveForestProjection GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame

private theorem zeroTickFields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineState) :
    let after := RootZeroCompleteState.tick options remaining span machine
    after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
      after.threads = machine.threads ∧ after.dataRace = machine.dataRace ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.ghost = machine.user.payload.ghost ∧
      after.user.payload.validation = machine.user.payload.validation ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  dsimp only
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem rebuildPointer (p : Pointer (Option Provenance)) :
    p = Pointer.new p.provenance (Size.ofBytes p.offset.bytes) := by
  cases p with
  | mk offset provenance => cases offset; rfl

private theorem exactExtras {P : Type} (rows : Array (AllocId × MemoryExtras.AllocationExtra P))
    (id : AllocId) (extra : MemoryExtras.AllocationExtra P)
    (lookup : rows.find? (·.1 == id) = some (id,extra))
    (weak : extra.weakMemory = none) (sync : extra.sync = #[]) :
    rows.find? (·.1 == id) = some (id, {weakMemory := none, backtrace := AllocationBacktrace.get rows id}) := by
  rw [lookup, AllocationBacktrace.of_lookup lookup]
  cases extra
  simp_all

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

/-- Every nonzero count on a non-null no-provenance empty slice rejects
and returns false through the actual protected physical Boolean destination. -/
theorem emptyIntegerPhysicalRejects
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (noProvenance : pointer.provenance = none) (positive : count ≠ 0)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer 0 count)
    (compiler : InitialCompilerControl before frame) (physical : PhysicalBoolDestination before frame pointer 0)
    (stack : before.stack.frames = #[frame]) (continuation : frame.returnContinuation = .stop true) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let machine := before.machine
  have state : before = Storage.withCurrent #[] frame machine := withFrames stack
  let profile := admitted.profile
  obtain ⟨place, id, allocation, relative, tag, base, tracker, owned, source, returnTag, holder,
    saved, layout, aligned, live, mutable, storage, mask, maskLength, provenance, fits, ptr, _,
    address, addressFits, cached, tracked, trackedFrame, ledger, _, coherent, sourceKey,
    sourceNode, holderKey, holderNode, extent, writeGrant, _, separated⟩ := physical.storage
  obtain ⟨old, oldTracker, mode⟩ := admitted.profile.mode
  have same : old = tracker := Option.some.inj (oldTracker.symm.trans tracked)
  subst old
  obtain ⟨node, atNode, nodeTag, parent, hidden⟩ := holderNode
  have ownedTag : returnTag ∈ owned.protectedTags.toList.map Prod.snd := by
    rw [ledger]
    simp
  obtain ⟨afterTree, outputReleased, treeFrame, afterCoherent, treeSize, owners⟩ :=
    physicalReleasePreservesParent allocation.allocation.extra tracker.global owned returnTag holder source
      node relative holderKey atNode nodeTag parent hidden coherent extent ownedTag (grantForByte writeGrant extent)
  let finalHeap := StackPopRelease.commitTree machine.memory id allocation afterTree
  have outputLive := StackPopRelease.lookup_commit_same machine.memory id allocation afterTree
  have release : StackPopRelease.Plan tracker.global.protectedTags owned.protectedTags.toList
      machine.memory finalHeap := by
    rw [ledger]
    simpa [argumentLedger, noProvenance] using
      (StackPopRelease.Plan.live _ _ _ _ [] _ _ live outputReleased (.nil finalHeap) :
        StackPopRelease.Plan tracker.global.protectedTags [(id,returnTag)] machine.memory finalHeap)
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
  obtain ⟨previous, prevOwned, prevTracked, prevFrame, distinct, headroom, others⟩ := admitted.allocations.ledger
  have trackers : previous = tracker := Option.some.inj (prevTracked.symm.trans tracked)
  subst previous
  have capacity : tracker.global.nextPointerTag.value.toNat + 4 < 2^64 := headroom
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat < 18446744073709551615; omega)
  have freshAgain : (allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (tracker.global.nextPointerTag.value + 1).toNat < 18446744073709551615
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)]
    omega
  obtain ⟨thread, active, cacheBound⟩ := admitted.stack.active
  have within (i : Nat) (position : thread.topUserRelevantFrame = some i) : i < (#[ ] : Array Frame).size+1 := by
    simpa [stack] using cacheBound i position
  have k3 := admitted.initialTemporarySlot loaded compiler 3 (by decide) (by decide)
  have k4 := admitted.initialTemporarySlot loaded compiler 4 (by decide) (by decide)
  have k5 := admitted.initialTemporarySlot loaded compiler 5 (by decide) (by decide)
  have k13 := admitted.initialTemporarySlot loaded compiler 13 (by decide) (by decide)
  obtain ⟨result, final, trace, resultBody, resultIdentity, resultFn, pc, boolValue, resultExtra,
    resultPlace, resultContinue, resultArgs, immediate, memory, tracking, postGhost, postShallow, postRace, fixed, unchecked,
    noGc, postAddresses, types, postBackend, extras, finalActive⟩ :=
    EmptyIntegerPrefix.reaches_return options limits remaining dispatch calling span profile.preciseInteriorMutOff
      profile.implicitWritesOff profile.debugOff (show ProjectionMetadataFacts.NullComparator from by first | exact True.intro | unfold ProjectionMetadataFacts.NullComparator; decide) compilerSourceComparator
      dynamicFuel fuel sizing validation (#[] : Array Frame) frame machine pointer.offset.bytes count admitted.slice.nonnull positive
      body identity callee location size unused admitted.resultSlot slot1 slot2
      (by simpa using k3) (by simpa using k4) (by simpa using k5) (by simpa using k13)
      admitted.immediateLocals tracker tracked mode fresh freshAgain admitted.stack.calleeClocksOff
      profile.ghostOff profile.shallow profile.raceOff profile.backendOff thread active within
      profile.compilerRuntime profile.noSyntheticSliceCache profile.unchecked profile.noGc profile.fixed
  let currentTracker := EmptyReferenceAllocation.allocatedTracker
    (EmptyReferenceAllocation.allocatedTracker tracker fresh) freshAgain
  let charged := PtrMetadataReturn.accountedMachine options remaining span final
  have tails := zeroTickFields options remaining span final
  have trackerNow : charged.borrowTracker = some currentTracker := tails.2.1.trans tracking
  obtain ⟨threadAfter, activeAfter⟩ := finalActive
  have liveThread : charged.threads.activeThread? = some threadAfter := by
    change (RootZeroCompleteState.tick options remaining span final).threads.activeThread? = some threadAfter
    rw [tails.2.2.1]
    exact activeAfter
  have legalRelease : StackPopRelease.Plan currentTracker.global.protectedTags owned.protectedTags.toList
      charged.memory finalHeap := by
    change StackPopRelease.Plan currentTracker.global.protectedTags owned.protectedTags.toList
      (RootZeroCompleteState.tick options remaining span final).memory finalHeap
    rw [tails.1, memory]
    exact release
  let released := ActualPopPlan.released charged finalHeap currentTracker owned
  let passed := GenericPopFrame.afterRelevanceAt #[] result released (threadAfter.topUserRelevantFrame.getD 0)
  let retState : State := ⟨⟨#[]⟩, passed⟩
  have resultHeap : retState.machine.memory = finalHeap := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  let finalTracker := {currentTracker with global := currentTracker.global.endCall owned}
  have resultTracker : retState.machine.borrowTracker = some finalTracker := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultUser : retState.machine.user = charged.user := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultRace : retState.machine.dataRace = charged.dataRace := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have addresses : retState.machine.user.addresses = machine.user.addresses :=
    (congrArg (·.addresses) resultUser).trans (tails.2.2.2.2.1.trans postAddresses)
  have extrasPreserved : retState.machine.user.payload.payload.user.runtime.extras =
      machine.user.payload.payload.user.runtime.extras :=
    (congrArg (·.payload.payload.user.runtime.extras) resultUser).trans (tails.2.2.2.2.2.2.2.2.trans extras)
  have race : retState.machine.dataRace = none :=
    resultRace.trans (tails.2.2.2.1.trans postRace)
  have backend : retState.machine.user.payload.payload.user.backend = .none :=
    (congrArg (·.payload.payload.user.backend) resultUser).trans (tails.2.2.2.2.2.2.2.1.trans (postBackend.trans profile.backendOff))
  have beforeGhost : charged.user.payload.ghost = false := tails.2.2.2.2.2.1.trans postGhost
  have ghost : retState.machine.user.payload.ghost = false := (congrArg (·.payload.ghost) resultUser).trans beforeGhost
  have shallow : retState.machine.user.payload.validation = .Shallow :=
    (congrArg (·.payload.validation) resultUser).trans (tails.2.2.2.2.2.2.1.trans postShallow)
  have width := allocation.allocation.byteSize.bytes.toNat_lt
  have relativeFits := UInt64.lt_iff_toNat_lt.mp fits
  have absFits : base.toNat + relative.bytes.toNat < 2^64 := by omega
  have addNat : (base + relative.bytes).toNat = base.toNat + relative.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt absFits]
  have originalOffset : place.mplace.ptr.offset.bytes = base + relative.bytes :=
    UInt64.toNat.inj (address.trans addNat.symm)
  have exactPointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+relative.bytes)) := by
    exact (rebuildPointer place.mplace.ptr).trans (by rw [ptr,originalOffset])
  let finalEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {allocation with allocation := allocation.allocation.setExtra afterTree}
  let window : PhysicalBoolWindowWrite.Window retState.machine place := {
    layout, aligned, id, tag
    entry := finalEntry
    base
    offset := relative.bytes
    capacity := allocation.allocation.byteSize.bytes
    live := by rw [resultHeap]; exact outputLive
    cachedBase := by rw [addresses]; exact cached
    pointer := exactPointer
    bounds := by omega
    size := by change allocation.allocation.byteSize = Size.ofBytes allocation.allocation.byteSize.bytes; cases allocation.allocation.byteSize; rfl
    bytes := storage
    mutable
    maskValid := mask
    maskLength
    provenance := ProvenanceCopy.WellFormed.pointerBounds provenance }
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
  have effects : let ctx := (DuplicatePrefixPhysicalContexts.canonical options remaining span).writeContext
      (ctx.extras.get retState.machine.user).allocations.find? (·.1 == id) =
        some (id, {weakMemory := none, backtrace := (AllocationBacktrace.get
          ((ctx.extras.get retState.machine.user).allocations) id)}) := by
    dsimp only
    let actualRows := retState.machine.user.payload.payload.user.runtime.extras.allocations
    change actualRows.find? (·.1 == id) =
      some (id,{weakMemory := none, backtrace := AllocationBacktrace.get actualRows id})
    dsimp only [actualRows]
    obtain ⟨extra, location, weak, sync⟩ := admitted.allocations.extras id
      (MemoryCopyBridge.live_any_of_present before.machine.memory id allocation live)
    have baseFacts := exactExtras _ id extra location weak sync
    have extrasEq : retState.machine.user.payload.payload.user.runtime.extras =
        before.machine.user.payload.payload.user.runtime.extras := extrasPreserved
    rw [extrasEq]
    exact baseFacts
  have addressBound : place.mplace.ptr.offset.bytes.toNat + 1 < 2^64 := by omega
  obtain ⟨valid, returnedBool⟩ := Array.getElem?_eq_some_iff.mp boolValue
  obtain ⟨updated, returned, stopped, _, _, _⟩ :=
    RootWindowPhysicalReturn.return_step_terminal options remaining span limits fuel validation
      profile.debugOff result final charged rfl unchecked noGc fixed
      currentTracker owned trackerNow (by rw [resultExtra]; exact trackedFrame) finalHeap legalRelease threadAfter liveThread
      retState rfl (resultBody.trans body) pc valid false
      (congrArg LocalState.value returnedBool) (congrArg LocalState.layout returnedBool)
      ((congrArg MachineHooks.FrameExtra.dataRace resultExtra).trans admitted.stack.calleeClocksOff) beforeGhost
      (resultContinue.trans continuation) immediate (resultArgs.trans admitted.stack.noVarargs)
      place window (by rw [resultPlace,saved]; rfl) finalTracker resultTracker race backend ghost shallow
      source root originalSource newNode newKey roots afterCoherent bound owners effects addressBound
  rw [state]
  apply GeneratedSafetyOfTrace.required program loaded config limits _ _ (state ▸ admitted.entered)
    (SuccessfulTrace.append trace (.next returned (.refl _)))
  simp [CanonicalCopy.replaceAllocation,retState,Storage.withCurrent]


#print axioms emptyIntegerPhysicalRejects
end DuplicatePrefix.CanonicalCallDomain

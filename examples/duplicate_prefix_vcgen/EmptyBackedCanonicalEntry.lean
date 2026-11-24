import duplicate_prefix.SharedKeyResources
import CanonicalEntryFacts
import duplicate_prefix.EmptyBackedPrefix
import CanonicalCallRelease
import VerifyAllCountCanonicalPhysical
import duplicate_prefix.RootLocalBoolReturn
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Verification
open EmptyBackedLength EmptyReferenceAllocation
open Miri.DataStructures
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

/-- The actual root reached its false Return after both zero-width retags.
The original dormant tag is still present, and other live allocations retain
their exact pre-call table entries. -/
structure EmptyBackedEndpoint
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (frames : Array CompilerFrameContext.ActualFrame)
    (result : CompilerFrameContext.ActualFrame) (final : MachineState)
    (id : AllocId) (tag : BorTag) (updated : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (holder : UniIndex) (finalTracker : MachineHooks.BorrowState) : Prop where
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    before (Storage.withCurrent frames result final)
  body : result.body = RootBody.reflected.body.body
  location : result.location = .mir ⟨10,0⟩
  resultSlot : result.locals[0]? =
    some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  extra : result.extra = frame.extra
  returnPlace : result.returnPlace = frame.returnPlace
  continuation : result.returnContinuation = frame.returnContinuation
  varargs : result.vaList = frame.vaList
  immediate : ZeroImmediateFacts.AllImmediate result
  sourceLive : final.memory.live[id]? = some updated
  otherLive : ∀ key, key ≠ id → final.memory.live[key]? = before.machine.memory.live[key]?
  tagAt : updated.allocation.extra.indexOfTag tag = some holder
  node : ∃ node, updated.allocation.extra.nodeAt holder = some node ∧ node.isExposed = false
  dormant : ∀ pos (valid : pos < updated.allocation.extra.locations.entries.size),
    updated.allocation.extra.locations.entries[pos].data.perms.get holder = none
  tracked : final.borrowTracker = some finalTracker
  sameProtections : ∃ initial, before.machine.borrowTracker = some initial ∧
    initial.global.protectedTags = finalTracker.global.protectedTags
  ghost : final.user.payload.ghost = false
  shallow : final.user.payload.validation = .Shallow
  race : final.dataRace = none
  fixed : final.threads.fixedScheduling = true
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl final.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl final.user).gcInterval = 0
  addresses : final.user.addresses = before.machine.user.addresses
  types : final.user.payload.payload.user.types = before.machine.user.payload.payload.user.types
  backend : final.user.payload.payload.user.backend = .none
  extras : final.user.payload.payload.user.runtime.extras = before.machine.user.payload.payload.user.runtime.extras
  active : ∃ thread, final.threads.activeThread? = some thread
  transfer : ∃ old fresh,
    before.machine.memory.live[id]? = some old ∧
    updated = {old with allocation := old.allocation.setExtra updated.allocation.extra} ∧
    EmptySharedWriteFrame.Transfer old.allocation.extra updated.allocation.extra fresh ∧
    (∀ index, updated.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < updated.allocation.extra.locations.entries.size),
        updated.allocation.extra.locations.entries[position].data.perms.get index = none) ∧
    (∀ index node, old.allocation.extra.nodeAt index = some node → node.tag ∉ fresh) ∧
    (∀ freshTag ∈ fresh, finalTracker.global.protectedTags.contains freshTag = false)

theorem emptyBackedReachesReturn
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining dynamicFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sizing : options.place.dynamicFuel = dynamicFuel+1)
    (validation : options.limits.validation = fuel+1) (calling : limits.callDispatch = dispatch+1)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : CompilerFrameContext.ActualFrame) (pointer : Pointer (Option Provenance)) (count : UInt64)
    (id : AllocId) (tag : BorTag) (concrete : pointer.provenance = some (.concrete id tag))
    (ready : ∀ entry, before.machine.memory.live[id]? = some entry →
      RetagInsertionCapacity.Ready entry.allocation.extra ∧ entry.allocation.extra.nodes.size + 2 < 2^32)
    (positive : count ≠ 0)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer 0 count)
    (compiler : InitialCompilerControl before frame)
    (frames : Array CompilerFrameContext.ActualFrame) (stack : before.stack.frames = frames.push frame) :
    ∃ result final updated holder finalTracker,
      EmptyBackedEndpoint options limits remaining span before frame frames result final id tag updated holder finalTracker := by
  let machine := before.machine
  have state : before = Storage.withCurrent frames frame machine := by
    cases before with
    | mk callStack original =>
      cases callStack with
      | mk data =>
        change data = frames.push frame at stack
        cases stack
        rfl
  obtain ⟨identity, body, location, size⟩ := admitted.emittedFrame loaded
  have callee := admitted.identity.trans (loadedRootInstance_eq loaded)
  obtain ⟨argument, representation, slot1, slot2⟩ := admitted.initialArgumentSlots
  have physical := admitted.emptyProtector rfl
  rw [concrete] at physical
  obtain ⟨entry, holder, node, trackedBy, base, start, found, profileTracker, _, tagAt, nodeAt, hidden,
    coherent, cachedAddress, addressNat, extent⟩ := physical
  obtain ⟨cap, room⟩ := ready entry found
  have sumFits : base.toNat + start.bytes.toNat < 2^64 :=
    by rw [← addressNat]; exact pointer.offset.bytes.toNat_lt
  have address : pointer.offset.bytes = base + start.bytes := UInt64.toNat.inj (by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt sumFits]
    exact addressNat)
  have nonzeroAddress : base + start.bytes ≠ 0 := by rw [← address]; exact admitted.slice.nonnull
  have proofArgument := RootZeroShallowReturn.concreteSliceImmediate pointer id tag base start.bytes 0 concrete address
  have argumentEq := Except.ok.inj (representation.symm.trans proofArgument)
  have data : (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base =
      PreparedReflection.actual.runtime.target.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span]
  rw [argumentEq] at slot1
  have nodeTag : node.tag = tag :=
    ArchiveForestProjection.ready_tag_at entry.allocation.extra cap holder tag node tagAt nodeAt
  have dormant (position : Nat) (valid : position < entry.allocation.extra.locations.entries.size) :
      entry.allocation.extra.locations.entries[position].data.perms.get holder = none :=
    ReleaseRange.noEmptyMaterialization extent coherent.ranges valid
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
  obtain ⟨stored, owned, storedTracker, ownedFrame, rows, headroom, protectorsOld, _, allOld⟩ := admitted.allocations.ledger
  have agree : stored = tracker := Option.some.inj (storedTracker.symm.trans tracked)
  subst stored
  have capacity : tracker.global.nextPointerTag.value.toNat + 4 < 2^64 := headroom
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat < 18446744073709551615; omega)
  have freshAgain : (allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (tracker.global.nextPointerTag.value + 1).toNat < 18446744073709551615
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)]
    omega
  have nextAge : tracker.global.nextPointerTag.value < (allocatedTracker tracker fresh).global.nextPointerTag.value := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change tracker.global.nextPointerTag.value.toNat < (tracker.global.nextPointerTag.value + 1).toNat
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega : tracker.global.nextPointerTag.value.toNat + 1 < 2^64)]
    omega
  have unprotected : tracker.global.protectedTags.contains (allocatedTracker tracker fresh).global.nextPointerTag = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    unfold ProtectedTags.contains ProtectedTags.get at yes
    cases choose : tracker.global.protectedTags.entries.find?
      (fun row => row.1 == (allocatedTracker tracker fresh).global.nextPointerTag) with
    | none => simp [choose] at yes
    | some row =>
      have old := protectorsOld row (Array.mem_of_find?_eq_some choose)
      have accepted := Array.find?_some (p := fun row : BorTag × ProtectorKind =>
        row.1 == (allocatedTracker tracker fresh).global.nextPointerTag) choose
      rw [beq_iff_eq.mp accepted] at old
      exact UInt64.lt_asymm old nextAge
  obtain ⟨thread, active, cacheBound⟩ := admitted.stack.active
  have within (i : Nat) (position : thread.topUserRelevantFrame = some i) : i < frames.size+1 := by
    have bound := cacheBound i position
    simpa [stack, Array.size_push] using bound
  have k3 := admitted.initialTemporarySlot loaded compiler 3 (by decide) (by decide)
  have k4 := admitted.initialTemporarySlot loaded compiler 4 (by decide) (by decide)
  have k5 := admitted.initialTemporarySlot loaded compiler 5 (by decide) (by decide)
  have k13 := admitted.initialTemporarySlot loaded compiler 13 (by decide) (by decide)
  obtain ⟨result, final, updated, trace, resultBody, resultIdentity, resultFn, pc, boolValue, resultExtra,
    resultPlace, resultContinue, resultArgs, immediate, liveFinal, otherLive, tagFinal, hiddenFinal, dormantFinal, tracking, ghost, shallow, race, fixed, unchecked,
    noGc, addresses, types, backend, extras, finalActive, outputTransfer, sameAllocation, vacantAfter⟩ :=
    EmptyBackedPrefix.reaches_return options limits remaining dispatch calling span profile.preciseInteriorMutOff
      profile.implicitWritesOff profile.debugOff ProjectionMetadataFacts.nullComparator compilerSourceComparator
      dynamicFuel fuel sizing validation frames frame machine base start.bytes count nonzeroAddress positive id entry tag found cachedAddress holder node tagAt nodeAt
      nodeTag hidden dormant coherent cap room
      body identity callee location size unused admitted.resultSlot
      (by
        rw [data]
        simpa [RetagReferencePlace.sliceValue, EmptyReferenceMetadata.reference] using slot1)
      slot2
      (by simpa using k3) (by simpa using k4) (by simpa using k5) (by simpa using k13)
      admitted.immediateLocals tracker tracked mode fresh freshAgain nextAge unprotected (fun i node seen => allOld id entry i node found seen) admitted.stack.calleeClocksOff
      profile.ghostOff profile.shallow profile.raceOff profile.backendOff thread active within
      profile.compilerRuntime profile.noSyntheticSliceCache profile.unchecked profile.noGc profile.fixed
  let finalTracker := allocatedTracker (allocatedTracker tracker fresh) freshAgain
  refine ⟨result,final,updated,holder,finalTracker,?_⟩
  refine ⟨state.symm ▸ trace,resultBody.trans body,pc,boolValue,resultExtra,resultPlace,resultContinue,resultArgs,
    immediate,liveFinal,otherLive,tagFinal,hiddenFinal,dormantFinal,tracking,⟨tracker,tracked,rfl⟩,
    ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend.trans profile.backendOff,extras,finalActive,?_⟩
  refine ⟨entry, _, found, sameAllocation, outputTransfer, vacantAfter, ?_, ?_⟩
  · intro index data nodePresent
    have older := allOld id entry index data found nodePresent
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · intro eq
      rw [eq] at older
      exact UInt64.lt_irrefl _ older
    · intro eq
      rw [eq] at older
      exact UInt64.lt_asymm older nextAge
  · intro selected member
    change tracker.global.protectedTags.contains selected = false
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with eq | eq
    · subst selected
      apply Bool.eq_false_iff.mpr
      intro yes
      unfold ProtectedTags.contains ProtectedTags.get at yes
      cases choose : tracker.global.protectedTags.entries.find?
          (fun row => row.1 == tracker.global.nextPointerTag) with
      | none => simp [choose] at yes
      | some row =>
        have old := protectorsOld row (Array.mem_of_find?_eq_some choose)
        have accepted := Array.find?_some (p := fun row : BorTag × ProtectorKind =>
          row.1 == tracker.global.nextPointerTag) choose
        rw [beq_iff_eq.mp accepted] at old
        exact UInt64.lt_irrefl _ old
    · rw [eq]
      exact unprotected

#print axioms emptyBackedReachesReturn
end
end DuplicatePrefix.CanonicalCallDomain

import duplicate_prefix.RootMutableStep
import duplicate_prefix.CurrentTwoPhaseStructural
import duplicate_prefix.CurrentReferenceCore

namespace DuplicatePrefix.RootTwoPhaseComplete
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts PreparedArguments SourceDomain RootMutableStep

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

private theorem referenceSized : RootCompilerFacts.sliceLayout.layout.isSized = true := by
  decide +kernel

private theorem referenceTy : RootCompilerFacts.sliceLayout.ty = 1 := by
  decide +kernel

private theorem referenceRepresentation : RootCompilerFacts.sliceLayout.layout.backendRepr =
    .ScalarPair
      (a := .Initialized (value := .Pointer AddressSpace.ZERO) (validRange := ⟨1,18446744073709551615⟩))
      (b := .Initialized (value := .Int .I64 false) (validRange := ⟨0,18446744073709551615⟩))
      (bOffset := Size.ofBytes 8) := by
  with_unfolding_all rfl

/-- The actual positive-lane two-phase reference assignment advances to
the call terminator and produces initialized byte ownership at the child
tag. All hypotheses describe the compiler configuration, frame and
live ownership resources before the statement. -/
theorem assigned
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (older : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length base : UInt64) (parentTag : BorTag)
    (positive : 0 < length) (bounded : length ≤ 9223372036854775807)
    (valid : 16 < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨6,7⟩)
    (sourceCached : (frame.locals[1]'(by omega)).layout = some RootCompilerFacts.sliceLayout)
    (destLive : frame.locals[16].value = .live (.immediate .uninit))
    (destUncached : frame.locals[16].layout = none)
    (noClocks : frame.extra.dataRace = none) (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (storage : InitializedRegion (Storage.withCurrent older frame machine) length)
    (loan : ExclusiveRegion (Storage.withCurrent older frame machine) length storage parentTag)
    (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤
      storage.entry.allocation.extra.locations.size.bytes.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id, base⟩)
    (nonnull : base + storage.relativeStart.bytes ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).entries.any
      (·.value.ty == 2) = false)
    (cmp : ProjectionMetadataFacts.NullComparator) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let oldPointer := Pointer.new (.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))
    let oldValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base oldPointer length RootCompilerFacts.sliceLayout).imm
    let newTag := loan.tracker.global.nextPointerTag
    let newPointer := Pointer.new (.concrete storage.id newTag) oldPointer.offset
    let newValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base newPointer length RootCompilerFacts.sliceLayout).imm
    (frame.locals[1]'(by omega)).value = .live (.immediate oldValue) →
    ∃ (afterFrame : CompilerFrameContext.ActualFrame)
      (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      ExecutionMachine.step cfg limits () (Storage.withCurrent older frame machine) =
        (Storage.withCurrent older afterFrame afterMachine, .ok true) ∧
      afterFrame.location = .mir ⟨6,8⟩ ∧
      afterFrame.locals[16]? = some ⟨.live (.immediate newValue),some RootCompilerFacts.sliceLayout⟩ ∧
      afterFrame.body = frame.body ∧ afterFrame.bodyIdentity = frame.bodyIdentity ∧
      afterFrame.functionInstance = frame.functionInstance ∧ afterFrame.extra = frame.extra ∧
      afterFrame.locals.size = frame.locals.size ∧
      (∀ id, id ≠ 16 → afterFrame.locals[id]? = frame.locals[id]?) ∧
      afterMachine.user = machine.user ∧ afterMachine.dataRace = machine.dataRace ∧
      afterMachine.threads = machine.threads ∧
      (∀ key, key ≠ storage.id → afterMachine.memory.live[key]? = machine.memory.live[key]?) ∧
      (∃ (next : InitializedRegion (Storage.withCurrent older afterFrame afterMachine) length)
        (right : ExclusiveRegion (Storage.withCurrent older afterFrame afterMachine) length next newTag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        next.entry.allocation.extra.roots = #[root] ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        right.tracker.retagMode = loan.tracker.retagMode ∧
        loan.tracker.global.newPointerTag = .ok (right.tracker.global, newTag) ∧
        next.entry.allocation.extra = ExclusiveTwoPhaseRetag.reservationTree storage.entry.allocation.extra
          parentTag newTag storage.relativeStart (Size.ofBytes length) loan.tracker.global.protectedTags ∧
        next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra }) ∧
      afterFrame.trackCallerArg = frame.trackCallerArg ∧
      afterFrame.returnPlace = frame.returnPlace ∧ afterFrame.returnContinuation = frame.returnContinuation ∧
      afterFrame.vaList = frame.vaList ∧ afterFrame.localsIdentity = frame.localsIdentity := by
  intro cfg oldPointer oldValue newTag newPointer newValue arg
  let innerCfg := PreparedContracts.actualConfig options () remaining span
  have sameTarget : cfg.access.runtime = innerCfg.access.runtime := by
    unfold cfg innerCfg
    rw [actual_access_runtime, actual_access_runtime]
  let cached := cacheDestination frame valid
  have cachedSize : 16 < cached.locals.size := by
    simpa [cached, cacheDestination, LocalPlaces.cachePlaceLayout] using valid
  let stored := CurrentReferenceLocalWrite.written cached 16 oldValue cachedSize
  have storedSize : 16 < stored.locals.size := by
    simpa [stored, CurrentReferenceLocalWrite.written] using cachedSize
  let scope := scopeMachine machine loan.tracker
  let pre := Storage.withCurrent older stored scope
  let active := CurrentReferenceVisitor.ghost pre true
  let activeStorage : InitializedRegion active length :=
    {storage with live := storage.live}
  let activeTracker := {loan.tracker with retagMode := .TwoPhase}
  let activeLoan : ExclusiveRegion active length activeStorage parentTag :=
    {loan with tracker := activeTracker, tracked := rfl}
  obtain ⟨effect, retagged, stack, user, race, threads, unrelated, next, rights, idEq, offsetEq, roots, nextSize, _, advanced, exactTree, physical⟩ :=
    CurrentTwoPhaseStructural.retag options remaining span sizeFuel sizeBudget preciseOff implicitOff
      RootCompilerFacts.sliceLayout referenceTy active length base parentTag activeStorage activeLoan rfl
      address positive bounded tagRoom noRace root capacity extent cmp metadata noAlias
  have activeFrame : Storage.withCurrent older stored effect.machine = effect := by
    cases effect
    simp [active, pre, Storage.withCurrent] at stack ⊢
    exact stack.symm
  have liveSlot : stored.locals[16].value =
      .live (.immediate (RetagReferencePlace.sliceValue innerCfg.access.runtime.base oldPointer length
        RootCompilerFacts.sliceLayout).imm) := by
    simp [stored, CurrentReferenceLocalWrite.written, oldValue, sameTarget]
  have cachedSlot : stored.locals[16].layout = some RootCompilerFacts.sliceLayout := by
    simp [stored, CurrentReferenceLocalWrite.written,cached,cacheDestination,LocalPlaces.cachePlaceLayout]
  have retagEffect : innerCfg.validity.retagPointer ()
      (RetagReferencePlace.sliceValue innerCfg.access.runtime.base oldPointer length RootCompilerFacts.sliceLayout)
      RootCompilerFacts.sliceLayout.ty active =
      .ok (some (RetagReferencePlace.sliceValue innerCfg.access.runtime.base newPointer length
        RootCompilerFacts.sliceLayout)) (Storage.withCurrent older stored effect.machine) := by
    rw [activeFrame]
    exact retagged
  have validation := CurrentReferenceCore.validatePositive options remaining span fuel sizeFuel sizeBudget
    debugOff older stored scope effect.machine 16 storedSize RootCompilerFacts.sliceLayout true referenceTy referenceSized
    (.Pointer AddressSpace.ZERO) (.Int .I64 false) ⟨1,18446744073709551615⟩ ⟨0,18446744073709551615⟩
    (Size.ofBytes 8) referenceRepresentation storage.id parentTag newTag base storage.relativeStart.bytes length storage.entry
    address storage.live nonnull positive bounded storage.fits cachedSlot ghost (by rw [user]) shallow
    cmp metadata noAlias liveSlot retagEffect
  let written := CurrentReferenceLocalWrite.written stored 16 newValue storedSize
  let restored := {effect.machine with user := {effect.machine.user with payload := {effect.machine.user.payload with ghost := false}}}
  have validated : ValidityMachine.validateRuntime innerCfg.validity () (fuel+1)
      (LocalPlaces.localRuntimePlace older.size stored 16 RootCompilerFacts.sliceLayout) true pre =
        .ok () (Storage.withCurrent older written restored) := by
    simpa only [innerCfg, pre, written, restored, newValue, newPointer, oldPointer, Pointer.new, sameTarget] using validation
  have exactStep := stepOfValidation options limits remaining fuel span budget debugOff older frame written machine restored
    oldPointer length valid body identity callee located
    (by simpa [written,stored,cached,CurrentReferenceLocalWrite.written,cacheDestination,LocalPlaces.cachePlaceLayout] using located)
    sourceCached destLive destUncached noClocks loan.tracker rights.tracker loan.tracked rights.tracked ghost shallow arg validated
  let finalFrame := {written with location := FrameLocation.mir ⟨6,8⟩}
  let finalMachine := restoreMachine restored loan.tracker rights.tracker
  let final := Storage.withCurrent older finalFrame finalMachine
  have originalUser : finalMachine.user = machine.user := by
    have effectUser : effect.machine.user =
        {machine.user with payload := {machine.user.payload with ghost := true}} := user
    change {effect.machine.user with payload := {effect.machine.user.payload with ghost := false}} = machine.user
    rw [effectUser]
    have clear (current : Machine.RootUser) (off : current.payload.ghost = false) :
        {current with payload := {current.payload with ghost := false}} = current := by
      cases current with
      | mk addresses payload alignment =>
        cases payload
        simp only at off
        cases off
        rfl
    exact clear machine.user ghost
  refine ⟨finalFrame,finalMachine,exactStep,rfl,?_,rfl,rfl,rfl,rfl,?_,?_,originalUser,race.trans noRace.symm,threads,unrelated,?_,rfl,rfl,rfl,rfl,rfl⟩
  · simp [finalFrame,written,stored,cached,cacheDestination,LocalPlaces.cachePlaceLayout,CurrentReferenceLocalWrite.written,storedSize]
  · simp [finalFrame,written,stored,cached,cacheDestination,LocalPlaces.cachePlaceLayout,CurrentReferenceLocalWrite.written]
  · intro id different
    simp [finalFrame,written,stored,cached,cacheDestination,LocalPlaces.cachePlaceLayout,CurrentReferenceLocalWrite.written,
      Array.getElem?_set,Ne.symm different]
  let finalStorage : InitializedRegion final length := {next with live := next.live}
  let finalTracker := {rights.tracker with retagMode := loan.tracker.retagMode}
  let finalRights : ExclusiveRegion final length finalStorage newTag :=
    {rights with tracker := finalTracker, tracked := rfl}
  exact ⟨finalStorage,finalRights,idEq,offsetEq,roots,nextSize,rfl,advanced,exactTree,physical⟩

end DuplicatePrefix.RootTwoPhaseComplete

#print axioms DuplicatePrefix.RootTwoPhaseComplete.assigned

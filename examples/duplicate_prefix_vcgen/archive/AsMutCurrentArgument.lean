import duplicate_prefix.AsMutCurrentInstall
import duplicate_prefix.CurrentAsMutStrong
import duplicate_prefix.CurrentReferenceCore
import duplicate_prefix.ScopedFrame

namespace DuplicatePrefix.AsMutCurrentArgument
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts PreparedArguments SourceDomain ActualReferenceMetadata

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- The pushed scope's FnEntry argument installs and validates the actual
strong borrow before the helper begins. The returned footprint is from
the same fresh tag, allocation and range as the installed local. -/
theorem install
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
    (valid : 1 < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (dead : frame.locals[1].value = .dead) (uncached : frame.locals[1].layout = none)
    (ledger : FrameState) (frameLedger : frame.extra.borrowTracker = some ledger)
    (noClocks : frame.extra.dataRace = none) (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (storage : InitializedRegion (Storage.withCurrent older frame machine) length)
    (loan : ExclusiveRegion (Storage.withCurrent older frame machine) length storage parentTag)
    (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id, base⟩)
    (nonnull : base + storage.relativeStart.bytes ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older frame machine)).entries.any
      (·.value.ty == 2) = false)
    (cmp : ProjectionMetadataFacts.NullComparator) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let h := ExecutionMachine.callHooks cfg limits
    let atAddress := Size.ofBytes (base + storage.relativeStart.bytes)
    let oldPointer := Pointer.new (.concrete storage.id parentTag) atAddress
    let oldValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base oldPointer length reference).imm
    let tag := loan.tracker.global.nextPointerTag
    let newValue := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete storage.id tag) atAddress) length reference).imm
    ∃ (afterFrame : CompilerFrameContext.ActualFrame)
      (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      h.withRetagMode () .FnEntry (AsMutCurrentInstall.action h oldValue) (Storage.withCurrent older frame machine) =
        .ok (1,1) (Storage.withCurrent older afterFrame afterMachine) ∧
      afterFrame.extra.borrowTracker = some (ledger.addProtector storage.id tag) ∧
      afterFrame.locals[1]? = some ⟨.live (.immediate newValue), some reference⟩ ∧
      afterFrame.returnPlace = frame.returnPlace ∧ afterFrame.returnContinuation = frame.returnContinuation ∧
      afterFrame.body = frame.body ∧ afterFrame.bodyIdentity = frame.bodyIdentity ∧ afterFrame.functionInstance = frame.functionInstance ∧
      afterFrame.extra.dataRace = frame.extra.dataRace ∧ afterFrame.locals.size = frame.locals.size ∧
      afterFrame.vaList = frame.vaList ∧
      (∀ i, i ≠ 1 → afterFrame.locals[i]? = frame.locals[i]?) ∧
      afterMachine.user = machine.user ∧ afterMachine.dataRace = none ∧
      afterMachine.threads = machine.threads ∧
      ∃ (next : InitializedRegion (Storage.withCurrent older afterFrame afterMachine) length)
        (right : ExclusiveRegion (Storage.withCurrent older afterFrame afterMachine) length next tag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        right.tracker.retagMode = loan.tracker.retagMode ∧
        next.entry.allocation.extra.roots = #[root] ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        (∃ node, next.entry.allocation.extra.nodeAt right.source = some node ∧ node.tag = tag ∧ node.isExposed = false) ∧
        RetagReleaseFootprint.MaterializedWithin next.entry.allocation.extra right.source
          next.relativeStart.bytes (next.relativeStart.bytes + length) ∧
        RetagReleaseFootprint.VacantRows next.entry.allocation.extra := by
  intro cfg h atAddress oldPointer oldValue tag newValue
  let innerCfg := PreparedContracts.actualConfig options () remaining span
  have target : cfg.access.runtime = innerCfg.access.runtime := by
    unfold cfg innerCfg
    rw [actual_access_runtime, actual_access_runtime]
  let cached := AsMutCurrentInstall.cacheFrame frame valid
  have vc : 1 < cached.locals.size := by simpa [cached,AsMutCurrentInstall.cacheFrame,AsMutCurrentInstall.spanFrame,LocalOperands.cachedLayoutFrame] using valid
  let live := CurrentReferenceLocalWrite.written cached 1 .uninit vc
  have vl : 1 < live.locals.size := by simpa [live,CurrentReferenceLocalWrite.written] using vc
  let stored := CurrentReferenceLocalWrite.written live 1 oldValue vl
  have vs : 1 < stored.locals.size := by simpa [stored,CurrentReferenceLocalWrite.written] using vl
  let scope := ScopedFrame.entered machine loan.tracker .FnEntry
  let pre := Storage.withCurrent older stored scope
  let active := CurrentReferenceVisitor.ghost pre true
  let activeStorage : InitializedRegion active length :=
    {storage with live := storage.live}
  let activeTracker := {loan.tracker with retagMode := .FnEntry}
  let activeLoan : ExclusiveRegion active length activeStorage parentTag :=
    {loan with tracker := activeTracker, tracked := rfl}
  have current : active.stack.currentFrame? = some stored := by
    simp [active,pre,Storage.withCurrent,Stack.currentFrame?]
  let tagged := {stored with extra := {stored.extra with borrowTracker := some (ledger.addProtector storage.id tag)}}
  obtain ⟨effect, retagged, stack, user, race, threads, next, rights, idEq, offsetEq, roots, nextSize, node, materialized, vacant⟩ :=
    CurrentAsMutStrong.retag options remaining span sizeFuel sizeBudget preciseOff implicitOff reference reference_ty
      active length base parentTag activeStorage activeLoan rfl stored ledger current frameLedger callee
      address positive bounded tagRoom noRace root capacity extent cmp metadata noAlias
  have exactStack : Storage.withCurrent older tagged effect.machine = effect := by
    cases effect
    simp [tagged,active,pre,Storage.withCurrent] at stack ⊢
    exact stack.symm
  have liveLoc : stored.locals[1].value =
      .live (.immediate (RetagReferencePlace.sliceValue innerCfg.access.runtime.base oldPointer length reference).imm) := by
    simp [stored,CurrentReferenceLocalWrite.written,oldValue,target]
  have cachedLoc : stored.locals[1].layout = some reference := by
    simp [stored,live,cached,CurrentReferenceLocalWrite.written,AsMutCurrentInstall.cacheFrame,AsMutCurrentInstall.spanFrame,LocalOperands.cachedLayoutFrame]
  have coherentRetag : innerCfg.validity.retagPointer ()
      (RetagReferencePlace.sliceValue innerCfg.access.runtime.base oldPointer length reference)
      reference.ty active =
      .ok (some (RetagReferencePlace.sliceValue innerCfg.access.runtime.base
        (Pointer.new (.concrete storage.id tag) atAddress) length reference))
        (Storage.withCurrent older tagged effect.machine) := by
    rw [exactStack]
    exact retagged
  obtain ⟨pa,pb,ra,rb,n,repr⟩ := reference_repr
  have validation := CurrentReferenceCore.validatePositiveAcrossFrame options remaining span fuel sizeFuel sizeBudget
    debugOff older stored tagged scope effect.machine 1 vs reference true reference_ty reference_sized pa pb ra rb n repr
    storage.id parentTag tag base storage.relativeStart.bytes length storage.entry address storage.live nonnull
    positive bounded storage.fits rfl rfl cachedLoc ghost (by rw [user]) shallow cmp metadata noAlias liveLoc coherentRetag
  let vt : 1 < tagged.locals.size := vs
  let written := CurrentReferenceLocalWrite.written tagged 1 newValue vt
  let restored := {effect.machine with user := {effect.machine.user with payload := {effect.machine.user.payload with ghost := false}}}
  have priorCached : cached.locals[1].layout = some reference := by
    simp [cached, AsMutCurrentInstall.cacheFrame, LocalOperands.cachedLayoutFrame]
  have priorDead : cached.locals[1].value = .dead := by
    simpa [cached, AsMutCurrentInstall.cacheFrame, AsMutCurrentInstall.spanFrame, LocalOperands.cachedLayoutFrame] using dead
  have sameDest : LocalPlaces.localRuntimePlace older.size live 1 reference =
      LocalPlaces.localRuntimePlace older.size stored 1 reference := rfl
  have machineInitialized : ValidityMachine.validateRuntime innerCfg.validity () options.limits.validation
      (LocalPlaces.localRuntimePlace older.size live 1 reference) true pre =
        .ok () (Storage.withCurrent older written restored) := by
    rw [budget, sameDest]
    simpa only [innerCfg, pre, written, restored, newValue, atAddress, target] using validation
  have copied := AsMutPassArgument.copy options limits remaining span debugOff older cached scope body vc
      priorDead priorCached noClocks ghost shallow oldValue (Storage.withCurrent older written restored) machineInitialized
  have installed := AsMutCurrentInstall.install_of_copy options limits (remaining+1) span older frame scope
    body identity callee valid uncached oldValue (Storage.withCurrent older written restored) copied
  have scopeAction := ScopedFrame.changed_state (AsMutCurrentInstall.action h oldValue)
    (Storage.withCurrent older frame machine) (Storage.withCurrent older written restored)
    loan.tracker rights.tracker .FnEntry (1,1) loan.tracked rights.tracked installed
  let releasedMode := {rights.tracker with retagMode := loan.tracker.retagMode}
  let finalMachine := {restored with borrowTracker := some releasedMode}
  let final := Storage.withCurrent older written finalMachine
  have stableUser : finalMachine.user = machine.user := by
    have effectUser : effect.machine.user =
        {machine.user with payload := {machine.user.payload with ghost := true}} := user
    change {effect.machine.user with payload := {effect.machine.user.payload with ghost := false}} = machine.user
    rw [effectUser]
    have clear (value : Machine.RootUser) (off : value.payload.ghost = false) :
        {value with payload := {value.payload with ghost := false}} = value := by
      cases value with
      | mk addresses payload alignment =>
        cases payload
        simp_all
    exact clear machine.user ghost
  refine ⟨written,finalMachine,scopeAction,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,?_,stableUser,race,threads,?_⟩
  · simp [written, tagged, stored, live, cached,CurrentReferenceLocalWrite.written,AsMutCurrentInstall.cacheFrame,AsMutCurrentInstall.spanFrame,LocalOperands.cachedLayoutFrame]
  · simp [written, tagged, stored, live, cached,CurrentReferenceLocalWrite.written,AsMutCurrentInstall.cacheFrame,AsMutCurrentInstall.spanFrame,LocalOperands.cachedLayoutFrame]
  · intro i different
    simp [written, tagged, stored, live, cached,CurrentReferenceLocalWrite.written,AsMutCurrentInstall.cacheFrame,AsMutCurrentInstall.spanFrame,LocalOperands.cachedLayoutFrame,Ne.symm different]
  let resultStorage : InitializedRegion final length := {next with live := next.live}
  let resultRights : ExclusiveRegion final length resultStorage tag :=
    {rights with tracker := releasedMode, tracked := rfl}
  exact ⟨resultStorage,resultRights,idEq,offsetEq,rfl,roots,nextSize,node,materialized,vacant⟩

end DuplicatePrefix.AsMutCurrentArgument

#print axioms DuplicatePrefix.AsMutCurrentArgument.install

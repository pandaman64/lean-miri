import duplicate_prefix.PushThread
import duplicate_prefix.AsMutCurrentEntry
import duplicate_prefix.AsMutCurrentArgument

namespace DuplicatePrefix.AsMutPreparedEntry
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain ActualReferenceMetadata

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

private theorem rawSize (options : EvalConfigurationCore.Options) (before : RootState) (dest : RuntimeStackPlace Provenance) :
    (AsMutCurrentEntry.rawFrame options before dest).locals.size = 5 := by
  with_unfolding_all rfl

theorem prepared
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (budget : options.limits.validation = fuel+1)
    (sizeBudget : options.place.dynamicFuel = sizeFuel+1)
    (debugOff : options.place.debugAssertions = false)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (older : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length base : UInt64) (parentTag : BorTag)
    (positive : 0 < length) (bounded : length ≤ 9223372036854775807)
    (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (storage : InitializedRegion (Storage.withCurrent older caller machine) length)
    (loan : ExclusiveRegion (Storage.withCurrent older caller machine) length storage parentTag)
    (root : UniIndex)
    (capacity : CurrentTwoPhaseStructural.InsertionCapacity storage.entry.allocation.extra loan.source root
      loan.tracker.global.nextPointerTag)
    (tagRoom : loan.tracker.global.nextPointerTag.value ≠ 18446744073709551615)
    (extent : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id, base⟩)
    (nonnull : base + storage.relativeStart.bytes ≠ 0)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent older caller machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent older caller machine)).entries.any
      (·.value.ty == 2) = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (old : Immediate Provenance) (destIndex : MIR.LocalId) (destValid : destIndex < caller.locals.size)
    (destCached : caller.locals[destIndex].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : caller.locals[destIndex].value = .live (.immediate old))
    (noClocks : caller.extra.dataRace = none)
    (thread : ThreadRecord) (index : Nat) (relevant : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let h := ExecutionMachine.callHooks cfg limits
    let before := Storage.withCurrent older caller machine
    let dest := (LocalPlaces.localRuntimePlace older.size caller destIndex CopyCompilerFacts.destPointerLayout).stackView
    let tag := loan.tracker.global.nextPointerTag
    let ptr := Pointer.new (.concrete storage.id parentTag) (Size.ofBytes (base + storage.relativeStart.bytes))
    let child := Pointer.new (.concrete storage.id tag) ptr.offset
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base ptr length reference).imm
    let expected := (RetagReferencePlace.sliceValue cfg.access.runtime.base child length reference).imm
    FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates before dest).stack
      thread.topUserRelevantFrame = some index →
    (AsMutPush.pushed options.userRelevantCrates before dest).stack.frames[index]? = some relevant →
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      AsMutCallCore.core h ⟨.immediate value,reference⟩ dest before =
        .ok () (Storage.withCurrent (older.push caller) frame after) ∧
      frame.location = .mir ⟨0,0⟩ ∧ frame.body = HelperCompilerFacts.asMutPtrBody.body ∧
      frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity ∧ frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee ∧
      frame.returnPlace = dest ∧ frame.returnContinuation = .goto (some 7) .Unreachable ∧
      frame.extra.dataRace = none ∧ frame.locals.size = 5 ∧ frame.vaList = #[] ∧
      frame.extra.borrowTracker = some (({} : FrameState).addProtector storage.id tag) ∧
      frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩ ∧
      frame.locals[1]? = some ⟨.live (.immediate expected), some reference⟩ ∧
      (∀ localId, 2 ≤ localId → localId < 5 → frame.locals[localId]? = some ⟨.dead, none⟩) ∧
      after.user.payload.ghost = false ∧ after.user.payload.validation = .Shallow ∧ after.dataRace = none ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.payload.user.host = machine.user.payload.payload.user.host ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      after.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      after.threads.activeThread? = some (PushThread.after thread (older.push caller).size
        (AsMutCurrentEntry.rawFrame options before dest).extra.userRelevance relevant.extra.userRelevance) ∧
      (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) frame after)).metadata =
        PreparedReflection.actual.runtime ∧
      (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) frame after)).entries.any
        (·.value.ty == 2) = false ∧
      ∃ (next : InitializedRegion (Storage.withCurrent (older.push caller) frame after) length)
        (right : ExclusiveRegion (Storage.withCurrent (older.push caller) frame after) length next tag),
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        right.tracker.retagMode = loan.tracker.retagMode ∧
        next.entry.allocation.extra.roots = #[root] ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        (∃ node, next.entry.allocation.extra.nodeAt right.source = some node ∧ node.tag = tag ∧ node.isExposed = false) ∧
        RetagReleaseFootprint.MaterializedWithin next.entry.allocation.extra right.source
          next.relativeStart.bytes (next.relativeStart.bytes + length) ∧
        RetagReleaseFootprint.VacantRows next.entry.allocation.extra ∧
        next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } := by
  intro cfg h before dest tag ptr child value expected top populated
  let raw := AsMutCurrentEntry.rawFrame options before dest
  let pushed := (AsMutPush.completed options.userRelevantCrates before dest relevant).machine
  let stage := Storage.withCurrent (older.push caller) raw pushed
  have retainedMemory : pushed.memory = machine.memory := by
    simp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> rfl
  have retainedTracker : pushed.borrowTracker = machine.borrowTracker := by
    simp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> rfl
  have retainedGhost : pushed.user.payload.ghost = false := by
    simp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact ghost
  have retainedShallow : pushed.user.payload.validation = .Shallow := by
    simp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact shallow
  have retainedAddress : pushed.user.addresses = machine.user.addresses := by
    simp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> rfl
  have retainedRace : pushed.dataRace = none := by
    simp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact noRace
  have retainedMetadata : (EvalProjectionMachine.arrays.get stage).metadata = PreparedReflection.actual.runtime := by
    simp only [stage,pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact metadata
  have retainedNoAlias : (EvalProjectionMachine.arrays.get stage).entries.any (·.value.ty == 2) = false := by
    simp only [stage,pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact noAlias
  let liveStorage : InitializedRegion stage length :=
    {storage with live := by change pushed.memory.live[storage.id]? = _; rw [retainedMemory]; exact storage.live}
  let liveLoan : ExclusiveRegion stage length liveStorage parentTag :=
    {loan with tracked := by change pushed.borrowTracker = _; rw [retainedTracker]; exact loan.tracked}
  have originalTracker : machine.borrowTracker = some loan.tracker := loan.tracked
  have ledger : raw.extra.borrowTracker = some ({} : FrameState) := by
    simp [raw, AsMutCurrentEntry.rawFrame, AsMutFrame.rawFrame, AsMutPush.fresh,
      CallEntryFacts.freshRoot,before,Storage.withCurrent,originalTracker]
  have clocks : raw.extra.dataRace = none := by
    simp [raw, AsMutCurrentEntry.rawFrame, AsMutFrame.rawFrame, AsMutPush.fresh,
      CallEntryFacts.freshRoot,before,Storage.withCurrent,noRace]
  have size : raw.locals.size = 5 := rawSize options before dest
  have v : 1 < raw.locals.size := by rw [size]; decide
  obtain ⟨installed, after, exactInstall, owned, i1, saved, continuation, body, identity, callee, clock, installedSize, varargs, kept,
    user, race, threads, next, rights, idEq, offsetEq, sameMode, roots, nextSize, node, materialized, vacant, allocationFrame⟩ :=
    AsMutCurrentArgument.install options limits remaining fuel sizeFuel span budget sizeBudget debugOff preciseOff implicitOff
      (older.push caller) raw pushed length base parentTag positive bounded v rfl rfl rfl
      (by with_unfolding_all rfl) (by with_unfolding_all rfl) {} ledger clocks retainedRace
      retainedGhost retainedShallow liveStorage liveLoan root capacity tagRoom extent
      (by rw [retainedAddress]; exact address) nonnull retainedMetadata retainedNoAlias cmp
  have valid0 : 0 < installed.locals.size := by rw [installedSize,size]; decide
  have zero := kept 0 (by decide)
  have zeroDead : installed.locals[0].value = .dead := by
    rw [Array.getElem?_eq_getElem valid0] at zero
    have raw0 : raw.locals[0]? = some ⟨.dead,none⟩ := by with_unfolding_all rfl
    rw [raw0] at zero
    exact congrArg (·.value) (Option.some.inj zero)
  have total := AsMutCurrentEntry.coreOfInstall options limits (remaining+1) span debugOff older caller installed
    machine after destIndex destValid old value destCached destLive noClocks ghost thread index relevant active
    top populated exactInstall body identity callee valid0 zeroDead (clock.trans clocks)
  let entered := AsMutCurrentEntry.done installed
  let state := Storage.withCurrent (older.push caller) entered after
  have retainedReturn : entered.returnPlace = dest := saved
  have retainedContinuation : entered.returnContinuation = .goto (some 7) .Unreachable := continuation
  have sameExtras : after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    rw [user]
    simp only [pushed, AsMutPush.completed, AsMutPush.fresh, CallEntryFacts.freshRoot,
      GenericPushRelevance.afterPush, Storage.withCurrent]
    split <;> rfl
  refine ⟨entered,after,total,rfl,body,identity,callee,retainedReturn,retainedContinuation,clock.trans clocks,?_,?_,
    owned,?_,?_,?_,?_,?_,race,?_,?_,?_,sameExtras,?_,?_,?_,?_,?_⟩
  · simpa [entered,AsMutCurrentEntry.done,AsMutDone.doneFrame,CallEntryFacts.liveSlot] using installedSize.trans size
  · change installed.vaList = #[]
    exact varargs
  · have raw0 : raw.locals[0]? = some ⟨.dead,none⟩ := by with_unfolding_all rfl
    simp only [entered,AsMutCurrentEntry.done,AsMutDone.doneFrame,CallEntryFacts.liveSlot,
      Array.getElem?_modify, ite_eq_left rfl, kept 0 (by decide), raw0]
    rfl
  · simpa [entered,AsMutCurrentEntry.done,AsMutDone.doneFrame,CallEntryFacts.liveSlot,Array.getElem?_modify, expected,child,ptr,Pointer.new] using i1
  · intro localId lo hi
    have eq : raw.locals[localId]? = some ⟨.dead,none⟩ := by
      have is2or3or4 : localId = 2 ∨ localId = 3 ∨ localId = 4 := by omega
      rcases is2or3or4 with rfl|rfl|rfl <;> with_unfolding_all rfl
    simpa [entered,AsMutCurrentEntry.done,AsMutDone.doneFrame,CallEntryFacts.liveSlot,Array.getElem?_modify,
      show 0 ≠ localId by omega, kept localId (by omega)] using eq
  · rw [user]; exact retainedGhost
  · rw [user]; exact retainedShallow
  · rw [user,retainedAddress]
  · rw [user]
    simp only [pushed, AsMutPush.completed, AsMutPush.fresh, CallEntryFacts.freshRoot,
      GenericPushRelevance.afterPush, Storage.withCurrent]
    split <;> rfl
  · rw [user]
    simp only [pushed, AsMutPush.completed, AsMutPush.fresh, CallEntryFacts.freshRoot,
      GenericPushRelevance.afterPush, Storage.withCurrent]
    split <;> rfl
  · rw [threads]
    simp only [pushed,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> rfl
  · rw [threads]
    let fresh := (AsMutPush.fresh before.machine).1
    let rank := raw.extra.userRelevance
    let oldRank := relevant.extra.userRelevance
    exact PushThread.active_after fresh thread before.stack.frames.size rank oldRank active
  · change (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) raw after)).metadata = _
    simp only [Storage.withCurrent,EvalProjectionMachine.arrays,user]
    exact retainedMetadata
  · change (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push caller) raw after)).entries.any (·.value.ty == 2) = _
    simp only [Storage.withCurrent,EvalProjectionMachine.arrays,user]
    exact retainedNoAlias
  let nextStorage : InitializedRegion state length := {next with live := next.live}
  let rawRights : ExclusiveRegion state length nextStorage tag := {rights with tracked := rights.tracked}
  exact ⟨nextStorage,rawRights,idEq,offsetEq,sameMode,roots,nextSize,node,materialized,vacant,allocationFrame⟩

end DuplicatePrefix.AsMutPreparedEntry

#print axioms DuplicatePrefix.AsMutPreparedEntry.prepared

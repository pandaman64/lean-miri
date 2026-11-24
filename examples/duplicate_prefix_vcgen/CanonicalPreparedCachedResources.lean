import CanonicalPreparedPhysicalResources
import VerifyAllCountCanonical
import CanonicalCachedReturn
import duplicate_prefix.ActiveStackReleaseExclusive

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open SourceDomain PreparedArguments CanonicalConfigFacts
open GeneralRangeMapOrigins ArchiveForestProjection RetagReleaseFootprint
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem nonemptyCached
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (dynamic : options.place.dynamicFuel = sizeFuel+1) (dispatchFuel : limits.callDispatch = dispatch+1)
    (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) (positive : 0 < length)
    (admitted : Admitted program options remaining preparedTagHeadroom span
      before frame pointer length count)
    (compiler : InitialCompilerControl before frame)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (destination : CachedBoolDestination before frame)
    (ledger : ∃ owned, frame.extra.borrowTracker = some owned ∧ owned.protectedTags = argumentLedger pointer)
    (resource : ∀ id tag, pointer.provenance = some (.concrete id tag) →
      ∀ entry, before.machine.memory.live[id]? = some entry → CopySourceResources entry) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits
      before := by
  have nonempty : length ≠ 0 := by
    intro equal
    rw [equal] at positive
    exact UInt64.lt_irrefl _ positive
  obtain ⟨older, caller, stack, ⟨ready⟩⟩ := admitted.cachedActiveCaller nonempty destination ledger
  let machine := before.machine
  have state : before = Storage.withCurrent (older.push caller) frame machine := by
    cases before with
    | mk callStack m =>
      cases callStack with
      | mk data =>
        change data = (older.push caller).push frame at stack
        cases stack
        rfl
  obtain ⟨storage,tag,base,loan,owned,concrete,pointerNat,address,frameLedger,_,_,⟨node,found,hidden⟩,scope⟩ :=
    admitted.sliceProtector nonempty
  obtain ⟨root,roots⟩ := scope.root nonempty
  have live : machine.memory.live[storage.id]? = some storage.entry := storage.live
  have addr : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) =
      some ⟨storage.id,base⟩ := address
  have pointerSum : base.toNat + storage.relativeStart.bytes.toNat < 2^64 := by
    have declared := admitted.allocations.regionAddresses ⟨storage.id,base⟩
      (Array.mem_of_find?_eq_some address) storage.entry live
    have fits := storage.fits
    change base.toNat + storage.entry.allocation.byteSize.bytes.toNat < 2^64 at declared
    omega
  have pointerBytes : pointer.offset.bytes = base+storage.relativeStart.bytes := by
    apply UInt64.toNat.inj
    rw [pointerNat,UInt64.toNat_add,Nat.mod_eq_of_lt pointerSum]
  have nonnull : base + storage.relativeStart.bytes ≠ 0 := by
    rw [← pointerBytes]
    exact admitted.slice.nonnull
  have available := resource storage.id tag concrete storage.entry live
  have owners := RetagReleaseRights.region_owned _ length storage tag loan scope.extent
  have mem : machine.memory.live.contains storage.id = true := by
    simp [Std.ExtTreeMap.contains_eq_isSome_getElem?,live]
  obtain ⟨extra,foundExtra,noneWeak,noSync⟩ := admitted.allocations.extras storage.id mem
  have extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) =
      some (storage.id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) storage.id)}) := by
    change machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) = some (storage.id,extra) at foundExtra
    have same := AllocationBacktrace.of_lookup foundExtra
    rw [same,foundExtra]
    congr 2
    cases extra
    simp_all
  have frameLedgerEq : owned = ready.owned := Option.some.inj (frameLedger.symm.trans ready.ownership)
  have actualLedger : owned.protectedTags = #[(storage.id,tag)] := by
    obtain ⟨row, rowEq, rows⟩ := ledger
    rw [show owned = row from Option.some.inj (frameLedger.symm.trans rowEq),rows,argumentLedger,concrete]
  have pair : (storage.id,tag) = (ready.id,ready.tag) := by
    rw [frameLedgerEq,ready.ownedTags] at actualLedger
    exact List.cons.inj (congrArg Array.toList actualLedger).symm |>.1
  have sameId : storage.id = ready.id := congrArg Prod.fst pair
  have sameTag : tag = ready.tag := congrArg Prod.snd pair
  have equalEntry : storage.entry = ready.entry := by
    have same := live
    rw [sameId,ready.present] at same
    exact Option.some.inj same.symm
  have sameRoot : root = ready.root := by
    have saved := roots
    rw [equalEntry,ready.roots] at saved
    exact List.cons.inj (congrArg Array.toList saved).symm |>.1
  have sameHolder : loan.source = ready.source := by
    have selected := loan.tagKnown
    have key := congrArg (fun t => ready.entry.allocation.extra.indexOfTag t) sameTag
    have actual : ready.entry.allocation.extra.indexOfTag tag = some loan.source :=
      (congrArg (fun a : LocalAllocation Provenance BorrowTree MiriMemoryKind => a.allocation.extra.indexOfTag tag)
        equalEntry).symm.trans selected
    exact Option.some.inj (actual.symm.trans (key.trans ready.indexed))
  obtain ⟨immediate,rebuilt,sourceSlot,_⟩ := admitted.initialArgumentSlots
  have raw := RootZeroShallowReturn.concreteSliceImmediate pointer storage.id tag base storage.relativeStart.bytes length concrete pointerBytes
  have immediateEq := Except.ok.inj (rebuilt.symm.trans raw)
  rw [immediateEq, ← actual_access_runtime options () (remaining+1) span] at sourceSlot
  let storageNow : InitializedRegion (Storage.withCurrent (older.push caller) frame machine) length :=
    ⟨storage.id,storage.relativeStart,storage.entry,live,storage.writable,storage.backed,storage.fits,storage.initialized⟩
  rw [state] at admitted compiler ⊢
  exact RootZeroShallowReturn.allCountsFromCanonicalAdmitted options limits remaining sizeFuel span fuel validation
    older caller frame machine count loan.tracker loan.tracked dynamic storage.id tag loan.source root base
    storage.relativeStart.bytes length storage.entry addr positive nonnull loan.coherent node found roots loan.tagKnown
    scope.extent owners scope.materializedWithin sourceSlot
    ready sameId sameRoot sameHolder sameTag hidden dispatch dispatchFuel program loaded pointer
    admitted compiler storageNow rfl rfl rfl available.keys available.room statementFuel outerRank innerRank
    available.maskLength available.mask available.provenance available.storageBound extras

#print axioms nonemptyCached
end DuplicatePrefix.CanonicalCallDomain

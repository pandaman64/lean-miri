import VerifyAllCountCanonicalPhysical
import duplicate_prefix.ActiveStackReleaseExclusive

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open SourceDomain PreparedArguments CanonicalConfigFacts
open GeneralRangeMapOrigins ArchiveForestProjection RetagReleaseFootprint
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The initialized source allocation retains enough dense key capacity and
well-formed physical backing for this compiled function's actual accesses. -/
structure CopySourceResources (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) : Prop where
  keys : RetagInsertionCapacity.Ready entry.allocation.extra
  dense : entry.allocation.extra.tagMapping.deassigned = #[]
  room : entry.allocation.extra.nodes.size + 3 < 2^32
  maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize
  mask : InitMaskCopy.WellFormed entry.allocation.initializationMask
  provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  storageBound : entry.allocation.len + 64 < 18446744073709551616

theorem nonemptyPhysical
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (dynamic : options.place.dynamicFuel = sizeFuel+1) (dispatchFuel : limits.callDispatch = dispatch+1)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) (positive : 0 < length)
    (admitted : Admitted program options remaining preparedTagHeadroom span
      (Storage.withCurrent #[] frame machine) frame pointer length count)
    (compiler : InitialCompilerControl (Storage.withCurrent #[] frame machine) frame)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (resource : ∀ id tag, pointer.provenance = some (.concrete id tag) →
      ∀ entry, machine.memory.live[id]? = some entry → CopySourceResources entry) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent #[] frame machine) := by
  have nonempty : length ≠ 0 := by
    intro equal
    rw [equal] at positive
    exact UInt64.lt_irrefl _ positive
  obtain ⟨storage,tag,base,loan,_,concrete,pointerNat,address,_,_,_,⟨node,found,_⟩,scope⟩ :=
    admitted.sliceProtector nonempty
  obtain ⟨root,roots⟩ := scope.root
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
  exact RootZeroShallowReturn.allCountsFromCanonicalPhysical options limits remaining sizeFuel span fuel validation
    frame machine count loan.tracker loan.tracked dynamic storage.id tag loan.source root base
    storage.relativeStart.bytes length storage.entry addr positive nonnull loan.coherent node found roots loan.tagKnown
    scope.extent owners scope.materializedWithin dispatch dispatchFuel available.dense program loaded pointer concrete
    pointerBytes admitted compiler storage rfl rfl rfl available.keys available.room statementFuel outerRank innerRank
    available.maskLength available.mask available.provenance available.storageBound extras

#print axioms nonemptyPhysical

end DuplicatePrefix.CanonicalCallDomain

import RootAliasedReturnAfterCopy
import duplicate_prefix.RootPositiveCopyFromBB7
import duplicate_prefix.CopyRootPositiveRoundtripExact
import duplicate_prefix.RootPositiveReturnContinuation
import duplicate_prefix.InitializedRegionPrefix

namespace DuplicatePrefix.RootPositiveWithSharedOutput
open Miri Miri.ABI Miri.MIR Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.Concurrency Miri.DataStructures
open PreparedArguments SourceDomain CopyRootPositiveRoundtrip PhysicalDestinationAfterCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false

theorem completes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (incoming : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      before (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) frame machine))
    (length count base : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) frame machine) length)
    (rights : ExclusiveRegion (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) frame machine) length storage tag)
    (positive : 0 < count.toNat) (countFits : count.toNat < 2^63)
    (disjoint : count.toNat + count.toNat ≤ length.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id,base⟩)
    (size : frame.locals.size = 25)
    (pointerSlot : frame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes)))))),
      some CopyCompilerFacts.destPointerLayout⟩)
    (temp16 : Immediate Provenance)
    (live16 : (frame.locals[16]'(by omega)).value = .live (.immediate temp16))
    (countSlot : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (unused : ∀i(v:i<frame.locals.size),17≤i→i≤23→(frame.locals[i]'v)=⟨.dead,none⟩)
    (unused24 : frame.locals[24]? = some ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,0⟩) (noClocks : frame.extra.dataRace = none)
    (mode : rights.tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (all : CopyHelperCleanup.AllImmediate frame) (noRace : machine.dataRace = none)
    (trackNone : frame.trackCallerArg = none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some 0) (relevant : frame.extra.userRelevance > 0)
    (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (source : PreparedContracts.SourceComparator)
    (outerRank : LanguageZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (innerRank : RuntimeZeroEntryFacts.rank options.userRelevantCrates < frame.extra.userRelevance)
    (maskLen : storage.entry.allocation.initializationMask.len = storage.entry.allocation.byteSize)
    (maskValid : InitMaskCopy.WellFormed storage.entry.allocation.initializationMask)
    (provenance : ProvenanceCopy.WellFormed storage.entry.allocation.provenanceMap storage.entry.allocation.len)
    (storageFits : storage.entry.allocation.len+64 < 18446744073709551616)
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (rangeCapacity : storage.relativeStart.bytes.toNat+length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == storage.id) =
      some (storage.id, {weakMemory := none, backtrace := (AllocationBacktrace.get
        (machine.user.payload.payload.user.runtime.extras.allocations) storage.id)}))
    (zeroSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (holder : SliceHolder storage.entry.allocation.extra rights.tracker.global.protectedTags tag
      storage.relativeStart length)
    (pointer : Pointer (Option Provenance))
    (concrete : pointer.provenance = some (.concrete storage.id holder.tag))
    (sourceAddress : pointer.offset.bytes.toNat = base.toNat+storage.relativeStart.bytes.toNat)
    (destination : CanonicalCallDomain.PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer length true)
    (backing : ∀ id entry, machine.memory.live[id]? = some entry →
      machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
        some (id,{weakMemory := none,backtrace := (AllocationBacktrace.get
          machine.user.payload.payload.user.runtime.extras.allocations id)}))
    (noVarargs : frame.vaList = #[]) (continues : frame.returnContinuation = .stop true) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ final, SuccessfulTrace.Trace cfg limits before final ∧ final.stack.frames = #[] ∧
      ExecutionMachine.step cfg limits () final = (final,.ok false) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  have nonempty : 0 < length := UInt64.lt_iff_toNat_lt.mpr (by change 0 < length.toNat; omega)
  let post (state : MachineHooks.State MiriMemoryKind Machine.RootUser) : Prop :=
    state.stack.frames = #[] ∧ ExecutionMachine.step cfg limits () state = (state,.ok false)
  exact RootPositiveRootSuffix.runs_to_return options limits remaining span debug fuel validation statementFuel
    #[] frame before machine incoming length count base tag storage rights positive countFits disjoint address
    size pointerSlot temp16 live16 countSlot unused unused24 body identity callee location noClocks mode ghost shallow all noRace
    trackNone thread active top relevant budget dispatch backend unchecked noGc fixed source outerRank innerRank maskLen maskValid
    provenance storageFits root roots rangeCapacity bounded extras zeroSlot post (by
      intro result last allocation after done cleanup
      obtain ⟨final, returned, stopped, empty⟩ :=
        RootAliasedReturnAfterCopy.returns options limits remaining span debug fuel validation
          frame result done machine last length count base tag storage rights holder disjoint nonempty allocation after cleanup
          body noClocks noVarargs continues pointer concrete sourceAddress address destination backing
      exact ⟨final,returned,empty,stopped⟩)

#print axioms completes
end DuplicatePrefix.RootPositiveWithSharedOutput

import PreparedNonemptyLengthPrefix
import CanonicalPreparedPhysicalResources
import PhysicalDestinationAfterLength

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open SourceDomain PreparedArguments CanonicalConfigFacts
open GeneralRangeMapOrigins ArchiveForestProjection RetagReleaseFootprint RootZeroShallowReturn NonemptyReturnWatch
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The canonical source and actual emitted state after the length call. -/
structure PhysicalLengthContext (config : RootConfig) (limits : ExecutionMachine.Limits)
    (frame : CompilerFrameContext.ActualFrame) (machine : LenExitFacts.MachineState)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) where
  storage : InitializedRegion (Storage.withCurrent #[] frame machine) length
  tag : BorTag
  base : UInt64
  loan : ExclusiveRegion (Storage.withCurrent #[] frame machine) length storage tag
  scope : ReleaseRange storage.entry.allocation.extra loan.source storage.relativeStart length true
  source : CopySourceResources storage.entry
  ready : RetainedSlice machine
  id : ready.id = storage.id
  retainedTag : ready.tag = tag
  retainedEntry : ready.entry = storage.entry
  retainedHolder : ready.source = loan.source
  pointerTag : pointer.provenance = some (.concrete ready.id ready.tag)
  cached : machine.user.addresses.baseAddr.find? (·.allocId == ready.id) = some ⟨ready.id,base⟩
  address : pointer.offset.bytes.toNat = base.toNat + storage.relativeStart.bytes.toNat
  upper : (storage.relativeStart.bytes+length).toNat = storage.relativeStart.bytes.toNat + length.toNat
  result : CompilerFrameContext.ActualFrame
  final : LenExitFacts.MachineState
  post : RootLengthOfActiveSlice config #[] frame result machine final ready storage.entry storage.relativeStart.bytes
    length count loan.tracker
  trace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result final)

theorem reachesPhysicalLengthContext
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel fuel dispatch : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1)
    (dynamic : options.place.dynamicFuel = sizeFuel+1) (dispatchFuel : limits.callDispatch = dispatch+1)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) (positive : 0 < length)
    (nonzero : count ≠ 0)
    (admitted : Admitted program options remaining preparedTagHeadroom span
      (Storage.withCurrent #[] frame machine) frame pointer length count true)
    (compiler : InitialCompilerControl (Storage.withCurrent #[] frame machine) frame)
    (resource : ∀ id tag, pointer.provenance = some (.concrete id tag) →
      ∀ entry, machine.memory.live[id]? = some entry → CopySourceResources entry) :
    Nonempty (PhysicalLengthContext (PreparedContracts.actualConfig options () (remaining+1) span) limits
      frame machine pointer length count) := by
  have nonempty : length ≠ 0 := by
    intro equal
    rw [equal] at positive
    exact UInt64.lt_irrefl _ positive
  obtain ⟨storage,tag,base,loan,_,concrete,pointerNat,address,_,_,_,⟨node,found,_⟩,scope⟩ :=
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
  have upperEq : (storage.relativeStart.bytes+length).toNat =
      storage.relativeStart.bytes.toNat + length.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt scope.extent
      storage.entry.allocation.extra.locations.size.bytes.toNat_lt)]
  let active : AccessedWithin storage.entry.allocation.extra loan.source storage.relativeStart.bytes (storage.relativeStart.bytes+length) := by
    intro point pos valid lo hi state stored accessed
    rw [upperEq]
    exact scope.accessedWithin point pos valid lo hi state stored accessed
  obtain ⟨ready,result,final,idEq,tagEq,entryEq,holderEq,_,trace,⟨post⟩⟩ :=
    canonicalNonemptyLengthPrefix options limits remaining sizeFuel span fuel validation
      frame machine count nonzero loan.tracker loan.tracked dynamic storage.id tag loan.source root base
      storage.relativeStart.bytes length storage.entry addr positive nonnull loan.coherent node found roots loan.tagKnown
      scope.extent owners active dispatch dispatchFuel program loaded pointer concrete
      pointerBytes admitted compiler storage rfl rfl rfl available.keys available.room
  have actual : pointer.provenance = some (.concrete ready.id ready.tag) := by
    rw [idEq,tagEq]
    exact concrete
  have cached : machine.user.addresses.baseAddr.find? (·.allocId == ready.id) = some ⟨ready.id,base⟩ := by
    rw [idEq]
    exact addr
  exact ⟨⟨storage,tag,base,loan,scope,available,ready,idEq,tagEq,entryEq,holderEq,actual,cached,pointerNat,
    upperEq,result,final,post,trace⟩⟩

/-- The length call preserves the physical output's byte and protection
even when the argument reads from elsewhere in the same allocation. -/
theorem PhysicalLengthContext.destination
    {config limits frame machine pointer length count}
    (context : PhysicalLengthContext config limits frame machine pointer length count)
    (nonempty : length ≠ 0)
    (physical : PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer length true) :
    PhysicalBoolDestination (Storage.withCurrent #[] context.result context.final) context.result pointer length true := by
  have initialLive : machine.memory.live[context.ready.id]? = some context.storage.entry := by
    rw [context.id]
    exact context.storage.live
  have finalLive : context.final.memory.live[context.ready.id]? = some {context.storage.entry with
      allocation := context.storage.entry.allocation.setExtra context.post.branch.ready.entry.allocation.extra} := by
    rw [← context.post.branch.id,← context.post.branch.allocationData]
    exact context.post.branch.ready.present
  have sourceKey : context.storage.entry.allocation.extra.indexOfTag context.ready.tag = some context.ready.source := by
    rw [← context.retainedEntry]
    exact context.ready.indexed
  have sourceNode : ∃ node, context.storage.entry.allocation.extra.nodeAt context.ready.source = some node := by
    rw [← context.retainedEntry]
    exact ⟨context.ready.node,context.ready.found⟩
  exact PhysicalDestinationAfterLength.transport
    (before := Storage.withCurrent #[] frame machine) (after := Storage.withCurrent #[] context.result context.final)
    context.pointerTag nonempty initialLive finalLive context.post.branch.unrelated context.post.place
    (congrArg (·.borrowTracker) context.post.frameExtra) context.post.branch.stable.addresses context.cached context.address
    context.upper sourceKey sourceNode context.loan.tracked context.post.branch.ready.tracked context.post.protectors
    context.post.branch.rangeCapacity context.post.branch.ready.roots context.post.branch.coherence context.post.branch.vacant
    context.post.watched physical

#print axioms PhysicalLengthContext.destination
#print axioms reachesPhysicalLengthContext
end DuplicatePrefix.CanonicalCallDomain

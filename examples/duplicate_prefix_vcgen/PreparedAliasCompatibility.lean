import ActiveReleaseRangeOfCall

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.Verification Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows

theorem PhysicalBoolDestination.allowShared {before frame pointer length}
    (known : PhysicalBoolDestination before frame pointer length) :
    PhysicalBoolDestination before frame pointer length true := by
  obtain ⟨place,id,slot,relative,tag,base,tracker,owned,source,returnTag,returnIndex,
    saved,layout,aligned,live,mutable,backing,mask,maskLen,provenance,bound,ptr,nonnull,address,capacity,cached,
    tracked,owner,ledger,held,coherent,sourceKey,sourceNode,outputKey,outputNode,extent,grant,parentGrant,separate⟩ :=
    known.storage
  exact ⟨place,id,slot,relative,tag,base,tracker,owned,source,returnTag,returnIndex,
    saved,layout,aligned,live,mutable,backing,mask,maskLen,provenance,bound,ptr,nonnull,address,capacity,cached,
    tracked,owner,ledger,held,coherent,sourceKey,sourceNode,outputKey,outputNode,extent.toActive,grant,parentGrant,
    fun nonempty input inputTag sourcePtr => Or.inl (separate nonempty input inputTag sourcePtr)⟩

theorem Destination.allowShared {before frame pointer length}
    (known : Destination before frame pointer length) :
    Destination before frame pointer length true := by
  cases known with
  | physicalRoot stack continuation physical => exact .physicalRoot stack continuation physical.allowShared
  | cachedCaller cached ledger => exact .cachedCaller cached ledger

theorem Admitted.allowShared {program options remaining headroom span before frame pointer length count}
    (known : Admitted program options remaining headroom span before frame pointer length count) :
    Admitted program options remaining headroom span before frame pointer length count true := by
  refine ⟨known.profile,known.shape,known.stack,known.allocations,known.slice,known.identity,?_,
    known.emptyProtector,known.destination.allowShared,known.argLayout,known.countLayout,known.resultSlot,known.immediateLocals⟩
  intro nonempty
  obtain ⟨storage,tag,base,region,owned,concrete,address,cached,tracked,listed,held,node,range⟩ :=
    known.sliceProtector nonempty
  exact ⟨storage,tag,base,region,owned,concrete,address,cached,tracked,listed,held,node,range.toActive⟩

/-- Both tracked places select the same allocation. Their byte separation
and protector topology are supplied by the destination certificate. -/
def SharedPhysicalAllocation (frame : CompilerFrameContext.ActualFrame)
    (pointer : Pointer (Option Provenance)) : Prop :=
  ∃ (id : AllocId) (argument : BorTag) (place : MPlaceTy Provenance) (savedTag : BorTag),
    pointer.provenance = some (.concrete id argument) ∧
      frame.returnPlace = .memory place ∧ place.mplace.ptr.provenance = some (.concrete id savedTag)

/-- The root's ordinary prepared-input interface includes the existing
carrier profiles and admits a physical output byte sharing the nonempty
source allocation whenever its byte span is disjoint. -/
inductive PreparedReturnDomain
    (program : BodyVCGen.LoadedProgram) (options : EvalConfigurationCore.Options)
    (remaining headroom : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) : Prop where
  | legacy (call : Admitted program options remaining headroom span before frame pointer length count)
  | physical (call : Admitted program options remaining headroom span before frame pointer length count true)
      (nonempty : 0 < length) (stack : before.stack.frames = #[frame])
      (continuation : frame.returnContinuation = .stop true)
      (output : PhysicalBoolDestination before frame pointer length true)
      (shared : SharedPhysicalAllocation frame pointer)

#print axioms Admitted.allowShared
end DuplicatePrefix.CanonicalCallDomain

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.Interpreter Miri.Memory Miri.TreeBorrows

theorem PhysicalBoolDestination.reframeAlias
    {before after : MachineHooks.State MiriMemoryKind Machine.RootUser}
    {entry current : Frame Provenance LocalLayout MachineHooks.FrameExtra} {pointer : Pointer (Option Provenance)}
    {length : UInt64} {allowShared : Bool}
    (known : PhysicalBoolDestination before entry pointer length allowShared)
    (sameHeap : after.machine.memory = before.machine.memory)
    (sameTracker : after.machine.borrowTracker = before.machine.borrowTracker)
    (sameAddresses : after.machine.user.addresses = before.machine.user.addresses)
    (samePlace : current.returnPlace = entry.returnPlace)
    (sameLedger : current.extra.borrowTracker = entry.extra.borrowTracker) :
    PhysicalBoolDestination after current pointer length allowShared := by
  obtain ⟨place,id,slot,relative,tag,base,tracker,owned,source,returnTag,returnIndex,
    saved,layout,aligned,live,mutable,backing,mask,maskLen,provenance,bound,ptr,nonnull,address,capacity,cached,
    tracked,owner,ledger,held,coherent,sourceKey,sourceNode,outputKey,outputNode,extent,grant,parentGrant,separate⟩ :=
    known.storage
  exact ⟨place,id,slot,relative,tag,base,tracker,owned,source,returnTag,returnIndex,
    samePlace.trans saved,layout,aligned,by rw [sameHeap]; exact live,
    mutable,backing,mask,maskLen,provenance,bound,ptr,nonnull,address,capacity,by rw [sameAddresses]; exact cached,
    sameTracker.trans tracked,sameLedger.trans owner,ledger,held,coherent,sourceKey,sourceNode,
    outputKey,outputNode,extent,grant,parentGrant,separate⟩

#print axioms PhysicalBoolDestination.reframeAlias
end DuplicatePrefix.CanonicalCallDomain

import ActiveReleaseRangeOfCall
import duplicate_prefix.SharedReadWatch
import duplicate_prefix.GeneralRangeMapGeometry

namespace DuplicatePrefix.PhysicalDestinationAfterLength

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalCallDomain SourceDomain GeneralRangeMapOrigins ArchiveForestProjection RetagReleaseFootprint
open NonemptyReturnWatch

set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

/-- Preserve the prepared output byte through the actual shared length call. -/
theorem transport
    {before after : MachineHooks.State MiriMemoryKind Machine.RootUser}
    {entry current : CompilerFrameContext.ActualFrame}
    {pointer : Pointer (Option Provenance)} {length : UInt64}
    {id : AllocId} {tag : BorTag} {actor recipient root : UniIndex} {base lower upper : UInt64}
    {original : LocalAllocation Provenance BorrowTree MiriMemoryKind} {tree : BorrowTree}
    {tracker retained : MachineHooks.BorrowState}
    (concrete : pointer.provenance = some (.concrete id tag))
    (nonempty : length ≠ 0)
    (originalLive : before.machine.memory.live[id]? = some original)
    (readyLive : after.machine.memory.live[id]? = some {original with allocation := original.allocation.setExtra tree})
    (unrelated : ∀ key, key ≠ id → after.machine.memory.live[key]? = before.machine.memory.live[key]?)
    (samePlace : current.returnPlace = entry.returnPlace)
    (sameLedger : current.extra.borrowTracker = entry.extra.borrowTracker)
    (addresses : after.machine.user.addresses = before.machine.user.addresses)
    (sourceBase : before.machine.user.addresses.baseAddr.find? (·.allocId == id) = some ⟨id,base⟩)
    (sourceAddress : pointer.offset.bytes.toNat = base.toNat + lower.toNat)
    (sourceUpper : upper.toNat = lower.toNat + length.toNat)
    (sourceKey : original.allocation.extra.indexOfTag tag = some actor)
    (sourceNode : ∃ node, original.allocation.extra.nodeAt actor = some node)
    (tracked : before.machine.borrowTracker = some tracker)
    (readyTracked : after.machine.borrowTracker = some retained)
    (tags : retained.global.protectedTags = tracker.global.protectedTags)
    (treeSize : tree.locations.size = original.allocation.extra.locations.size)
    (rootEq : tree.roots = #[root])
    (coherent : CoherentForest tree) (vacant : VacantRows tree)
    (watched : SharedWatchTransfer original.allocation.extra tree actor recipient lower upper)
    (physical : PhysicalBoolDestination before entry pointer length true) :
    PhysicalBoolDestination after current pointer length true := by
  obtain ⟨place,key,row,start,parentTag,outputBase,seen,owned,parent,outputTag,output,
    saved,layout,aligned,live,mutable,backed,mask,maskLen,prov,fits,ptr,nonnull,address,capacity,cached,
    enabled,ledger,rows,held,oldCoherent,parentKey,parentData,outputKey,outputData,extent,grant,parentGrant,geometry⟩ :=
    physical.storage
  have sameTracker : seen = tracker := Option.some.inj (enabled.symm.trans tracked)
  subst seen
  have endCall : (retained.global.endCall owned).protectedTags = (tracker.global.endCall owned).protectedTags := by
    unfold GlobalState.endCall
    rw [tags]
  have address' : after.machine.user.addresses.baseAddr.find? (·.allocId == key) = some ⟨key,outputBase⟩ := by
    rw [addresses]
    exact cached
  by_cases alias : key = id
  · subst key
    have sameRow := Option.some.inj (live.symm.trans originalLive)
    subst row
    obtain ⟨parentNode,atParent,parentMatch⟩ := parentData
    obtain ⟨outputNode,atOutput,outputMatch,parentEdge,unexposed⟩ := outputData
    have baseMatches : outputBase = base := by
      have matchRow := Option.some.inj (cached.symm.trans sourceBase)
      injection matchRow
    subst outputBase
    obtain ⟨disjoint,foreign⟩ : DisjointResultByte (base.toNat + start.bytes.toNat)
        pointer.offset.bytes.toNat length ∧ ¬ Ancestor original.allocation.extra output actor := by
      rcases geometry nonempty id tag concrete with different | same
      · exact False.elim (different rfl)
      exact ⟨same.1,same.2 actor sourceKey⟩
    have outside : start.bytes.toNat < lower.toNat ∨ upper.toNat ≤ start.bytes.toNat := by
      rw [sourceAddress] at disjoint
      rw [sourceUpper]
      unfold DisjointResultByte at disjoint
      omega
    have wrap : start.bytes.toNat + 1 < 2^64 := Nat.lt_of_le_of_lt extent.extent
      original.allocation.extra.locations.size.bytes.toNat_lt
    have stop : (start.bytes+1).toNat = start.bytes.toNat+1 := by
      rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt wrap]
    have inputScope : AccessedWithin original.allocation.extra output start.bytes (start.bytes+1) := by
      intro point pos valid lo hi state fromRow accessed
      simpa only [stop,UInt64.toNat_one] using extent.accessedWithin point pos valid lo hi state fromRow accessed
    have beforeGrant : AtByte original.allocation.extra start.bytes tracker.global.protectedTags output := by
      intro i valid lo hi
      exact grant _ (Array.getElem_mem valid) lo hi
    have beforeParent : AtByte original.allocation.extra start.bytes (tracker.global.endCall owned).protectedTags parent := by
      intro i valid lo hi
      obtain ⟨segment,member,pLo,pHi,permission⟩ := parentGrant
      obtain ⟨j,inside,same⟩ := Array.mem_iff_getElem.mp member
      subst segment
      have unique : i = j := by
        rcases Nat.lt_trichotomy i j with lt | eq | gt
        · have bound := GeneralRangeMapGeometry.stop_le_start _ oldCoherent.ranges i j lt inside
          have lower := UInt64.le_iff_toNat_le.mp pLo
          have upper := UInt64.lt_iff_toNat_lt.mp hi
          omega
        · exact eq
        · have bound := GeneralRangeMapGeometry.stop_le_start _ oldCoherent.ranges j i gt valid
          have lower := UInt64.le_iff_toNat_le.mp lo
          have upper := UInt64.lt_iff_toNat_lt.mp pHi
          omega
      subst j
      exact permission
    obtain ⟨newScope,newGrant⟩ := watched.kept output output start.bytes (start.bytes+1) start.bytes
      tracker.global.protectedTags ⟨_,atOutput⟩ ⟨_,atOutput⟩ foreign outside inputScope beforeGrant
    have newParent := (watched.kept output parent start.bytes (start.bytes+1) start.bytes
      (tracker.global.endCall owned).protectedTags ⟨_,atOutput⟩ ⟨_,atParent⟩ foreign outside inputScope beforeParent).2
    have region : start.bytes.toNat + 1 ≤ tree.locations.size.bytes.toNat := by
      rw [treeSize]
      exact extent.extent
    have afterScope : AccessedOnlyWithin tree output start.bytes.toNat (start.bytes.toNat+1) := by
      intro point pos valid lo hi state found active
      simpa only [stop] using newScope point pos valid lo hi state found active
    have afterExtent := ReleaseRange.ofActiveByteScope coherent region ⟨root,rootEq⟩ afterScope vacant
    have afterGrant : ByteWriteGrant tree start.bytes output retained.global.protectedTags := by
      intro segment member lo hi
      obtain ⟨i,valid,same⟩ := Array.mem_iff_getElem.mp member
      subst segment
      rw [tags]
      exact newGrant i valid lo hi
    have afterParent : ∃ segment ∈ tree.locations.entries, segment.range.start ≤ start.bytes ∧
        start.bytes < segment.range.stop ∧ LocationRights tree segment.data (retained.global.endCall owned).protectedTags parent := by
      obtain ⟨i,valid,lo,hi⟩ := GeneralRangeMapGeometry.covered tree.locations coherent.ranges start.bytes (by omega)
      have l := UInt64.le_iff_toNat_le.mpr lo
      have h := UInt64.lt_iff_toNat_lt.mpr hi
      exact ⟨_,Array.getElem_mem valid,l,h,by rw [endCall]; exact newParent i valid l h⟩
    have newGeometry : length ≠ 0 → ∀ sourceId sourceTag,
        pointer.provenance = some (.concrete sourceId sourceTag) → sourceId ≠ id ∨
          (DisjointResultByte (base.toNat + start.bytes.toNat) pointer.offset.bytes.toNat length ∧
            ∀ holder, tree.indexOfTag sourceTag = some holder → ¬ Ancestor tree output holder) := by
      intro _ sourceId sourceTag selected
      have equal := Option.some.inj (concrete.symm.trans selected)
      injection equal with allocation source
      subst sourceId
      subst sourceTag
      refine .inr ⟨disjoint,?_⟩
      intro holder found path
      have same := Option.some.inj ((watched.key tag actor sourceKey).symm.trans found)
      subst holder
      exact foreign ((watched.ancestry actor output sourceNode).mpr path)
    obtain ⟨newParentNode,parentAt,parentTagged,_,_⟩ := watched.node parent parentNode atParent
    obtain ⟨newOutputNode,outputAt,outputTagged,outputParent,outputHidden⟩ := watched.node output outputNode atOutput
    exact ⟨place,id,_,start,parentTag,base,retained,owned,parent,outputTag,output,
      samePlace.trans saved,layout,aligned,readyLive,mutable,backed,mask,maskLen,prov,fits,ptr,nonnull,address,capacity,address',
      readyTracked,sameLedger.trans ledger,rows,by rw [tags];exact held,coherent,watched.key _ _ parentKey,
      ⟨newParentNode,parentAt,parentTagged.trans parentMatch⟩,watched.key _ _ outputKey,
      ⟨newOutputNode,outputAt,outputTagged.trans outputMatch,outputParent.trans parentEdge,outputHidden.trans unexposed⟩,
      afterExtent,afterGrant,afterParent,newGeometry⟩
  · exact ⟨place,key,row,start,parentTag,outputBase,retained,owned,parent,outputTag,output,
      samePlace.trans saved,layout,aligned,(unrelated key alias).trans live,mutable,backed,mask,maskLen,prov,fits,ptr,
      nonnull,address,capacity,address',readyTracked,sameLedger.trans ledger,rows,by rw [tags];exact held,
      oldCoherent,parentKey,parentData,outputKey,outputData,extent,by rw [tags];exact grant,
      by rw [endCall];exact parentGrant,geometry⟩

#print axioms transport
end DuplicatePrefix.PhysicalDestinationAfterLength

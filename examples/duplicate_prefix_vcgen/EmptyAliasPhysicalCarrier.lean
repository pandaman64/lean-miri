import EmptyAliasPhysicalRange
import duplicate_prefix.EmptySharedWriteFrame
import PhysicalCarrierDistinct
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.RootPhysicalCarrierTransport

open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Verification
open CanonicalCallDomain SourceDomain ArchiveForestProjection GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- The two empty-source retags preserve the original output slot even
when it belongs to the same allocation. -/
theorem transportEmpty
    (before after : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (entry current : CompilerFrameContext.ActualFrame)
    (pointer : Pointer (Option Provenance))
    (argument : AllocId) (old updated : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (originalLive : before.machine.memory.live[argument]? = some old)
    (updatedLive : after.machine.memory.live[argument]? = some updated)
    (sameBytes : updated = {old with allocation := old.allocation.setExtra updated.allocation.extra})
    (fresh : List BorTag)
    (transfer : EmptySharedWriteFrame.Transfer old.allocation.extra updated.allocation.extra fresh)
    (vacantAfter : ∀ index, updated.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < updated.allocation.extra.locations.entries.size),
        updated.allocation.extra.locations.entries[position].data.perms.get index = none)
    (freshKeys : ∀ index node, old.allocation.extra.nodeAt index = some node → node.tag ∉ fresh)
    (tracker retained : MachineHooks.BorrowState)
    (tracked : before.machine.borrowTracker = some tracker)
    (enabled : after.machine.borrowTracker = some retained)
    (protections : retained.global.protectedTags = tracker.global.protectedTags)
    (unheld : ∀ tag ∈ fresh, tracker.global.protectedTags.contains tag = false)
    (samePlace : current.returnPlace = entry.returnPlace)
    (sameLedger : current.extra.borrowTracker = entry.extra.borrowTracker)
    (addresses : after.machine.user.addresses = before.machine.user.addresses)
    (unrelated : ∀ key, key ≠ argument → after.machine.memory.live[key]? = before.machine.memory.live[key]?)
    (destination : PhysicalBoolDestination before entry pointer 0) :
    PhysicalBoolDestination after current pointer 0 := by
  obtain ⟨place,id,row,start,tag,base,recovered,owned,parent,child,childIndex,
    saved,layout,alignment,live,mutable,bytes,mask,maskLen,provenance,fits,ptr,nonnull,address,capacity,cached,
    active,ownership,ledger,held,coherent,parentKey,parentData,childKey,childData,extent,grant,retainedGrant,separation⟩ :=
    destination.storage
  have same : recovered = tracker := Option.some.inj (active.symm.trans tracked)
  subst recovered
  have endCall : (retained.global.endCall owned).protectedTags = (tracker.global.endCall owned).protectedTags := by
    unfold GlobalState.endCall
    rw [protections]
  by_cases alias : id = argument
  · subst id
    have actual := Option.some.inj (live.symm.trans originalLive)
    subst row
    obtain ⟨savedNode,savedAt,savedTag⟩ := parentData
    obtain ⟨outputNode,outputAt,outputTag,outputParent,outputHidden⟩ := childData
    have savedFresh : tag ∉ fresh := by rw [← savedTag]; exact freshKeys parent savedNode savedAt
    have outputFresh : child ∉ fresh := by rw [← outputTag]; exact freshKeys childIndex outputNode outputAt
    obtain ⟨nextSaved,nextSavedAt,nextSavedTag,_,_⟩ := transfer.nodes parent savedNode savedAt
    obtain ⟨nextOutput,nextOutputAt,nextOutputTag,nextOutputParent,nextOutputHidden⟩ :=
      transfer.nodes childIndex outputNode outputAt
    have bound : start.bytes.toNat + 1 ≤ old.allocation.extra.locations.size.bytes.toNat := by simpa using extent.extent
    have wrap : start.bytes.toNat + 1 < 2^64 :=
      Nat.lt_of_le_of_lt bound old.allocation.extra.locations.size.bytes.toNat_lt
    have capAfter : start.bytes.toNat + 1 ≤ updated.allocation.extra.locations.size.bytes.toNat := by
      rw [transfer.size]; exact bound
    have extentAfter := ReleaseRange.ofByteScope transfer.coherent capAfter
      (by rw [transfer.roots]; exact extent.root (by decide))
      (transfer.extent childIndex ⟨outputNode,outputAt⟩ _ _ extent.materializedWithin) vacantAfter
    have upper : (start.bytes+1).toNat = start.bytes.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt wrap]
    have childOwns : OwnedOn (fun row => LocationRights old.allocation.extra row tracker.global.protectedTags childIndex)
        start.bytes (start.bytes+1) old.allocation.extra.locations := by
      intro pos valid nonempty begins ends
      let row := old.allocation.extra.locations.entries[pos]
      change row.range.start.toNat < (start.bytes+1).toNat at begins
      have low : row.range.start ≤ start.bytes := UInt64.le_iff_toNat_le.mpr (by omega)
      exact grant row (Array.mem_iff_getElem.mpr ⟨pos,valid,rfl⟩) low (UInt64.lt_iff_toNat_lt.mpr ends)
    have grantAfter := byteGrant_of_owned wrap
      (transfer.owns tracker.global.protectedTags unheld childIndex ⟨outputNode,outputAt⟩ _ _ childOwns)
    have unheldEnd (freshTag : BorTag) (mem : freshTag ∈ fresh) :
        (tracker.global.endCall owned).protectedTags.contains freshTag = false := by
      rw [StackPopRelease.end_call_contains, unheld freshTag mem]
      split <;> rfl
    have parentOwns := ownedAtByte coherent.ranges wrap retainedGrant
    have nextParent := transfer.owns (tracker.global.endCall owned).protectedTags unheldEnd parent ⟨savedNode,savedAt⟩ _ _ parentOwns
    have covered := coveredAfter transfer.geometry wrap (by
      obtain ⟨row, member, lower, higher, _⟩ := retainedGrant
      exact ⟨row,member,lower,higher⟩) nextParent
    have backing : updated.allocation.mutability = .Mut ∧
        updated.allocation.len = updated.allocation.byteSize.bytes.toNat ∧
        DuplicatePrefix.InitMaskCopy.WellFormed updated.allocation.initializationMask ∧
        updated.allocation.initializationMask.len = updated.allocation.byteSize ∧
        DuplicatePrefix.ProvenanceCopy.WellFormed updated.allocation.provenanceMap updated.allocation.len ∧
        start.bytes < updated.allocation.byteSize.bytes ∧
        base.toNat + updated.allocation.byteSize.bytes.toNat < 2^64 := by
      have alloc := congrArg LocalAllocation.allocation sameBytes
      rw [alloc]
      exact ⟨mutable,bytes,mask,maskLen,provenance,fits,capacity⟩
    obtain ⟨mutAfter,bytesAfter,maskAfter,lenAfter,provAfter,fitsAfter,capacityAfter⟩ := backing
    exact ⟨⟨place,argument,updated,start,tag,base,retained,owned,parent,child,childIndex,
      samePlace.trans saved,layout,alignment,updatedLive,mutAfter,bytesAfter,maskAfter,lenAfter,provAfter,
      fitsAfter,ptr,nonnull,address,capacityAfter,(by rw [addresses]; exact cached),enabled,
      sameLedger.trans ownership,ledger,(by rw [protections]; exact held),transfer.coherent,
      (transfer.keys tag savedFresh).trans parentKey,⟨nextSaved,nextSavedAt,nextSavedTag.trans savedTag⟩,
      (transfer.keys child outputFresh).trans childKey,
      ⟨nextOutput,nextOutputAt,nextOutputTag.trans outputTag,nextOutputParent.trans outputParent,nextOutputHidden.trans outputHidden⟩,
      extentAfter,(by rw [protections]; exact grantAfter),(by rw [endCall]; exact covered),by simp⟩⟩
  · exact ⟨⟨place,id,row,start,tag,base,retained,owned,parent,child,childIndex,
      samePlace.trans saved,layout,alignment,(unrelated id alias).trans live,
      mutable,bytes,mask,maskLen,provenance,fits,ptr,nonnull,address,capacity,(by rw [addresses]; exact cached),
      enabled,sameLedger.trans ownership,ledger,(by rw [protections]; exact held),coherent,parentKey,parentData,
      childKey,childData,extent,(by rw [protections]; exact grant),(by rw [endCall]; exact retainedGrant),separation⟩⟩

#print axioms transportEmpty

end DuplicatePrefix.RootPhysicalCarrierTransport

import ActiveReleaseRangeOfCall
import duplicate_prefix.AliasedCopyTree
import duplicate_prefix.CopyProvenanceBounds
import duplicate_prefix.GeneralRangeMapGeometry
import EmptyAliasPhysicalRange

namespace DuplicatePrefix.PhysicalDestinationAfterCopy

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open CanonicalCallDomain SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint
open AccessedCopyHolderRights NonemptyReturnWatch Miri.Verification.RangeModifyLaw

set_option maxRecDepth 65536
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

/-- A protected original slice holder and the raw descendant actually used
by the emitted copy. Dormant materialization outside the slice is allowed. -/
structure SliceHolder (tree : BorrowTree) (tags : ProtectedTags) (raw : BorTag)
    (offset : Size) (length : UInt64) where
  source : UniIndex
  root : UniIndex
  holder : UniIndex
  tag : BorTag
  node : TreeNode
  holderNode : TreeNode
  atSource : tree.nodeAt source = some node
  atTag : tree.indexOfTag raw = some source
  atHolder : tree.nodeAt holder = some holderNode
  holderTag : tree.indexOfTag tag = some holder
  unexposed : holderNode.isExposed = false
  roots : tree.roots = #[root]
  coherent : CoherentForest tree
  lineage : Ancestor tree holder source
  unheld : ∀ index data, tree.nodeAt index = some data → Ancestor tree index source →
    ¬ Ancestor tree index holder → tags.contains data.tag = false
  fits : offset.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat
  footprint : Footprint tree tags source holder offset.bytes (offset.bytes+length)

private theorem same_cover (map : DedupRangeMap α) (formed : map.WellFormed) {point : UInt64}
    {i j : Nat} (hi : i < map.entries.size) (hj : j < map.entries.size)
    (ilo : map.entries[i].range.start.toNat ≤ point.toNat)
    (ihi : point.toNat < map.entries[i].range.stop.toNat)
    (jlo : map.entries[j].range.start.toNat ≤ point.toNat)
    (jhi : point.toNat < map.entries[j].range.stop.toNat) : i = j := by
  rcases Nat.lt_trichotomy i j with lt | same | gt
  · have no := GeneralRangeMapGeometry.stop_le_start map formed i j lt hj
    omega
  · exact same
  · have no := GeneralRangeMapGeometry.stop_le_start map formed j i gt hi
    omega

/-- Reframe the original physical destination after the real adjacent copy,
including a result byte in the same allocation outside the slice. -/
theorem transport
    (entry current : CompilerFrameContext.ActualFrame)
    (before after : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (pointer : Pointer (Option Provenance)) (length count : UInt64)
    (id : AllocId) (offset : Size) (base : UInt64) (raw : BorTag)
    (original : LocalAllocation Provenance BorrowTree MiriMemoryKind) (updated : Allocation Provenance BorrowTree)
    (oldLive : before.machine.memory.live[id]? = some original)
    (copiedLive : after.machine.memory.live[id]? = some ⟨original.kind,updated⟩)
    (unrelated : ∀ key, key ≠ id → after.machine.memory.live[key]? = before.machine.memory.live[key]?)
    (sized : updated.byteSize = original.allocation.byteSize)
    (bytes : updated.len = original.allocation.len)
    (valid : CopyProvenanceBounds.AllocationBacking updated)
    (tracker : MachineHooks.BorrowState)
    (oldTracker : before.machine.borrowTracker = some tracker)
    (tracked : after.machine.borrowTracker = some tracker)
    (slice : SliceHolder original.allocation.extra tracker.global.protectedTags raw offset length)
    (input : pointer.provenance = some (.concrete id slice.tag))
    (sliceBase : before.machine.user.addresses.baseAddr.find? (·.allocId == id) = some ⟨id,base⟩)
    (sliceAddress : pointer.offset.bytes.toNat = base.toNat+offset.bytes.toNat)
    (nonempty : length ≠ 0) (countBound : count.toNat+count.toNat ≤ length.toNat)
    (copiedTree :
      let read := original.allocation.extra.performBorrowAccessRange (.concrete raw) offset (Size.ofBytes count)
        .Read tracker.global.protectedTags .VisitChildrenOfAccessed
      updated.extra = (read.tree.performBorrowAccessRange (.concrete raw) (Size.ofBytes (offset.bytes+count))
        (Size.ofBytes count) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree)
    (addressEq : after.machine.user.addresses = before.machine.user.addresses)
    (savedPlace : current.returnPlace = entry.returnPlace)
    (savedLedger : current.extra.borrowTracker = entry.extra.borrowTracker)
    (physical : PhysicalBoolDestination before entry pointer length true) :
    PhysicalBoolDestination after current pointer length true true := by
  obtain ⟨place,key,row,start,parentTag,outputBase,seen,owned,parent,outputTag,output,
    saved,layout,aligned,live,mutable,backed,mask,maskLen,prov,fits,ptr,nonnull,address,capacity,cached,
    enabled,ledger,rows,held,coherent,parentKey,parentData,outputKey,outputData,extent,grant,parentGrant,geometry⟩ :=
    physical.storage
  have sameTracker : seen = tracker := Option.some.inj (enabled.symm.trans oldTracker)
  subst seen
  have address' : after.machine.user.addresses.baseAddr.find? (·.allocId == key) = some ⟨key,outputBase⟩ := by
    rw [addressEq]
    exact cached
  by_cases alias : key = id
  · subst key
    have sameRow := Option.some.inj (live.symm.trans oldLive)
    subst row
    obtain ⟨parentNode,atParent,parentMatch⟩ := parentData
    obtain ⟨outputNode,atOutput,outputMatch,parentEdge,unexposed⟩ := outputData
    have sameBase : outputBase = base := by
      have matchRow := Option.some.inj (cached.symm.trans sliceBase)
      injection matchRow
    subst outputBase
    have requirements := geometry nonempty id slice.tag input
    simp only [Bool.true_eq, ↓reduceIte, ne_self_iff_false, false_or] at requirements
    have outside : start.bytes.toNat < offset.bytes.toNat ∨ offset.bytes.toNat+length.toNat ≤ start.bytes.toNat := by
      have relative := (disjointResultByteRelative base.toNat start.bytes.toNat offset.bytes.toNat length).mp
        (by rw [← sliceAddress]; exact requirements.1)
      unfold DisjointResultByte at relative
      omega
    have foreign : ¬ Ancestor original.allocation.extra output slice.source := by
      intro path
      by_cases old : Ancestor original.allocation.extra output slice.holder
      · exact requirements.2 slice.holder slice.holderTag old
      · have noneHeld := slice.unheld output outputNode atOutput path old
        rw [outputMatch] at noneHeld
        simp only [ProtectedTags.contains, held, Option.isSome_some] at noneHeld
        contradiction
    have originalScope := extent.accessedWithin
    have wrap : start.bytes.toNat + 1 < 2^64 := Nat.lt_of_le_of_lt (by simpa using extent.extent)
      original.allocation.extra.locations.size.bytes.toNat_lt
    have stop : (start.bytes+1).toNat = start.bytes.toNat+1 := by
      rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt wrap]
    have watched : AccessedWithin original.allocation.extra output start.bytes (start.bytes+1) := by
      intro point pos valid lo hi savedState atState active
      simpa only [stop,UInt64.toNat_one] using originalScope point pos valid lo hi savedState atState active
    have frame := AliasedCopyTree.adjacent original.allocation.extra raw slice.source slice.holder slice.root
      tracker.global.protectedTags offset count length countBound slice.coherent slice.roots slice.atTag slice.node
      slice.atSource slice.lineage slice.unheld slice.fits slice.footprint output outputNode atOutput foreign
      start.bytes (start.bytes+1) watched
    obtain ⟨_,_,shape,afterCoherent,keptSize,permissions⟩ :=
      AccessedCopyHolderRights.prefixCopy_retains_holder original.allocation.extra tracker.global.protectedTags raw
        slice.source slice.holder slice.root offset count length countBound slice.coherent slice.node slice.atSource
        slice.roots slice.atTag slice.lineage slice.unheld slice.fits slice.footprint
    change updated.extra = _ at copiedTree
    dsimp only at frame
    rw [← copiedTree] at frame shape afterCoherent keptSize permissions
    have rootsAfter : updated.extra.roots = #[slice.root] := by rw [shape]; exact slice.roots
    have unitFits : start.bytes.toNat+1 ≤ updated.extra.locations.size.bytes.toNat := by
      rw [keptSize]
      simpa using extent.extent
    have scope : AccessedOnlyWithin updated.extra output start.bytes.toNat (start.bytes.toNat+1) := by
      intro point pos valid lo hi savedState atState activeState
      simpa only [stop] using frame.1 point pos valid lo hi savedState atState activeState
    have afterExtent := ReleaseRange.ofActiveByteScope afterCoherent unitFits ⟨slice.root,rootsAfter⟩ scope permissions.vacant
    have nodes : original.allocation.extra.nodes = updated.extra.nodes := (congrArg BorrowTree.nodes shape).symm
    have afterGrant : ByteWriteGrant updated.extra start.bytes output tracker.global.protectedTags := by
      intro row member lower upper
      obtain ⟨pos,good,equal⟩ := Array.mem_iff_getElem.mp member
      subst row
      obtain ⟨i,valid,lo,hi,rowEq⟩ := frame.2 start.bytes pos good lower upper outside
      have beforeGrant := grant _ (Array.getElem_mem valid) (UInt64.le_iff_toNat_le.mpr lo) (UInt64.lt_iff_toNat_lt.mpr hi)
      rw [← rowEq]
      exact CopyHolderRights.rights_frame nodes _ _ _ beforeGrant
    have afterParent : ∃ row ∈ updated.extra.locations.entries,
        row.range.start ≤ start.bytes ∧ start.bytes < row.range.stop ∧
        LocationRights updated.extra row.data (tracker.global.endCall owned).protectedTags parent := by
      obtain ⟨position,good,lo,hi⟩ := GeneralRangeMapGeometry.covered updated.extra.locations afterCoherent.ranges
        start.bytes (by omega)
      have lower := UInt64.le_iff_toNat_le.mpr lo
      have upper := UInt64.lt_iff_toNat_lt.mpr hi
      obtain ⟨previous,valid,pLo,pHi,rowEq⟩ := frame.2 start.bytes position good lower upper outside
      obtain ⟨past,member,oldLo,oldHi,ownedParent⟩ := parentGrant
      obtain ⟨wanted,wantedValid,observed⟩ := Array.mem_iff_getElem.mp member
      subst past
      have same := same_cover original.allocation.extra.locations coherent.ranges valid wantedValid pLo pHi
        (UInt64.le_iff_toNat_le.mp oldLo) (UInt64.lt_iff_toNat_lt.mp oldHi)
      subst wanted
      refine ⟨_,Array.getElem_mem good,lower,upper,?_⟩
      rw [← rowEq]
      exact CopyHolderRights.rights_frame nodes _ _ _ ownedParent
    have newGeometry : length ≠ 0 → ∀ sourceId srcTag,
        pointer.provenance = some (.concrete sourceId srcTag) →
        sourceId ≠ id ∨
          (DisjointResultByte (base.toNat + start.bytes.toNat) pointer.offset.bytes.toNat length ∧
            ∀ holder, updated.extra.indexOfTag srcTag = some holder → ¬ Ancestor updated.extra output holder) := by
      intro hz sourceId srcTag sourcePtr
      rcases geometry hz sourceId srcTag sourcePtr with diff | ⟨noOverlap,noAncestor⟩
      · exact .inl diff
      · refine .inr ⟨noOverlap,?_⟩
        intro holder key path
        rw [shape] at key path
        exact noAncestor holder key (AliasedCopyTree.ancestor_from_locations original.allocation.extra
          updated.extra.locations output holder path)
    exact ⟨place,id,⟨original.kind,updated⟩,start,parentTag,base,tracker,owned,parent,outputTag,output,
      savedPlace.trans saved,layout,aligned,copiedLive,valid.mutable,bytes.trans (backed.trans (congrArg (fun s : Size => s.bytes.toNat) sized.symm)),
      valid.mask,valid.maskLength,valid.pointers,(by rw [sized];exact fits),ptr,nonnull,address,(by rw [sized];exact capacity),
      address',tracked,savedLedger.trans ledger,rows,held,afterCoherent,(by rw [shape];exact parentKey),
      ⟨parentNode,by rw [shape];exact atParent,parentMatch⟩,(by rw [shape];exact outputKey),
      ⟨outputNode,by rw [shape];exact atOutput,outputMatch,parentEdge,unexposed⟩,
      afterExtent,afterGrant,afterParent,newGeometry⟩
  · have backingValid : ProvenanceCopy.WellFormed row.allocation.provenanceMap row.allocation.len := prov
    exact ⟨place,key,row,start,parentTag,outputBase,tracker,owned,parent,outputTag,output,
      savedPlace.trans saved,layout,aligned,(unrelated key alias).trans live,mutable,backed,
      mask,maskLen,ProvenanceCopy.WellFormed.pointerBounds backingValid,fits,ptr,nonnull,address,capacity,address',tracked,
      savedLedger.trans ledger,rows,held,coherent,parentKey,parentData,outputKey,outputData,extent,
      grant,parentGrant,geometry⟩

#print axioms transport
end DuplicatePrefix.PhysicalDestinationAfterCopy

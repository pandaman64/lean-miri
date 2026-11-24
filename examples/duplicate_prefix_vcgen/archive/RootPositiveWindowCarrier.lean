import duplicate_prefix.RootPositiveWindowReturn

namespace DuplicatePrefix.RootPositiveWindowCarrier

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalCallDomain RootPositiveWindowReturn ArchiveForestProjection GeneralRangeMapOrigins
open SourceDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

private theorem rangedGrant {tree : BorrowTree} {start : Size} {source : UniIndex}
    {tags : ProtectedTags} (grant : ByteWriteGrant tree start.bytes source tags)
    (extent : ReleaseRange tree source start 1) :
    OwnedOn (fun row => LocationRights tree row tags source)
      start.bytes (start.bytes + 1) tree.locations := by
  have fits : start.bytes.toNat + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt extent.extent tree.locations.size.bytes.toNat_lt
  have endByte : (start.bytes + 1).toNat = start.bytes.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  intro position inside _ starts stops
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  have below : segment.range.start ≤ start.bytes := by
    rw [UInt64.le_iff_toNat_le]
    change segment.range.start.toNat < (start.bytes + 1).toNat at starts
    omega
  exact grant segment member below (UInt64.lt_iff_toNat_lt.mpr stops)

/-- The canonical physical carrier supplies a live result byte, its release
authorization, and the parent's access to that exact byte after the release. -/
theorem from_destination
    (frame : CompilerFrameContext.ActualFrame) (machine : RootPositivePhysicalPop.MachineState)
    (pointer : Pointer (Option Provenance)) (length : UInt64) (argument : AllocId) (holderTag : BorTag)
    (nonempty : length ≠ 0) (concrete : pointer.provenance = some (.concrete argument holderTag))
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer length)
    (backing : ∀ id entry, id ≠ argument → machine.memory.live[id]? = some entry →
      machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
        some (id,{weakMemory := none,backtrace := (AllocationBacktrace.get
          machine.user.payload.payload.user.runtime.extras.allocations id)})) :
    ∃ (slot : Slot machine frame) (owned : FrameState),
      slot.id ≠ argument ∧ frame.extra.borrowTracker = some owned ∧
      owned.protectedTags = #[(argument,holderTag),(slot.id,slot.protectedTag)] ∧
      Nonempty (ReleasedSlot tracker owned slot) := by
  obtain ⟨place,id,row,relative,tag,base,actualTracker,owned,parent,releaseTag,holder,
    saved,layout,alignment,live,mutable,bytes,mask,maskLen,provenance,fits,ptr,_,address,capacity,cached,
    active,ownership,ledger,_,coherent,parentKey,parentData,holderKey,holderData,extent,grant,retainedGrant⟩ :=
    destination.storage
  have trackerEq : actualTracker = tracker := Option.some.inj (active.symm.trans tracked)
  subst actualTracker
  obtain ⟨parentNode,foundParent,_⟩ := parentData
  obtain ⟨holderNode,foundHolder,tagEq,edge,unexposed⟩ := holderData
  have naturalBound : relative.bytes.toNat < row.allocation.byteSize.bytes.toNat := UInt64.lt_iff_toNat_lt.mp fits
  have noWrap : base.toNat + relative.bytes.toNat < 2 ^ 64 := by omega
  have computed : (base + relative.bytes).toNat = base.toNat + relative.bytes.toNat := by
    simp only [UInt64.toNat_add, Nat.mod_eq_of_lt noWrap]
  have addressEq : place.mplace.ptr.offset.bytes = base+relative.bytes :=
    UInt64.toNat_inj.mp (address.trans computed.symm)
  have exactPointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+relative.bytes)) := by
    cases exactPtr : place.mplace.ptr with
    | mk offset provenance =>
      have tagEq : provenance = some (.concrete id tag) := by simpa only [exactPtr] using ptr
      have offsetBytes : offset.bytes = base+relative.bytes := by simpa only [exactPtr] using addressEq
      have offsetEq : offset = Size.ofBytes (base+relative.bytes) := congrArg Size.ofBytes offsetBytes
      cases tagEq
      cases offsetEq
      rfl
  have frameLedger : owned.protectedTags = #[(argument,holderTag),(id,releaseTag)] := by
    rw [argumentLedger,concrete] at ledger
    exact ledger.trans (by rfl)
  have different : length ≠ 0 → ∀ sourceId srcTag,
      pointer.provenance = some (.concrete sourceId srcTag) → sourceId ≠ id := by
    first | exact retainedGrant | exact retainedGrant.2
  have separate : id ≠ argument := (different nonempty argument holderTag concrete).symm
  let slot : Slot machine frame :=
    { place := place
      id := id
      sourceTag := tag
      protectedTag := releaseTag
      entry := row
      base := base
      offset := relative.bytes
      capacity := row.allocation.byteSize.bytes
      layout := layout
      aligned := alignment
      present := live
      cached := cached
      pointer := exactPointer
      bounds := by omega
      size := by cases row.allocation.byteSize; rfl
      bytes := bytes
      mutable := mutable
      maskValid := mask
      maskLength := maskLen.trans (by cases row.allocation.byteSize; rfl)
      provenance := provenance
      destination := by rw [saved];rfl
      extras := backing id row separate live
      addressBound := by rw [address]; omega }
  have ownedTag : slot.protectedTag ∈ owned.protectedTags.toList.map Prod.snd := by
    rw [frameLedger]
    simp [slot]
  have relativeEq : relative = Size.ofBytes relative.bytes := by cases relative; rfl
  have result := released_slot_of_rights slot tracker owned parent holder parentNode holderNode
    parentKey foundParent holderKey foundHolder tagEq edge unexposed coherent (by rw [← relativeEq]; exact extent)
    ownedTag (rangedGrant grant extent)
  exact ⟨slot,owned,separate,ownership,frameLedger,result⟩

#print axioms from_destination
end DuplicatePrefix.RootPositiveWindowCarrier

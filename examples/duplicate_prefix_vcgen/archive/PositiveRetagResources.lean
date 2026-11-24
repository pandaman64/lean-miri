import duplicate_prefix.RootPositiveFromLength
import duplicate_prefix.RawHolderScope
import duplicate_prefix.RetagStageImage

namespace DuplicatePrefix.PositiveRetagResources
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open Miri.Verification.MutableTypedRetag Miri.Verification.MutableReferenceRights
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint
open FrozenReborrowInputs RetagStageImage RetagInsertionCapacity RootPositiveFromLength
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false

private theorem advance (global : TreeBorrows.GlobalState)
    (budget : global.nextPointerTag.value.toNat + 2 < 2 ^ 64) :
    ∃ next, global.newPointerTag = .ok (next,global.nextPointerTag) ∧
      next.nextPointerTag = global.nextPointerTag.succ.getD global.nextPointerTag := by
  have notMax : global.nextPointerTag.value ≠ 18446744073709551615 := by
    intro equal
    rw [equal] at budget
    simp at budget
  have notZero : global.nextPointerTag.value + 1 ≠ 0 := by
    intro equal
    have sum := congrArg UInt64.toNat equal
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by simpa using (show global.nextPointerTag.value.toNat + 1 < 2^64 by omega))] at sum
    simp at sum
  cases next : global.nextPointerTag.succ with
  | none => simp [BorTag.succ,BorTag.ofUInt64,notMax,notZero] at next
  | some tag => exact ⟨{global with nextPointerTag := tag},by simp [TreeBorrows.GlobalState.newPointerTag,next],by simp [next]⟩

/-- The raw pointer returned by the mutable helper carries the original
holder's ownership and the exact unprotected ancestry used by copy. -/
theorem holderImage
    (tree : BorrowTree) (global : TreeBorrows.GlobalState) (holderTag : BorTag)
    (holder root : UniIndex) (start length : Size)
    (source : Stage tree global.protectedTags holderTag global.nextPointerTag holder root start length
      (DedupRangeMap.new length ExclusiveTwoPhaseRetag.initial) false)
    (coherence : Ready tree) (space : tree.nodes.size + 1 < 2 ^ 32)
    (age : ∀ i node, tree.nodeAt i = some node → node.tag.value.toNat < global.nextPointerTag.value.toNat)
    (protectedOrder : ∀ old, global.protectedTags.contains old = true → old.value.toNat < global.nextPointerTag.value.toNat)
    (tagRoom : global.nextPointerTag.value.toNat + 2 < 2 ^ 64)
    (holderHidden : (tree.nodeAt holder).map TreeNode.isExposed = some false) :
    let reservationTag := global.nextPointerTag
    let finalTag := reservationTag.succ.getD reservationTag
    let tags := global.protectedTags
    let reservation := ExclusiveTwoPhaseRetag.reservationTree tree holderTag reservationTag start length tags
    let active := ExclusiveTypedRetag.protectedFrozenTree reservation tags reservationTag finalTag start length
    let released := (active.releaseProtector finalTag (tags.insert finalTag .StrongProtector)).tree
    ∀ index, released.indexOfTag finalTag = some index →
      HolderImage released ((tags.insert finalTag .StrongProtector).remove finalTag)
        holder index holderTag start length.bytes := by
  intro reservationTag finalTag tags reservation active released index picked
  obtain ⟨after,allocated,indexEq⟩ := advance global tagRoom
  have futureTag : after.nextPointerTag = finalTag := indexEq
  have distinctAge : reservationTag.value.toNat < finalTag.value.toNat := by
    rw [← futureTag,RetagSuccessorCapacity.allocated_tag_value global after allocated tagRoom]
    change global.nextPointerTag.value.toNat < global.nextPointerTag.value.toNat+1
    omega
  have noReservation : tags.contains reservationTag = false := by
    cases heldNow : tags.contains reservationTag
    · rfl
    · exact False.elim (Nat.lt_irrefl _ (protectedOrder reservationTag heldNow))
  have noFinal : tags.contains finalTag = false := by
    cases heldNow : tags.contains finalTag
    · rfl
    · have prior := protectedOrder finalTag heldNow
      change reservationTag.value.toNat < finalTag.value.toNat at distinctAge
      change finalTag.value.toNat < reservationTag.value.toNat at prior
      omega
  let outerRows := DedupRangeMap.new length ExclusiveTwoPhaseRetag.initial
  let innerRows := DedupRangeMap.new length ExclusiveTypedRetag.readState
  have outerSpan := RetagStageImage.uniform start length tree.locations.size
    ExclusiveTwoPhaseRetag.initial false source.bounds (.inl rfl)
  have fresh : ∀ i node, tree.nodeAt i = some node → node.tag ≠ reservationTag := by
    intro i node found equal
    have prior := age i node found
    rw [equal] at prior
    exact Nat.lt_irrefl _ prior
  have prepared := RetagStageImage.installed tree tags holderTag reservationTag holder root start length outerRows false
      source fresh (fun _ member => (outerSpan _ member).2.2)
  have capacity := RetagSuccessorCapacity.afterReservation tree global holderTag holder root start length
    source coherence space age tagRoom
  have inner (selected : UniIndex) (key : reservation.indexOfTag reservationTag = some selected) :
      Stage reservation (tags.insert finalTag .StrongProtector) reservationTag finalTag selected root start length innerRows true := by
    have before : Installed reservation tags selected root start length := prepared.2.2 selected key
    have nextCapacity := (capacity after selected allocated key).2
    rw [futureTag] at nextCapacity
    have sizes : reservation.locations.size = tree.locations.size := prepared.1
    have bounds : start.bytes.toNat+length.bytes.toNat ≤ reservation.locations.size.bytes.toNat := by
      rw [sizes]
      exact source.bounds
    have rows := RetagStageImage.uniform start length reservation.locations.size
      ExclusiveTypedRetag.readState true bounds (.inl rfl)
    have owners : OwnedOn (fun row => LocationRights reservation row (tags.insert finalTag .StrongProtector) selected)
        start.bytes (start.bytes+length.bytes) reservation.locations := by
      intro position valid positive lower upper query data found
      have same := contains_insert_other tags finalTag data.tag .StrongProtector (nextCapacity.freshNode query data found)
      obtain ⟨state,current,localRight,foreignRight⟩ := before.owners position valid positive lower upper query data found
      exact ⟨state,current,(by simpa only [same] using localRight),(by simpa only [same] using foreignRight)⟩
    exact {
      coherent := before.coherent
      parentFound := key
      parentPresent := by
        obtain ⟨node,found,_⟩ := before.found
        exact ⟨node,found⟩
      roots := before.roots
      fresh := nextCapacity.freshKey
      room := nextCapacity.room
      aligned := nextCapacity.aligned
      reuse := nextCapacity.reuse
      bounds := bounds
      span := fun segment member => (rows segment member).1
      policy := fun segment member => (rows segment member).2.1
      owners := owners
      scope := before.scope
      vacant := before.vacant }
  have release (returned : UniIndex) (key : active.indexOfTag finalTag = some returned) :
      RawHolderScope.ReleaseStage active (tags.insert finalTag .StrongProtector) returned root start length := by
    obtain ⟨selected,keyBefore⟩ := prepared.2.1
    have parentKey : reservation.indexOfTag reservationTag = some selected := keyBefore
    have entered := inner selected parentKey
    have nextCapacity := (capacity after selected allocated parentKey).2
    rw [futureTag] at nextCapacity
    have rows := RetagStageImage.uniform start length reservation.locations.size
      ExclusiveTypedRetag.readState true entered.bounds (.inl rfl)
    have installed := RetagStageImage.installed reservation (tags.insert finalTag .StrongProtector)
      reservationTag finalTag selected root start length innerRows true entered nextCapacity.freshNode
      (fun _ member => (rows _ member).2.2)
    have shape : Installed active (childProtections (tags.insert finalTag .StrongProtector) finalTag true)
        returned root start length := by
      exact installed.2.2 returned key
    have mask : childProtections (tags.insert finalTag .StrongProtector) finalTag true =
        tags.insert finalTag .StrongProtector := by
      simp [childProtections,ProtectedTags.insert,Array.filter_filter]
    rw [mask] at shape
    exact ⟨shape.coherent,shape.roots,shape.found,shape.scope,shape.vacant,shape.owners⟩
  obtain ⟨_,_,oldKey,hidden,sourceIndex,sourceKey,between,footprint⟩ :=
    RawHolderScope.from_two_reborrows tree tags holderTag reservationTag finalTag holder root start length
      noReservation noFinal outerRows innerRows source holderHidden inner release
  have matchIndex : index = sourceIndex := Option.some.inj (picked.symm.trans sourceKey)
  have restored := RawHolderScope.fresh_mask_restored tags finalTag .StrongProtector noFinal
  rw [restored,matchIndex]
  refine ⟨oldKey,?_,between,footprint⟩
  change (released.nodeAt holder).map TreeNode.isExposed = some false at hidden
  cases present : released.nodeAt holder with
  | none => simp [present] at hidden
  | some node => exact ⟨node,rfl,Option.some.inj (by simpa only [present,Option.map_some] using hidden)⟩

end DuplicatePrefix.PositiveRetagResources

#print axioms DuplicatePrefix.PositiveRetagResources.holderImage

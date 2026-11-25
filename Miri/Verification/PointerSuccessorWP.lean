import Miri.Verification.PointerFormationWP
import Miri.Verification.CopyInitialWP

/-! The allocation-local fragment of a frozen reference retag followed by
one byte access. The checked address, allocation, compiler policy and race
effects belong to the enclosing machine rule. -/
namespace Miri.Verification.PointerSuccessorWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open TreeRangeOutcomeWP

inductive Formation where
  | shared
  | mutable
  | raw

def Formation.policy : Formation → Option RetagPolicy.NewPermission
  | .shared => RetagPolicy.create ⟨true, true, true⟩ .Shared .Default ⟨false, false⟩
  | .mutable => RetagPolicy.create ⟨true, true, true⟩ .Mutable .Default ⟨false, false⟩
  | .raw => none

/-- Default formation on one frozen byte uses a read on the parent and
creates an unprotected child. The raw case allocates no tag. -/
def Formation.frozen : Formation → Option (Tree.LocationState × Permission)
  | .shared => some (⟨.Frozen, true, .Read⟩, .Frozen)
  | .mutable => some (⟨.ReservedFrz false, true, .Read⟩, .ReservedFrz false)
  | .raw => none

theorem Formation.frozen_policy (form : Formation) :
    form.policy.bind (fun policy =>
      (RetagPolicy.initialLocationState policy true).toOption.map
        (fun initial => (initial, policy.outsidePermission))) = form.frozen ∧
    ∀ policy, form.policy = some policy → policy.protector = none := by
  cases form <;> constructor <;> first | rfl | intro policy selected; cases selected
  all_goals rfl

abbrev Error := RangeAccessError ⊕ BorrowTree.ChildInsertError

/-- Execute the actual allocation-local operations selected by the policy
for a single frozen byte. Raw formation has no parent visit or insertion. -/
def access (form : Formation) (parent : ProvenanceExtra) (tag : BorTag)
    (offset : Size) (tags : ProtectedTags) (kind : AccessKind) :
    EStateM Error BorrowTree Trace :=
  let observe := fun source => EStateM.adaptExcept Sum.inl
    (TreeBorrowsWP.access source offset (Size.ofBytes 1) kind tags .VisitChildrenOfAccessed)
  match form.frozen with
  | none => observe parent
  | some (initial, outside) => do
    let _ ← EStateM.adaptExcept Sum.inl
      (TreeBorrowsWP.access parent offset (Size.ofBytes 1) .Read tags .VisitChildrenOfAccessed)
    EStateM.adaptExcept Sum.inr (TreeBorrowsWP.insertChild offset parent tag
      (DedupRangeMap.new (Size.ofBytes 1) initial) outside false)
    observe (.concrete tag)

private theorem wp_bind_attempt {E E' A B S : Type} (liftError : E → E')
    (effect : EStateM E S A) (next : A → EStateM E' S B) (state : S)
    (post : B → S → Prop) (failure : E' → S → Prop) :
    wp (EStateM.adaptExcept liftError effect >>= next) post failure state ↔
      wp effect (fun value after => wp (next value) post failure after)
        (fun error after => failure (liftError error) after) state := by
  simp only [wp, WP.wpTrans, bind, Bind.bind, EStateM.bind, EStateM.adaptExcept]
  cases effect state <;> rfl

private theorem wp_adapt {E E' A S : Type} (liftError : E → E')
    (effect : EStateM E S A) (state : S) (post : A → S → Prop) (failure : E' → S → Prop) :
    wp (EStateM.adaptExcept liftError effect) post failure state ↔
      wp effect post (fun error after => failure (liftError error) after) state := by
  simp only [wp, WP.wpTrans, EStateM.adaptExcept]
  cases effect state <;> rfl

private theorem wp_insertChild (offset : Size) (parent : ProvenanceExtra) (tag : BorTag)
    (initial : Tree.LocationState) (outside : Permission) (state : BorrowTree)
    (post : Unit → BorrowTree → Prop) (failure : BorrowTree.ChildInsertError → BorrowTree → Prop) :
    wp (TreeBorrowsWP.insertChild offset parent tag (DedupRangeMap.new (Size.ofBytes 1) initial)
      outside false) post failure state ↔
    BorrowTree.MutationVerification.insertChildPre state offset parent tag
      (DedupRangeMap.new (Size.ofBytes 1) initial) outside false
      (post ()) failure := by
  rw [BorrowTree.MutationVerification.insertChildPre_iff]
  unfold BorrowTree.MutationVerification.childResultPre wp WP.wpTrans EStateM.wpInst TreeBorrowsWP.insertChild
    TreeBorrowsWP.mutation
  generalize child : (state.newChild offset parent tag (DedupRangeMap.new (Size.ofBytes 1) initial)
      outside false) = result
  cases outcome : result.outcome with
  | error => simp only [child, outcome]
  | ok value => cases value; simp only [child, outcome]

/-- Pull the successor through the actual child insertion and its parent
access. Each failing local operation retains the tree and diagnostic it
produced. The uniform frozen policy has a read for shared and mutable. -/
theorem wp_access (form : Formation) (parent : ProvenanceExtra) (tag : BorTag)
    (offset : Size) (tags : ProtectedTags) (kind : AccessKind) (state : BorrowTree)
    (post : Trace → BorrowTree → Prop) (failure : Error → BorrowTree → Prop) :
    wp (access form parent tag offset tags kind) post failure state ↔
      let observe (source : ProvenanceExtra) (before : BorrowTree) :=
        TreeBorrowsWP.accessPre before source offset (Size.ofBytes 1) kind tags .VisitChildrenOfAccessed
          (fun after trace => post trace after)
          (fun status after trace => failure (.inl (status, trace)) after)
      match form.frozen with
      | none => observe parent state
      | some (initial, outside) =>
        let insert := fun before => BorrowTree.MutationVerification.insertChildPre
          before offset parent tag (DedupRangeMap.new (Size.ofBytes 1) initial)
          outside false (observe (.concrete tag))
          (fun error after => failure (.inr error) after)
        TreeBorrowsWP.accessPre state parent offset (Size.ofBytes 1) .Read tags .VisitChildrenOfAccessed
          (fun after _ => insert after) (fun status after trace => failure (.inl (status, trace)) after) := by
  unfold access
  cases frozen : form.frozen with
  | none => simp only [wp_adapt, wp_access_outcomePre_iff]
  | some profile =>
    rcases profile with ⟨initial, outside⟩
    simp only [wp_bind_attempt, wp_adapt, wp_insertChild, wp_access_outcomePre_iff]

/-- In the rejecting-error WP, a checked extent eliminates the initial
ranged operation in favor of its byte-local permission and protector
conditions. The child insertion and successor operate on the tree supplied
by that continuation. No successful tree transition is a premise. -/
theorem wp_checked (form : Formation) (parent : ProvenanceExtra) (tag : BorTag)
    (offset finish : Size) (tags : ProtectedTags) (kind : AccessKind) (tree : BorrowTree)
    (formed : tree.locations.WellFormed) (endOffset : offset.add (Size.ofBytes 1) = .ok finish)
    (bound : finish.bytes ≤ tree.locations.size.bytes) (post : Trace → BorrowTree → Prop) :
    wp (access form parent tag offset tags kind) post (fun _ _ => False) tree ↔
      let observed (source : ProvenanceExtra) (ready : BorrowTree) :=
        TreeBorrowsWP.accessPre ready source offset (Size.ofBytes 1) kind tags .VisitChildrenOfAccessed
          (fun next trace => post trace next) (fun _ _ _ => False)
      let initialAccess (accessKind : AccessKind) (next : Trace → BorrowTree → Prop) :=
        TreeOverlapWP.accessBytePre tree parent offset (Size.ofBytes 1) ⟨offset.bytes, finish.bytes⟩
          accessKind tags .VisitChildrenOfAccessed next
      match form.frozen with
      | none => initialAccess kind post
      | some (initial, outside) =>
        initialAccess .Read (fun _ read =>
          BorrowTree.MutationVerification.insertChildPre read offset parent tag
            (DedupRangeMap.new (Size.ofBytes 1) initial) outside false (observed (.concrete tag))
            (fun _ _ => False)) := by
  rw [wp_access]
  cases form.frozen with
  | none => exact CopyInitialWP.accessPre_checkedBytes _ _ _ _ _ _ _ _ formed endOffset bound _
  | some profile =>
    rcases profile with ⟨initial, outside⟩
    exact CopyInitialWP.accessPre_checkedBytes _ _ _ _ _ _ _ _ formed endOffset bound _

/-- A successful successor read observes the symbolic initialized byte at
the checked offset. The returned tree is the successor's, while decoding
uses the original byte image because retagging changes allocation extra. -/
theorem wp_initializedRead (form : Formation) (parent : ProvenanceExtra) (tag : BorTag)
    (offset : Size) (tags : ProtectedTags) (allocation : Allocation Provenance BorrowTree)
    (layout : TargetDataLayout) (byte : UInt8)
    (bytes : allocation.getBytesUnchecked (allocRange offset (Size.ofBytes 1)) = .ok #[byte])
    (initialized : allocation.initializationMask.isRangeInitialized
      (allocRange offset (Size.ofBytes 1)) = .ok (.ok ()))
    (post : UInt8 → Trace → BorrowTree → Prop) (failure : Error → BorrowTree → Prop) :
    wp (access form parent tag offset tags .Read)
      (fun trace after =>
        ((allocation.setExtra after).readScalar layout (allocRange offset (Size.ofBytes 1)) false
          |>.toOption.bind fun scalar => scalar.toUInt8.toOption) = some byte ∧ post byte trace after)
      failure allocation.extra ↔
    wp (access form parent tag offset tags .Read) (post byte) failure allocation.extra := by
  have observed (after : BorrowTree) :
      (allocation.setExtra after).readScalar layout (allocRange offset (Size.ofBytes 1)) false =
        .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 byte)) := by
    rw [MemoryObservationWP.readScalar_eq_image]
    change MemoryObservationWP.scalarFromImage layout (allocRange offset (Size.ofBytes 1)) false
      (allocation.getBytesUnchecked _) (allocation.initializationMask.isRangeInitialized _)
      allocation.provenanceMap = _
    rw [bytes, initialized, CopyInitialWP.scalarFromImage_byte]
  simp only [observed, Except.toOption, Option.bind_some, CopyInitialWP.toUInt8_byte, true_and]

/-- An integer store through the selected pointer writes its symbolic byte
and keeps the access's new permission tree. The premises concern initial
storage, the one-byte offset and scalar encoding. The physical write result
follows from the allocation's scalar-store rule. -/
theorem wp_initializedWrite (form : Formation) (parent : ProvenanceExtra) (tag : BorTag)
    (offset : Size) (tags : ProtectedTags) (allocation : Allocation Provenance BorrowTree)
    (layout : TargetDataLayout) (value : Scalar Provenance) (bits : U128)
    (cleared : ProvenanceMap Provenance)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (mutable : allocation.mutability = .Mut)
    (maskLength : allocation.initializationMask.len = allocation.byteSize)
    (maskValid : InitMask.WriteProof.WellFormed allocation.initializationMask)
    (bound : offset.bytes.toNat + 1 ≤ allocation.byteSize.bytes.toNat)
    (conversion : value.toBitsOrPtrInternal (Size.ofBytes 1) = .ok (.bits bits))
    (clear : ∀ image : Array UInt8,
      allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) = .ok image →
      allocation.provenanceMap.clear (allocRange offset (Size.ofBytes 1)) image
        (Size.fromBits layout.pointerWidth.bits) = .ok () cleared)
    (post : Trace → BorrowTree → Prop) (failure : Error → BorrowTree → Prop) :
    wp (access form parent tag offset tags .Write)
      (fun trace after =>
        match Allocation.writeScalar layout (allocRange offset (Size.ofBytes 1)) value
          (allocation.setExtra after) with
        | .error _ _ => False
        | .ok () written =>
          written.extra = after ∧
          written.getBytesUnchecked (allocRange offset (Size.ofBytes 1)) =
            .ok (MemoryWP.scalarBytes layout (Size.ofBytes 1) bits.toNat) ∧ post trace after)
      failure allocation.extra ↔
    wp (access form parent tag offset tags .Write) post failure allocation.extra := by
  have stored (trace : Trace) (after : BorrowTree) :
      (match Allocation.writeScalar layout (allocRange offset (Size.ofBytes 1)) value
          (allocation.setExtra after) with
        | .error _ _ => False
        | .ok () written =>
          written.extra = after ∧
          written.getBytesUnchecked (allocRange offset (Size.ofBytes 1)) =
            .ok (MemoryWP.scalarBytes layout (Size.ofBytes 1) bits.toNat) ∧ post trace after) =
        post trace after := by
    obtain ⟨written, success, _, _, extra, _, _, encoded⟩ := MemoryWP.writeInt_of_bytes
      (allocation.setExtra after) layout (allocRange offset (Size.ofBytes 1)) value bits cleared
      storage mutable maskLength maskValid (by change (1 : UInt64) ≠ 0; decide)
      (by change 1 ≤ 16; decide) bound conversion clear
    rw [success]
    have retains : written.extra = after := extra
    have storedBytes : written.getBytesUnchecked (allocRange offset (Size.ofBytes 1)) =
        .ok (MemoryWP.scalarBytes layout (Size.ofBytes 1) bits.toNat) := encoded
    simp only [retains, storedBytes, true_and]
  simp only [stored]

end Miri.Verification.PointerSuccessorWP

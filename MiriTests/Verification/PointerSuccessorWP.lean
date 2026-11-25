import Miri.Verification.PointerSuccessorWP
import Init.Internal.Order.While

namespace MiriTests.Verification.PointerSuccessorWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open Miri.Verification Miri.Verification.PointerSuccessorWP Std.WP

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def initialTree := BorrowTree.new BorTag.one (Size.ofBytes 1)
private def fresh : BorTag := ⟨2, by decide⟩
private def layout : TargetDataLayout := ⟨.little, .w64⟩
private def range := allocRange Size.ZERO (Size.ofBytes 1)

private theorem rootFormed : initialTree.locations.WellFormed := DedupRangeMap.new_wellFormed ..
private theorem oneByteBound : (Size.ofBytes 1).bytes ≤ initialTree.locations.size.bytes := by decide

private def rootLocation : LocationTree :=
  { perms := ⟨#[some ⟨.Unique, true, .None⟩]⟩ }

private theorem root_at {byte : UInt64} {location : LocationTree}
    (found : initialTree.locations.MapAt byte location) : location = rootLocation := by
  obtain ⟨position, segment, entry, _, content⟩ := found
  change (#[⟨⟨0, 1⟩, rootLocation⟩] : Array (RangeMapSegment LocationTree))[position]? = some segment at entry
  have inside := (Array.getElem?_eq_some_iff.mp entry).choose
  have first : position = 0 := by simp at inside; omega
  subst position
  simp at entry
  subst segment
  exact content.symm

/-- Any initialized byte of the allocation is observed through the child
created by shared formation. Only the allocation-local permission stages
are reduced for this proof. -/
theorem shared_observes (byte : UInt8) :
    ∃ initial : Allocation Provenance Unit,
      Allocation.fromBytes #[byte] Align.ONE .Mut = .ok initial ∧
      wp (access .shared (.concrete BorTag.one) fresh Size.ZERO {} .Read)
        (fun _ after =>
          (((initial.mapExtra fun _ => after).readScalar layout range false).toOption.bind
            fun scalar => scalar.toUInt8.toOption) = some byte ∧
          (after.indexOfTag fresh).isSome = true)
        (fun _ _ => False) initialTree := by
  obtain ⟨initial, made, size, _⟩ := Allocation.Bridge.fromBytes_exists_bridge (P := Provenance)
    #[byte] Align.ONE 1 .Mut rfl rfl (by change 1 < 2 ^ 64; decide)
  have one : initial.byteSize = Size.ofBytes 1 := size
  have facts := Allocation.Bridge.fromBytes_ok_bridge _ _ _ initial made
  have bytes : initial.getBytesUnchecked range = .ok #[byte] := by
    simpa only [one, range] using facts.2.2.2.2.2.2.2
  have init : initial.initializationMask.isRangeInitialized range = .ok (.ok ()) := by
    rw [facts.2.2.2.2.2.2.1, one]
    cbv
  refine ⟨initial, made, ?_⟩
  apply (wp_initializedRead .shared (.concrete BorTag.one) fresh Size.ZERO {} (initial.mapExtra fun _ => initialTree)
    layout byte bytes init (fun _ _ after => (after.indexOfTag fresh).isSome = true) _).mpr
  change wp (access .shared (.concrete BorTag.one) fresh Size.ZERO {} .Read) _ _ initialTree
  rw [wp_checked _ _ _ _ _ _ _ _ rootFormed rfl oneByteBound]
  simp only [Formation.frozen, Miri.Verification.TreeOverlapWP.accessBytePre,
    Miri.Verification.TreeOverlapWP.byteChecks]
  refine ⟨⟨by cbv, ?_⟩, by cbv <;> trivial⟩
  intro index location found _
  rw [root_at found]
  cbv

/-- Mutable formation installs the child before the successor write. Raw
formation instead uses the initial root and never inserts the prospective tag. -/
theorem mutable_and_raw_write :
    wp (access .mutable (.concrete BorTag.one) fresh Size.ZERO {} .Write)
      (fun _ after => (after.indexOfTag fresh).isSome = true) (fun _ _ => False) initialTree ∧
    wp (access .raw (.concrete BorTag.one) fresh Size.ZERO {} .Write)
      (fun _ after => after.indexOfTag fresh = none) (fun _ _ => False) initialTree := by
  constructor <;>
    rw [wp_checked _ _ _ _ _ _ _ _ rootFormed rfl oneByteBound] <;>
    simp only [Formation.frozen, Miri.Verification.TreeOverlapWP.accessBytePre,
      Miri.Verification.TreeOverlapWP.byteChecks]
  all_goals
    refine ⟨⟨by cbv, ?_⟩, by cbv <;> trivial⟩
    intro index location found _
    rw [root_at found]
    cbv

/-- A store through either writable form produces the requested byte for
any original byte and any value to store. -/
theorem writes_symbolic_byte (old written : UInt8) (form : Formation)
    (writable : form = .mutable ∨ form = .raw) :
    ∃ initial : Allocation Provenance Unit,
      Allocation.fromBytes #[old] Align.ONE .Mut = .ok initial ∧
      wp (access form (.concrete BorTag.one) fresh Size.ZERO {} .Write)
        (fun _ after =>
          match Allocation.writeScalar layout range (Scalar.fromScalarInt (ScalarInt.ofUInt8 written))
              ((initial.mapExtra fun _ => initialTree).setExtra after) with
          | .error _ _ => False
          | .ok () updated => updated.extra = after ∧ updated.getBytesUnchecked range = .ok #[written])
        (fun _ _ => False) initialTree := by
  obtain ⟨initial, made, size, _⟩ := Allocation.Bridge.fromBytes_exists_bridge (P := Provenance)
    #[old] Align.ONE 1 .Mut rfl rfl (by change 1 < 2 ^ 64; decide)
  have one : initial.byteSize = Size.ofBytes 1 := size
  obtain ⟨storageSize, storage, mutable, _, _, provenance, mask, _⟩ :=
    Allocation.Bridge.fromBytes_ok_bridge _ _ _ initial made
  have len : initial.initializationMask.len = initial.byteSize := by rw [mask]; rfl
  have valid : InitMask.WriteProof.WellFormed initial.initializationMask := by rw [mask]; trivial
  have bound : Size.ZERO.bytes.toNat + 1 ≤ initial.byteSize.bytes.toNat := by rw [one]; decide
  have clear image :
      initial.provenanceMap.clear range image (Size.fromBits layout.pointerWidth.bits) =
        .ok () ProvenanceMap.new := by
    rw [provenance]
    exact ProvenanceMap.clear_new range image _ (Size.ofBytes 1) (by decide) rfl
  let bits : U128 := BitVec.ofNat 128 written.toNat
  have encoded : MemoryWP.scalarBytes layout (Size.ofBytes 1) bits.toNat = #[written] := by
    have small : written.toNat < 256 := written.toNat_lt_size
    have fits : written.toNat < 2 ^ 128 := Nat.lt_trans small (by decide)
    apply Array.ext
    · rfl
    · intro index first second
      have bounded : index < 1 := first
      have zero : index = 0 := by omega
      subst index
      simp only [MemoryWP.scalarBytes, Array.getElem_ofFn, layout, bits, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt fits]
      change UInt8.ofNat (written.toNat / 1 % 256) = written
      simp [Nat.mod_eq_of_lt small]
  refine ⟨initial, made, ?_⟩
  have physical := (wp_initializedWrite form (.concrete BorTag.one) fresh Size.ZERO {}
    (initial.mapExtra fun _ => initialTree) layout (Scalar.fromScalarInt (ScalarInt.ofUInt8 written))
    bits ProvenanceMap.new (storage.trans storageSize.symm) mutable len valid bound rfl
    (fun image _ => clear image) (fun _ _ => True) (fun _ _ => False)).mpr
  rw [encoded] at physical
  have allowed : wp (access form (.concrete BorTag.one) fresh Size.ZERO {} .Write)
      (fun _ _ => True) (fun _ _ => False) initialTree := by
    rcases writable with rfl | rfl <;>
      rw [wp_checked _ _ _ _ _ _ _ _ rootFormed rfl oneByteBound] <;>
      simp only [Formation.frozen, TreeOverlapWP.accessBytePre, TreeOverlapWP.byteChecks]
    all_goals
      refine ⟨⟨by cbv, ?_⟩, by cbv <;> trivial⟩
      intro index location found _
      rw [root_at found]
      cbv <;> trivial
  have guarantee := physical allowed
  have starts : (initial.mapExtra fun _ => initialTree).extra = initialTree := rfl
  cases observed : access form (.concrete BorTag.one) fresh Size.ZERO {} .Write initialTree with
  | error error after =>
    simp only [starts, wp, WP.wpTrans, observed] at guarantee
  | ok trace after =>
    simp only [starts, wp, WP.wpTrans, observed, range] at guarantee ⊢
    generalize writtenResult : Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 1))
      (Scalar.fromScalarInt (ScalarInt.ofUInt8 written))
      ((initial.mapExtra fun _ => initialTree).setExtra after) = result at guarantee ⊢
    cases result with
    | error error retained => exact guarantee
    | ok value updated =>
      cases value
      exact ⟨guarantee.1, guarantee.2.1⟩

#print axioms shared_observes
#print axioms mutable_and_raw_write
#print axioms writes_symbolic_byte

end MiriTests.Verification.PointerSuccessorWP

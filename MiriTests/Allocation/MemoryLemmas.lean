import Miri.Memory.AllocationVerification
import Miri.Memory.Pointer

/-!
Kernel-checked non-vacuity and integration witnesses for the memory specification
lemmas in `Miri.Memory.InitMaskVerification`,
`Miri.Memory.ProvenanceMapVerification`, and
`Miri.Memory.AllocationVerification`.

These theorems confirm that the preconditions of the general lemmas are jointly
satisfiable and compose across materialized 64-bit word boundaries, little- and
big-endian scalar roundtrips, provenance-stripping reads, partial-range writes,
and repeated/single initialized copies.
-/

namespace MiriTests.Allocation.MemoryLemmas

open Miri.ABI
open Miri.Memory

set_option autoImplicit false

/-- Exercises all 7 `InitMask.WriteProof` specification lemmas across two 64-bit
word boundaries (`64` and `128`), including `.Lazy` → `.Materialized` partial
writes, disjoint-frame preservation, `prepareCopy_of_uniform`, and
`applyCopy_singleton`. -/
theorem initMask_materialized_chain :
    ∃ (u uCopy : InitMask) (b0 : Bool) (bad : AllocRange),
      (InitMask.new (Size.ofBytes 200) false).get Size.ZERO = .ok b0 ∧
      (InitMask.new (Size.ofBytes 200) false).setRange
        (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) true = .ok u ∧
      u.get (Size.ofBytes 59) = .ok false ∧ u.get (Size.ofBytes 60) = .ok true ∧
      u.get (Size.ofBytes 63) = .ok true ∧ u.get (Size.ofBytes 64) = .ok true ∧
      u.get (Size.ofBytes 127) = .ok true ∧ u.get (Size.ofBytes 128) = .ok true ∧
      u.get (Size.ofBytes 139) = .ok true ∧ u.get (Size.ofBytes 140) = .ok false ∧
      u.isRangeInitialized (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) = .ok (.ok ()) ∧
      (u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ()) ↔
        (InitMask.new (Size.ofBytes 200) false).isRangeInitialized
          (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.ok ())) ∧
      u.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 60)) = .ok (.error bad) ∧
      u.prepareCopy (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) = .ok ⟨true, #[80]⟩ ∧
      u.applyCopy ⟨true, #[80]⟩ (allocRange Size.ZERO (Size.ofBytes 80)) 2 = .ok uCopy := by
  let m0 := InitMask.new (Size.ofBytes 200) false
  have hwf0 : InitMask.WriteProof.WellFormed m0 := True.intro
  let ⟨b0, hb0⟩ := InitMask.WriteProof.get_ok_of_wellFormed m0 Size.ZERO hwf0 (by decide)
  have hend : (allocRange (Size.ofBytes 60) (Size.ofBytes 80)).endExclusive =
      .ok (Size.ofBytes 140) := by decide
  let ⟨u, hu, hlen, hwfu⟩ := InitMask.WriteProof.set_range_exists m0
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) true hwf0 hend
    (by decide) (by decide)
  have hget : ∀ idx : Size, idx.bytes.toNat < 200 → u.get idx =
      if 60 ≤ idx.bytes.toNat ∧ idx.bytes.toNat < 140 then .ok true else .ok false :=
    fun idx hidx => InitMask.WriteProof.set_range_get m0 u
      (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) idx true hwf0 hend
      (by decide) (by decide) hidx hu
  have his := InitMask.WriteProof.isRangeInitialized_after_setRange_true m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) hwf0 hend
    (by decide) (by decide) hu
  have hfr := InitMask.WriteProof.isRangeInitialized_frame m0 u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (allocRange Size.ZERO (Size.ofBytes 60))
    (Size.ofBytes 140) (Size.ofBytes 60) true hwf0 hend (by decide)
    (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide)) hu
  have h59 : u.get (Size.ofBytes 59) = .ok false := by rw [hget _ (by decide)]; decide
  let ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff u
    (allocRange Size.ZERO (Size.ofBytes 60)) (Size.ofBytes 60) hwfu (by decide)
    (by decide) (by rw [hlen]; decide)).2 ⟨Size.ofBytes 59, by decide, by decide, h59⟩
  have hprep := InitMask.WriteProof.prepareCopy_of_uniform u
    (allocRange (Size.ofBytes 60) (Size.ofBytes 80)) (Size.ofBytes 140) true hwfu hend
    (by decide) (by rw [hlen]; decide)
    (fun idx hlo hhi => by
      have hidx : idx.bytes.toNat < 200 := Nat.lt_trans hhi (by decide)
      rw [hget idx hidx, ite_eq_left ⟨hlo, hhi⟩])
  have hap := InitMask.WriteProof.applyCopy_singleton u Size.ZERO (Size.ofBytes 80)
    (Size.ofBytes 160) 2 true (by decide) (by decide)
  let ⟨uCopy, huCopy, _, _⟩ := InitMask.WriteProof.set_range_exists u
    (allocRange Size.ZERO (Size.ofBytes 160)) (Size.ofBytes 160) true hwfu (by decide)
    (by decide) (by rw [hlen]; decide)
  refine ⟨u, uCopy, b0, bad, hb0, hu, h59, ?_, ?_, ?_, ?_, ?_, ?_, ?_, his, hfr, hbad,
    hprep, hap.trans huCopy⟩ <;> rw [hget _ (by decide)] <;> decide

/-- Exercises `fromBytes_{exists,spec}`, `writeBytes_{zero_,}spec`,
`getBytesUnchecked_{size,subrange,split}`, and the `withExtra` / `mapExtra`
commutation family. -/
theorem fromBytes_writeBytes_slices_and_mapExtra :
    ∃ (alloc updated : Allocation CtfeProvenance Unit) (slice26 : Array UInt8),
      Allocation.fromBytes (Array.replicate 8 (0 : UInt8)) Align.ONE .Mut = .ok alloc ∧
      Allocation.writeBytes (Size.ofBytes 8) #[] (Size.ofBytes 8) alloc = .ok () alloc ∧
      Allocation.writeBytes (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) alloc = .ok () updated ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok #[7, 9] ∧
      updated.initializationMask.isRangeInitialized
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok (.ok ()) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) = .ok slice26 ∧
      slice26.size = 4 ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 3) (Size.ofBytes 2)) =
        .ok (slice26.extract 1 3) ∧
      updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) =
        .ok (#[7, 9] ++ #[0, 0, 0, 0]) ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).byteSize = updated.byteSize ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).len = updated.len ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).align = updated.align ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).mutability = updated.mutability ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).provenanceMap = updated.provenanceMap ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).initializationMask =
        updated.initializationMask ∧
      ((updated.withExtra (42 : Nat)).mapExtra (· + 1)).getBytesUnchecked
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).getBytesStripProvenance ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) =
        updated.getBytesStripProvenance ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) ∧
      (updated.mapExtra id).readScalar ⟨.little, .w64⟩
        (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false =
        updated.readScalar ⟨.little, .w64⟩
          (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) false ∧
      Allocation.writeBytes (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) (alloc.mapExtra id) =
        .ok () (updated.mapExtra id) ∧
      Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
        (updated.mapExtra id) =
        (match Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
            (Size.ofBytes 8) updated with
         | .ok v s => .ok v (s.mapExtra id)
         | .error e s => .error e (s.mapExtra id)) := by
  let ⟨alloc, hcreated, _, _⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    (Array.replicate 8 0) Align.ONE 1 .Mut rfl rfl (by decide)
  let ⟨hbs, hlen, hmut, _, _, hprov, hmask, hwf, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hzero := Allocation.writeBytes_zero_spec (Size.ofBytes 8) (Size.ofBytes 8) #[] alloc
    rfl (hlen.trans hbs.symm) (by rw [hbs]; decide)
  let ⟨updated, hw, hbsU, hlenU, _, _, _, _, _, _, _, hinit, _, hget22, hframe⟩ :=
    Allocation.writeBytes_spec (Size.ofBytes 2) (Size.ofBytes 8) #[7, 9] alloc ProvenanceMap.new
      (by decide) (hlen.trans hbs.symm) hmut (by rw [hmask]; rfl) hwf (by rw [hbs]; decide)
      (fun _ _ => by
        rw [hprov]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 4) (by decide) (by decide))
  have hget44 : updated.getBytesUnchecked (allocRange (Size.ofBytes 4) (Size.ofBytes 4)) =
      .ok #[0, 0, 0, 0] := by
    rw [hframe _ (Size.ofBytes 8) (by decide) (by decide) (by rw [hbs]; decide) (by decide),
      hslice _ (Size.ofBytes 8) (by decide) (by decide) (by decide)]
    decide
  have hstorU : updated.len = updated.byteSize.bytes.toNat :=
    hlenU.trans (hlen.trans (hbs.symm.trans (congrArg (·.bytes.toNat) hbsU.symm)))
  let ⟨slice26, hget24, hsz24⟩ := Allocation.getBytesUnchecked_size updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (Size.ofBytes 6) hstorU
    (by decide) (by decide) (by rw [hbsU, hbs]; decide)
  have hsub := Allocation.getBytesUnchecked_subrange updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 4)) (allocRange (Size.ofBytes 3) (Size.ofBytes 2))
    (Size.ofBytes 6) (Size.ofBytes 5) slice26 (by decide) (by decide)
    (by decide) (by decide) (by decide) hget24
  have hsplit := Allocation.getBytesUnchecked_split updated
    (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) (allocRange (Size.ofBytes 4) (Size.ofBytes 4))
    (allocRange (Size.ofBytes 2) (Size.ofBytes 6)) (Size.ofBytes 4) (Size.ofBytes 8)
    #[7, 9] #[0, 0, 0, 0] (by decide) rfl (by decide) rfl (by decide)
    (by decide) (by decide) hget22 hget44
  have hw_map := Allocation.writeBytes_mapExtra (Size.ofBytes 2) #[7, 9] (Size.ofBytes 8) alloc id
  rw [hw] at hw_map
  refine ⟨alloc, updated, slice26, hcreated, hzero, hw, hget22, hinit, hget44, hget24,
    hsz24, hsub, hsplit,
    (Allocation.byteSize_mapExtra _ _).trans (Allocation.byteSize_withExtra _ _),
    (Allocation.len_mapExtra _ _).trans (Allocation.len_withExtra _ _),
    (Allocation.align_mapExtra _ _).trans (Allocation.align_withExtra _ _),
    (Allocation.mutability_mapExtra _ _).trans (Allocation.mutability_withExtra _ _),
    (Allocation.provenanceMap_mapExtra _ _).trans (Allocation.provenanceMap_withExtra _ _),
    (Allocation.initializationMask_mapExtra _ _).trans (Allocation.initializationMask_withExtra _ _),
    (Allocation.getBytesUnchecked_mapExtra _ _ _).trans
      (Allocation.getBytesUnchecked_withExtra _ _ _),
    Allocation.getBytesStripProvenance_mapExtra _ _ _ _,
    Allocation.readScalar_mapExtra _ _ _ _ _,
    hw_map, ?_⟩
  rw [Allocation.clearProvenance_mapExtra]
  cases Allocation.clearProvenance (allocRange Size.ZERO (Size.ofBytes 2))
    (Size.ofBytes 8) updated <;> rfl

/-- Exercises `tryNew_{exists,spec}` (`.Uninit` and `.Zero`),
`getBytesStripProvenance_{uninit_err,ok}`, `readScalar_uninit_err`,
`ProvenanceMap.rangeEmpty_new`, and `writeUninit_{zero_,}spec`. -/
theorem tryNew_strip_and_writeUninit :
    ∃ (aUninit aZero aDeinit : Allocation CtfeProvenance Unit) (bad : AllocRange),
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aUninit ∧
      aUninit.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      aUninit.readScalar ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) false =
        .error (.invalidUninitBytes (some ⟨allocRange Size.ZERO (Size.ofBytes 4), bad⟩)) ∧
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Zero
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok aZero ∧
      aZero.getBytesStripProvenance ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 4)) =
        .ok #[0, 0, 0, 0] ∧
      Allocation.writeUninit (allocRange (Size.ofBytes 8) Size.ZERO) (Size.ofBytes 8) aZero =
        .ok () aZero ∧
      Allocation.writeUninit (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8) aZero =
        .ok () aDeinit ∧
      aDeinit.initializationMask.get Size.ZERO = .ok false ∧
      aDeinit.initializationMask.get (Size.ofBytes 2) = .ok true ∧
      aDeinit.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] := by
  let ⟨aUninit, huNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  let ⟨_, _, _, _, _, _, hmaskU, _, hwfU, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit aUninit huNew
  have hmU := hmaskU rfl
  have hget0_false : aUninit.initializationMask.get Size.ZERO = .ok false := by rw [hmU]; rfl
  let ⟨bad, hbad⟩ := (InitMask.WriteProof.isRangeInitialized_nonempty_iff
    aUninit.initializationMask (allocRange Size.ZERO (Size.ofBytes 4)) (Size.ofBytes 4)
    hwfU (by decide) (by decide) (by rw [hmU]; decide)).2
    ⟨Size.ZERO, by decide, by decide, hget0_false⟩
  have hstripErr := Allocation.getBytesStripProvenance_uninit_err aUninit ⟨.little, .w64⟩ _ bad hbad
  have hreadErr := Allocation.readScalar_uninit_err aUninit ⟨.little, .w64⟩ _ bad false hbad
  let ⟨aZero, hzNew, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Zero (by decide) (by decide)
  let ⟨hbsZ, hlenZ, hmutZ, _, _, hprovZ, _, hmaskZ, hwfZ, hsliceZ⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Zero aZero hzNew
  have hmZ := hmaskZ rfl
  have hend4 : (allocRange Size.ZERO (Size.ofBytes 4)).endExclusive = .ok (Size.ofBytes 4) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  have hinitZ : aZero.initializationMask.isRangeInitialized
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok (.ok ()) := by
    rw [hmZ]
    exact InitMask.lazy_initialized_query _ _ _ hend4 (by decide)
  have hstripOk : aZero.getBytesStripProvenance ⟨.little, .w64⟩
      (allocRange Size.ZERO (Size.ofBytes 4)) = .ok #[0, 0, 0, 0] := by
    rw [Allocation.getBytesStripProvenance_ok aZero _ _ hinitZ
      (Or.inr (by rw [hprovZ]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps hend4))]
    exact hsliceZ _ _ hend4 (by decide) (by decide)
  have hstorZ : aZero.len = aZero.byteSize.bytes.toNat := by rw [hlenZ, hbsZ]
  have hwuZero := Allocation.writeUninit_zero_spec (allocRange (Size.ofBytes 8) Size.ZERO)
    (Size.ofBytes 8) (Size.ofBytes 8) aZero rfl hstorZ (by decide) (by decide)
    (by rw [hbsZ]; decide)
  let ⟨aDeinit, hwu, _, _, _, _, _, _, _, _, hsetF, _, hbytesEq⟩ :=
    Allocation.writeUninit_spec (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 8)
      aZero ProvenanceMap.new (by decide) hstorZ hmutZ (by rw [hmZ, hbsZ]; rfl) hwfZ
      (by rw [hbsZ]; decide)
      (fun _ _ => by
        rw [hprovZ]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 2) (by decide) (by decide))
  have hg0 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    Size.ZERO false hwfZ (by decide) (by decide) (by rw [hmZ]; decide) (by rw [hmZ]; decide) hsetF
  have hg2 := InitMask.WriteProof.set_range_get aZero.initializationMask
    aDeinit.initializationMask (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2)
    (Size.ofBytes 2) false hwfZ (by decide) (by decide) (by rw [hmZ]; decide)
    (by rw [hmZ]; decide) hsetF
  have hmZ0 : aZero.initializationMask.get Size.ZERO = .ok true := by rw [hmZ]; rfl
  have hmZ2 : aZero.initializationMask.get (Size.ofBytes 2) = .ok true := by rw [hmZ]; rfl
  refine ⟨aUninit, aZero, aDeinit, bad, huNew, hstripErr, hreadErr, hzNew, hstripOk, hwuZero,
    hwu, ?_, ?_, (hbytesEq _).trans (hsliceZ _ _ hend4 (by decide) (by decide))⟩
  · rw [hg0, hmZ0]; decide
  · rw [hg2, hmZ2]; decide

/-- Exercises `readScalar_int_of_bytes`, `writeScalar_spec` (both `.bits` and
`.pointer` paths), `readScalar_int_roundtrip`, `readScalar_ptr_none_roundtrip`,
`readScalar_ptr_roundtrip`, and `ProvenanceMap.readPtr_new` across both little-
and big-endian targets. -/
theorem writeScalar_and_readScalar_roundtrips (endian : Endian) :
    ∃ (a0 aBits : Allocation CtfeProvenance Unit) (p0 pPtr : Allocation Provenance Unit),
      let layout : TargetDataLayout := ⟨endian, .w64⟩
      let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
      let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
      let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
      Allocation.tryNew (Size.ofBytes 8) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok a0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) intVal a0 =
        .ok () aBits ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) false = .ok intVal ∧
      aBits.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok intVal ∧
      Allocation.tryNew (Size.ofBytes 16) Align.EIGHT .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok p0 ∧
      Allocation.writeScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) ptrVal p0 =
        .ok () pPtr ∧
      pPtr.readScalar layout (allocRange Size.ZERO (Size.ofBytes 8)) true = .ok ptrVal ∧
      pPtr.getBytesUnchecked (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) =
        .ok (Array.replicate 8 0) := by
  let layout : TargetDataLayout := ⟨endian, .w64⟩
  let bits : U128 := BitVec.ofNat 128 (0x0102030405060708 : UInt64).toNat
  let intVal : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0x0102030405060708)
  let r08 := allocRange Size.ZERO (Size.ofBytes 8)
  have hend08 : r08.endExclusive = .ok (Size.ofBytes 8) := by decide
  have hps_eq : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by
    dsimp only [layout]; decide
  have hps_nz : (Size.fromBits layout.pointerWidth.bits).bytes ≠ 0 := by
    dsimp only [layout]; decide
  let ⟨a0, ha0, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.EIGHT 8 .Uninit (by decide) (by decide)
  let ⟨hbs0, hlen0, hmut0, _, _, hprov0, hmask0, _, hwf0, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.EIGHT .Uninit a0 ha0
  let ⟨aBits, hwBits, _, _, _, _, _, _, _, _, _, hisBits, hprovBits, hbytesBits, _, _⟩ :=
    Allocation.writeScalar_spec layout a0 r08 intVal (.bits bits) ProvenanceMap.new ProvenanceMap.new
      (by rw [hlen0, hbs0]) hmut0 (by rw [hmask0 rfl, hbs0]; rfl) hwf0
      (by decide) (by decide) (by rw [hbs0]; decide) (by decide)
      (fun _ _ => by
        rw [hprov0, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      rfl
  have hfromUInt : (Scalar.fromUInt (Prov := CtfeProvenance) bits r08.size).mapError
      AllocError.scalar = .ok intVal := by decide
  have hreadInt := Allocation.readScalar_int_roundtrip aBits layout r08 bits
    hisBits (by decide) (by decide)
    (Or.inr (by rw [hprovBits]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps_nz hend08))
    (hbytesBits bits rfl)
  have hreadPtrNone := Allocation.readScalar_ptr_none_roundtrip aBits layout r08 bits
    hisBits hps_eq.symm (by decide) (by decide)
    (by rw [hprovBits, hps_eq]; exact ProvenanceMap.readPtr_new _ _ _ (by decide) hend08)
    (hbytesBits bits rfl)
  let ptr : Pointer Provenance := ⟨Size.ofBytes 0x1020, .wildcard⟩
  let ptrVal : Scalar Provenance := Scalar.fromPointer layout ptr
  let ⟨pm1, hpm1_ins, hpm1_ptrs⟩ :
      ∃ pm1 : ProvenanceMap Provenance,
        ProvenanceMap.insertPtr Size.ZERO Provenance.wildcard (Size.ofBytes 8) ProvenanceMap.new =
          .ok () pm1 ∧
        pm1.ptrs = #[(Size.ZERO, Provenance.wildcard)] :=
    ⟨_, ProvenanceMap.insertPtr_new Size.ZERO (Size.ofBytes 8) (Size.ofBytes 8)
      Provenance.wildcard (by decide) hend08, rfl⟩
  have hconvPtr : ptrVal.toBitsOrPtrInternal r08.size = .ok (.pointer ptr) := by
    cases endian <;> decide
  let ⟨p0, hp0, _⟩ := Allocation.tryNew_exists (P := Provenance)
    (Size.ofBytes 16) Align.EIGHT 8 .Uninit (by decide) (by decide)
  let ⟨hbsP, hlenP, hmutP, _, _, hprovP, hmaskP, _, hwfP, hsliceP⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 16) Align.EIGHT .Uninit p0 hp0
  let ⟨pPtr, hwPtr, _, _, _, _, _, _, _, _, _, hisPtr, hprovPtr, _, hbytesPtr, hframePtr⟩ :=
    Allocation.writeScalar_spec layout p0 r08 ptrVal (.pointer ptr) ProvenanceMap.new pm1
      (by rw [hlenP, hbsP]) hmutP (by rw [hmaskP rfl, hbsP]; rfl) hwfP
      (by decide) (by decide) (by rw [hbsP]; decide) hconvPtr
      (fun _ _ => by
        rw [hprovP, hps_eq]
        exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 8) (by decide) hend08)
      ⟨hps_eq.symm, by rw [hps_eq]; exact hpm1_ins⟩
  have hpSlice : pPtr.getBytesUnchecked r08 =
      .ok (Array.ofFn (fun i : Fin r08.size.bytes.toNat =>
        UInt8.ofNat ((ptr.offset.bytes.toNat / 2 ^ (8 *
          (if layout.endian == .little then i.1 else r08.size.bytes.toNat - i.1 - 1))) % 256))) := by
    have hbv : (BitVec.ofNat 128 ptr.offset.bytes.toNat).toNat = ptr.offset.bytes.toNat := by decide
    simpa [hbv] using hbytesPtr ptr rfl
  have hgetPtr : pm1.getPtr r08.start = some ptr.provenance := by
    unfold ProvenanceMap.getPtr
    rw [hpm1_ptrs]
    decide
  have hreadPtr := Allocation.readScalar_ptr_roundtrip pPtr layout r08 ptr
    hisPtr hps_eq.symm (by decide) (by decide)
    (by rw [hprovPtr, hps_eq]; exact ProvenanceMap.read_exact_pointer pm1 _ _ _ hgetPtr) hpSlice
  have hfr8 := hframePtr (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by rw [hbsP]; decide) (Or.inl (by decide))
  have hp8 := hsliceP (allocRange (Size.ofBytes 8) (Size.ofBytes 8)) (Size.ofBytes 16)
    (by decide) (by decide) (by decide)
  exact ⟨a0, aBits, p0, pPtr, ha0, hwBits, hreadInt.trans hfromUInt,
    hreadPtrNone.trans hfromUInt, hp0, hwPtr, hreadPtr, hfr8.trans hp8⟩

/-- Exercises `readScalar_int_of_bytes` across both little- and big-endian byte
orderings. -/
theorem readScalar_int_of_bytes_endian (endian : Endian) :
    ∃ alloc : Allocation CtfeProvenance Unit,
      Allocation.fromBytes #[1, 2] Align.ONE .Not = .ok alloc ∧
      alloc.readScalar ⟨endian, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 2)) false =
        (Scalar.fromUInt (BitVec.ofNat 128 (if endian == .little then 0x0201 else 0x0102))
          (Size.ofBytes 2)).mapError AllocError.scalar := by
  let ⟨alloc, hcreated, _, _⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    #[1, 2] Align.ONE 1 .Not rfl rfl (by decide)
  let ⟨hbs, _, _, _, _, hprov, hmask, _, hslice⟩ :=
    Allocation.fromBytes_spec _ _ _ alloc hcreated
  have hend : (allocRange Size.ZERO (Size.ofBytes 2)).endExclusive = .ok (Size.ofBytes 2) := by
    decide
  have hps : (Size.fromBits PointerWidth.w64.bits).bytes ≠ 0 := by decide
  refine ⟨alloc, hcreated, ?_⟩
  rw [Allocation.readScalar_int_of_bytes alloc _ _ #[1, 2]
    (by
      rw [hmask]
      exact InitMask.lazy_initialized_query _ _ _ hend
        (UInt64.le_iff_toNat_le.mpr (by rw [hbs]; decide)))
    (hslice _ _ hend (by decide) (by decide)) (by decide)
    (Or.inr (by rw [hprov]; exact ProvenanceMap.rangeEmpty_new _ _ _ hps hend))]
  cases endian <;> rfl

/-- Exercises `ProvenanceMap.prepareCopy_new`, `ProvenanceMap.applyCopy_empty`,
`Allocation.copyRepeatedly_initialized_spec` (distinct-allocation repeated copy
and same-allocation nonoverlapping repeated copy), and
`Allocation.copy_initialized_spec`. -/
theorem copy_and_copyRepeatedly_initialized :
    ∃ (src dst rep single sameRep : Allocation CtfeProvenance Unit),
      Allocation.fromBytes #[10, 20] Align.ONE .Not = .ok src ∧
      Allocation.tryNew (Size.ofBytes 8) Align.ONE .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok dst ∧
      Allocation.copyRepeatedly src (allocRange Size.ZERO (Size.ofBytes 2))
        (Size.ofBytes 1) 3 (Size.ofBytes 8) false true dst = .ok () rep ∧
      rep.getBytesUnchecked (allocRange (Size.ofBytes 1) (Size.ofBytes 6)) =
        .ok #[10, 20, 10, 20, 10, 20] ∧
      rep.initializationMask.isRangeInitialized (allocRange (Size.ofBytes 1) (Size.ofBytes 6)) =
        .ok (.ok ()) ∧
      rep.initializationMask.get Size.ZERO = .ok false ∧
      rep.initializationMask.get (Size.ofBytes 7) = .ok false ∧
      Allocation.copy src (allocRange Size.ZERO (Size.ofBytes 2))
        (Size.ofBytes 2) (Size.ofBytes 8) false true dst = .ok () single ∧
      single.getBytesUnchecked (allocRange (Size.ofBytes 2) (Size.ofBytes 2)) = .ok #[10, 20] ∧
      Allocation.copyRepeatedly rep (allocRange (Size.ofBytes 1) (Size.ofBytes 2))
        (Size.ofBytes 3) 2 (Size.ofBytes 8) true true rep = .ok () sameRep ∧
      sameRep.getBytesUnchecked (allocRange (Size.ofBytes 3) (Size.ofBytes 4)) =
        .ok #[10, 20, 10, 20] ∧
      sameRep.getBytesUnchecked (allocRange (Size.ofBytes 1) (Size.ofBytes 2)) =
        .ok #[10, 20] := by
  let ⟨src, hsrc, _, _⟩ := Allocation.fromBytes_exists (P := CtfeProvenance)
    #[10, 20] Align.ONE 1 .Not rfl rfl (by decide)
  let ⟨hbsS, hlenS, _, _, _, hprovS, hmaskS, hwfS, hsliceS⟩ :=
    Allocation.fromBytes_spec _ _ _ src hsrc
  have hstorS : src.len = src.byteSize.bytes.toNat := hlenS.trans hbsS.symm
  have hendS : (allocRange Size.ZERO (Size.ofBytes 2)).endExclusive = .ok (Size.ofBytes 2) := by
    decide
  have hinitS : src.initializationMask.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 2)) =
      .ok (.ok ()) := by
    rw [hmaskS]
    exact InitMask.lazy_initialized_query _ _ _ hendS (UInt64.le_iff_toNat_le.mpr (by rw [hbsS]; decide))
  have hbytesS : src.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 2)) = .ok #[10, 20] := by
    exact (hsliceS _ _ hendS (by decide) (by decide)).trans (by decide)
  let ⟨dst, hdst, _⟩ := Allocation.tryNew_exists (P := CtfeProvenance)
    (Size.ofBytes 8) Align.ONE 1 .Uninit (by decide) (by decide)
  let ⟨hbsD, hlenD, hmutD, _, _, hprovD, hmaskD, _, hwfD, _⟩ :=
    Allocation.tryNew_spec (Size.ofBytes 8) Align.ONE .Uninit dst hdst
  have hstorD : dst.len = dst.byteSize.bytes.toNat := by rw [hlenD, hbsD]
  have hmD := hmaskD rfl
  let ⟨rep, hrep, hbsR, hlenR, hmutR, _, _, _, hmlR, hwfR, hisR, hgetR, _, hprovR, hbytesR, _⟩ :=
    Allocation.copyRepeatedly_initialized_spec src dst
      (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2) (Size.ofBytes 1)
      (Size.ofBytes 6) (Size.ofBytes 8) 3 false true #[10, 20] ⟨#[], #[]⟩
      ProvenanceMap.new ProvenanceMap.new
      hstorS hendS (by decide) (by rw [hmaskS]; rfl) hwfS hinitS hbytesS (by rw [hbsS]; decide)
      (fun _ _ => by rw [hprovS]; exact ProvenanceMap.prepareCopy_new _ _ _ (Size.ofBytes 2) (by decide) hendS)
      (by decide) (by decide) (fun _ => rfl) (fun h => by cases h)
      hstorD hmutD (by rw [hmD, hbsD]; rfl) hwfD (by rw [hbsD]; decide)
      (fun _ _ => by rw [hprovD]; exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 7) (by decide) (by decide))
      (ProvenanceMap.applyCopy_empty _ _ _)
  have hrepBytes : rep.getBytesUnchecked (allocRange (Size.ofBytes 1) (Size.ofBytes 6)) =
      .ok #[10, 20, 10, 20, 10, 20] := hbytesR.trans (by decide)
  have hrep0 : rep.initializationMask.get Size.ZERO = .ok false := by
    rw [hgetR Size.ZERO (by rw [hbsD]; decide)]
    simp [hmD]; rfl
  have hrep7 : rep.initializationMask.get (Size.ofBytes 7) = .ok false := by
    rw [hgetR (Size.ofBytes 7) (by rw [hbsD]; decide)]
    simp [hmD]; rfl
  let ⟨single, hsingle, _, _, _, _, _, _, _, _, _, _, _, _, hbytesSingle, _⟩ :=
    Allocation.copy_initialized_spec src dst
      (allocRange Size.ZERO (Size.ofBytes 2)) (Size.ofBytes 2) (Size.ofBytes 2) (Size.ofBytes 8)
      false true #[10, 20] ⟨#[], #[]⟩ ProvenanceMap.new ProvenanceMap.new
      hstorS hendS (by decide) (by rw [hmaskS]; rfl) hwfS hinitS hbytesS (by rw [hbsS]; decide)
      (fun _ _ => by rw [hprovS]; exact ProvenanceMap.prepareCopy_new _ _ _ (Size.ofBytes 2) (by decide) hendS)
      (fun h => by cases h)
      hstorD hmutD (by rw [hmD, hbsD]; rfl) hwfD (by rw [hbsD]; decide)
      (fun _ _ => by rw [hprovD]; exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 4) (by decide) (by decide))
      (ProvenanceMap.applyCopy_empty _ _ _)
  have hstorR : rep.len = rep.byteSize.bytes.toNat := by rw [hlenR, hbsR, hlenD, hbsD]
  have hmlR' : rep.initializationMask.len = rep.byteSize := by rw [hmlR, hmD, hbsR, hbsD]; rfl
  have hrep12Bytes : rep.getBytesUnchecked (allocRange (Size.ofBytes 1) (Size.ofBytes 2)) =
      .ok #[10, 20] := by
    have hsub := Allocation.getBytesUnchecked_subrange rep
      (allocRange (Size.ofBytes 1) (Size.ofBytes 6))
      (allocRange (Size.ofBytes 1) (Size.ofBytes 2))
      (Size.ofBytes 7) (Size.ofBytes 3) #[10, 20, 10, 20, 10, 20]
      (by decide) (by decide) (by decide) (by decide) (by decide) hrepBytes
    exact hsub.trans (by decide)
  have hrep12Init : rep.initializationMask.isRangeInitialized
      (allocRange (Size.ofBytes 1) (Size.ofBytes 2)) = .ok (.ok ()) := by
    rw [(InitMask.WriteProof.isRangeInitialized_nonempty_iff rep.initializationMask
      (allocRange (Size.ofBytes 1) (Size.ofBytes 2)) (Size.ofBytes 3) hwfR (by decide)
      (by decide) (by rw [hmlR', hbsR, hbsD]; decide)).1]
    intro idx hlo hhi
    change 1 ≤ idx.bytes.toNat at hlo
    change idx.bytes.toNat < 3 at hhi
    rw [hgetR idx (by rw [hbsD]; exact Nat.lt_trans hhi (by decide))]
    rw [ite_eq_left ⟨hlo, Nat.lt_trans hhi (by decide)⟩]
  let ⟨sameRep, hsameRep, _, _, _, _, _, _, _, _, _, _, _, _, hbytesSame, hframeSame⟩ :=
    Allocation.copyRepeatedly_initialized_spec rep rep
      (allocRange (Size.ofBytes 1) (Size.ofBytes 2)) (Size.ofBytes 3) (Size.ofBytes 3)
      (Size.ofBytes 4) (Size.ofBytes 8) 2 true true #[10, 20] ⟨#[], #[]⟩
      ProvenanceMap.new ProvenanceMap.new
      hstorR (by decide) (by decide) hmlR' hwfR hrep12Init hrep12Bytes (by rw [hbsR, hbsD]; decide)
      (fun _ _ => by rw [hprovR]; exact ProvenanceMap.prepareCopy_new _ _ _ (Size.ofBytes 3) (by decide) (by decide))
      (by decide) (by decide) (fun _ => rfl) (fun _ _ => Or.inl (by decide))
      hstorR (by rw [hmutR, hmutD]) hmlR' hwfR (by rw [hbsR, hbsD]; decide)
      (fun _ _ => by rw [hprovR]; exact ProvenanceMap.clear_new _ _ _ (Size.ofBytes 7) (by decide) (by decide))
      (ProvenanceMap.applyCopy_empty _ _ _)
  have hsame12 : sameRep.getBytesUnchecked (allocRange (Size.ofBytes 1) (Size.ofBytes 2)) =
      .ok #[10, 20] := by
    rw [hframeSame _ (Size.ofBytes 3) (by decide) (by decide) (by rw [hbsR, hbsD]; decide)
      (Or.inr (by decide))]
    exact hrep12Bytes
  exact ⟨src, dst, rep, single, sameRep, hsrc, hdst, hrep, hrepBytes, hisR, hrep0, hrep7,
    hsingle, hbytesSingle, hsameRep, hbytesSame.trans (by decide), hsame12⟩

end MiriTests.Allocation.MemoryLemmas

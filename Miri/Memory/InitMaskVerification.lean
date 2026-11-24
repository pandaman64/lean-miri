import Miri.Memory.InitMask

/-! Pointwise bit-query, range-initialization, disjoint-frame, and uniform-copy
specifications for `Miri.Memory.InitMask`, kept in a companion verification
module off the interpreter critical path. -/

namespace Miri.Memory.InitMask.WriteProof

open Miri.ABI
open Miri.Memory
open Miri.Memory.InitMask.Bridge

set_option autoImplicit false

private abbrev mask64 : Nat := 18446744073709551615

private def setW (word lo hi : Nat) (state : Bool) : UInt64 :=
  let mask := (2 ^ hi - 1) - (2 ^ lo - 1)
  UInt64.ofNat (if state then Nat.lor word mask else Nat.land word (mask64 - mask))

private def getB (ws : Array UInt64) (i : Nat) : Except InitMaskError UInt64 :=
  match ws[i]? with
  | some w => .ok w
  | none => .error (.blockIndexOutOfBounds i ws.size)

private def setB (ws : Array UInt64) (i : Nat) (w : UInt64) : Except InitMaskError (Array UInt64) :=
  if h : i < ws.size then .ok (ws.set i w h) else .error (.blockIndexOutOfBounds i ws.size)

private def updW (ws : Array UInt64) (i : Nat) (f : UInt64 → UInt64) :
    Except InitMaskError (Array UInt64) := do
  let w ← getB ws i
  setB ws i (f w)

private def fillStep (state : Bool) (i : Nat) (ws : Array UInt64) :
    Except InitMaskError (ForInStep (Array UInt64)) := do
  let next ← setB ws i (if state then UInt64.ofNat mask64 else 0)
  return ForInStep.yield next

private def setRangeWords (words : Array UInt64) (bA rA bB rB : Nat) (state : Bool) :
    Except InitMaskError (Array UInt64) := do
  if bA == bB then
    updW words bA (fun w => setW w.toNat rA (if rB == 0 then 64 else rB) state)
  else
    let initial ← updW words bA (fun w => setW w.toNat rA 64 state)
    let middle ← if rB != 0 then updW initial bB (fun w => setW w.toNat 0 rB state) else pure initial
    forIn (Std.Legacy.Range.mk (bA + 1) bB 1 (by decide)) middle (fillStep state)

private def sizeFromN (n : Nat) : Except InitMaskError Size :=
  if n ≤ mask64 then .ok (Size.ofBytes (UInt64.ofNat n))
  else .error (.sizeFromNatOverflow n)

private def searchBlk (word : UInt64) (block startBit : Nat) (isInit : Bool) :
    Except InitMaskError (Option Size) := do
  let bits := if isInit then word.toNat else mask64 - word.toNat
  match ((List.range (64 - startBit)).find? fun offset =>
      Nat.testBit bits (startBit + offset)).map (· + startBit) with
  | none => return none
  | some bit => return some (← sizeFromN (block * 64 + bit))

private def findBitPub (words : Array UInt64) (start fin : Size) (isInit : Bool) :
    Except InitMaskError (Option Size) := do
  let startBytes := start.bytes.toNat
  let finishBytes := fin.bytes.toNat
  if startBytes >= finishBytes then return none
  let (startBlock, startBit) := (startBytes / 64, startBytes % 64)
  let endInclusive ← sizeFromN (finishBytes - 1)
  let (endBlockInclusive, _) := (endInclusive.bytes.toNat / 64, endInclusive.bytes.toNat % 64)
  let first ← searchBlk (← getB words startBlock) startBlock startBit isInit
  match first with
  | some index =>
    if index.bytes.toNat < finishBytes then return some index else return none
  | none =>
    if startBlock < endBlockInclusive then
      for block in [startBlock + 1:endBlockInclusive + 1] do
        match ← searchBlk (← getB words block) block 0 isInit with
        | some index =>
          if index.bytes.toNat < finishBytes then return some index else return none
        | none => pure ()
    return none

private theorem mod64_lt (n : Nat) : n % 64 < 64 := Nat.mod_lt n (by decide)

private theorem div64_lt_of_lt_mul (n sz : Nat) (h : n < sz * 64) : n / 64 < sz := by omega

private theorem div64_mul_add_eq (n : Nat) : n / 64 * 64 + n % 64 = n := by omega

private theorem block_bit_range_same (b rA rB bit : Nat) :
    (rA ≤ bit ∧ bit < rB) ↔ (b * 64 + rA ≤ b * 64 + bit ∧ b * 64 + bit < b * 64 + rB) := by
  omega

private theorem block_bit_range_out_same (b k rA rB bit : Nat) (h_rA : rA < 64) (h_rB : rB < 64)
    (h_bit : bit < 64) (h_ne : k ≠ b) :
    ¬(b * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < b * 64 + rB) := by
  omega

private theorem block_bit_range_mid (bA rA bB rB k bit : Nat) (h_rA : rA < 64) (h_bit : bit < 64)
    (h_lo : bA + 1 ≤ k) (h_hi : k < bB) :
    bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB := by
  omega

private theorem block_bit_range_hi (bA rA bB rB bit : Nat) (h_rA : rA < 64) (h_lt : bA < bB) :
    (0 ≤ bit ∧ bit < rB) ↔ (bA * 64 + rA ≤ bB * 64 + bit ∧ bB * 64 + bit < bB * 64 + rB) := by
  omega

private theorem block_bit_range_lo (bA rA bB rB bit : Nat) (h_lt : bA < bB) (h_bit : bit < 64) :
    (rA ≤ bit ∧ bit < 64) ↔ (bA * 64 + rA ≤ bA * 64 + bit ∧ bA * 64 + bit < bB * 64 + rB) := by
  omega

private theorem block_bit_range_out_diff (bA rA bB rB k bit : Nat) (h_rA : rA < 64) (h_rB : rB < 64)
    (h_bit : bit < 64)
    (h_not_mid : ¬(bA + 1 ≤ k ∧ k < bB)) (h_not_bB : ¬(rB ≠ 0 ∧ k = bB)) (h_ne_bA : k ≠ bA) :
    ¬(bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by
  omega

private theorem testBit_mask64 (bit : Nat) (h : bit < 64) :
    Nat.testBit mask64 bit = true := by
  have hm : mask64 = 2 ^ 64 - 1 := by decide
  rw [hm, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true h

private theorem testBit_mask64_sub (x bit : Nat) (h_x : x < 2 ^ 64) (h_bit : bit < 64) :
    Nat.testBit (mask64 - x) bit = !Nat.testBit x bit := by
  have h_wm : mask64 = 2 ^ 64 - 1 := by decide
  rw [h_wm]
  have h_bv : BitVec.ofNat 64 (2 ^ 64 - 1 - x) = ~~~(BitVec.ofNat 64 x) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not]
    omega
  have h1 := congrArg (fun b : BitVec 64 => b.getLsbD bit) h_bv
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_not, h_bit, decide_true, Bool.true_and] at h1
  exact h1

private theorem setW_testBit (word lo hi bit : Nat) (state : Bool)
    (h_lo_hi : lo ≤ hi) (h_hi : hi ≤ 64) (h_bit : bit < 64) :
    Nat.testBit (setW word lo hi state).toNat bit =
      if lo ≤ bit ∧ bit < hi then state else Nat.testBit word bit := by
  let mask := (2 ^ hi - 1) - (2 ^ lo - 1)
  have h_pow_lo : 1 ≤ 2 ^ lo := Nat.one_le_two_pow
  have h_pow_diff : 1 ≤ 2 ^ (hi - lo) := Nat.one_le_two_pow
  have h_sum : mask = (2 ^ (hi - lo) - 1) <<< lo := by
    have h_eq : hi = lo + (hi - lo) := by omega
    have h_pow : 2 ^ hi = 2 ^ lo * 2 ^ (hi - lo) := by
      conv => lhs; rw [h_eq]
      exact Nat.pow_add 2 lo (hi - lo)
    have h_mul : 2 ^ lo * (2 ^ (hi - lo) - 1) = 2 ^ lo * 2 ^ (hi - lo) - 2 ^ lo := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
    dsimp only [mask]
    omega
  have h_mask_lt : mask < 2 ^ 64 := by
    have : 2 ^ hi ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h_hi
    dsimp only [mask]
    omega
  have h_mask_bit : Nat.testBit mask bit = decide (lo ≤ bit ∧ bit < hi) := by
    rw [h_sum, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h_ge : lo ≤ bit
    · by_cases h_lt : bit < hi
      · have h_sub : bit - lo < hi - lo := by omega
        simp only [h_ge, h_lt, h_sub, and_self, decide_true, Bool.true_and]
      · have h_sub : ¬(bit - lo < hi - lo) := by omega
        simp only [h_ge, h_lt, h_sub, and_false, decide_true, decide_false, Bool.true_and]
    · simp only [h_ge, false_and, decide_false, Bool.false_and]
  have h_inv : Nat.testBit (mask64 - mask) bit = !Nat.testBit mask bit :=
    testBit_mask64_sub mask bit h_mask_lt h_bit
  unfold setW
  dsimp only
  cases state
  · simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (word &&& (mask64 - mask)).testBit bit = _
    rw [Nat.testBit_and, h_inv, h_mask_bit]
    by_cases h_in : lo ≤ bit ∧ bit < hi
    · rw [ite_eq_left h_in, decide_eq_true h_in, Bool.not_true, Bool.and_false]
    · rw [ite_eq_right h_in, decide_eq_false h_in, Bool.not_false, Bool.and_true]
  · simp only [↓reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (word ||| mask).testBit bit = _
    rw [Nat.testBit_or, h_mask_bit]
    by_cases h_in : lo ≤ bit ∧ bit < hi
    · rw [ite_eq_left h_in, decide_eq_true h_in, Bool.or_true]
    · rw [ite_eq_right h_in, decide_eq_false h_in, Bool.or_false]

private theorem fill_list_getElem? (indices : List Nat) (words : Array UInt64) (state : Bool)
    (updated : Array UInt64)
    (h_ok : forIn indices words (fillStep state) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if k ∈ indices then some (if state then UInt64.ofNat mask64 else 0) else words[k]? := by
  let fillWord : UInt64 := if state then UInt64.ofNat mask64 else 0
  induction indices generalizing words with
  | nil =>
    simp only [List.forIn_nil, Pure.pure, Except.pure, Except.ok.injEq] at h_ok
    subst h_ok
    exact ⟨rfl, fun _ => by simp only [List.not_mem_nil, ↓reduceIte]⟩
  | cons first rest ih =>
    simp only [List.forIn_cons, fillStep, setB, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases h_first : first < words.size
    · simp only [h_first, ↓reduceDIte] at h_ok
      obtain ⟨h_sz, h_elem⟩ := ih (words.set first fillWord h_first) h_ok
      have h_wsz : (words.set first fillWord h_first).size = words.size := Array.size_set ..
      refine ⟨h_sz.trans h_wsz, fun k => ?_⟩
      rw [h_elem k]
      by_cases h_rest : k ∈ rest
      · rw [ite_eq_left h_rest, ite_eq_left (List.mem_cons_of_mem _ h_rest)]
      · rw [ite_eq_right h_rest]
        by_cases h_eq : k = first
        · subst h_eq
          rw [ite_eq_left (List.mem_cons_self ..), Array.getElem?_set_self h_first]
        · rw [ite_eq_right (by intro hm; rcases List.mem_cons.mp hm with rfl | hr; exact h_eq rfl; exact h_rest hr)]
          exact Array.getElem?_set_ne h_first (Ne.symm h_eq)
    · simp only [h_first, ↓reduceDIte] at h_ok; cases h_ok

private theorem fill_range_getElem? (lower upper : Nat) (words : Array UInt64) (state : Bool)
    (updated : Array UInt64)
    (h_ok : forIn (Std.Legacy.Range.mk lower upper 1 (by decide)) words (fillStep state) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if lower ≤ k ∧ k < upper then some (if state then UInt64.ofNat mask64 else 0) else words[k]? := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_ok
  obtain ⟨h_sz, h_elem⟩ := fill_list_getElem? _ words state updated h_ok
  refine ⟨h_sz, fun k => ?_⟩
  rw [h_elem k]
  have h_mem : (k ∈ List.range' [lower:upper].start [lower:upper].size [lower:upper].step) ↔
      (lower ≤ k ∧ k < upper) := by
    simp only [List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro ⟨h1, h2⟩; exact ⟨k - lower, by omega, by omega⟩
  by_cases h_in : lower ≤ k ∧ k < upper
  · rw [ite_eq_left (h_mem.mpr h_in), ite_eq_left h_in]
  · rw [ite_eq_right (fun h => h_in (h_mem.mp h)), ite_eq_right h_in]

private theorem updW_getElem? (words : Array UInt64) (index : Nat)
    (transform : UInt64 → UInt64) (updated : Array UInt64)
    (h_ok : updW words index transform = .ok updated) :
    index < words.size ∧ updated.size = words.size ∧
      ∀ k, updated[k]? = if k = index then words[index]?.map transform else words[k]? := by
  unfold updW getB setB at h_ok
  by_cases h_idx : index < words.size
  · have h_get : words[index]? = some words[index] := Array.getElem?_eq_getElem h_idx
    simp only [h_get, Bind.bind, Except.bind, h_idx, ↓reduceDIte, Except.ok.injEq] at h_ok
    subst h_ok
    refine ⟨h_idx, Array.size_set .., fun k => ?_⟩
    by_cases h_eq : k = index
    · subst h_eq
      rw [ite_eq_left rfl, h_get, Option.map_some, Array.getElem?_set_self h_idx]
    · rw [ite_eq_right h_eq, Array.getElem?_set_ne h_idx (Ne.symm h_eq)]
  · have h_get : words[index]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h_idx)
    simp only [h_get, Bind.bind, Except.bind] at h_ok; cases h_ok

private theorem setRangeWords_bit_gen (words : Array UInt64) (bA rA bB rB : Nat) (state : Bool)
    (updated : Array UInt64)
    (h_rA : rA < 64) (h_rB : rB < 64)
    (h_nonempty : bA * 64 + rA < bB * 64 + rB)
    (h_ok : setRangeWords words bA rA bB rB state = .ok updated) :
    updated.size = words.size ∧
      ∀ (k bit : Nat), k < words.size → bit < 64 →
        ∃ w oldW,
          updated[k]? = some w ∧
          words[k]? = some oldW ∧
          Nat.testBit w.toNat bit =
            if bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB then
              state
            else
              Nat.testBit oldW.toNat bit := by
  unfold setRangeWords at h_ok
  by_cases h_same : bA == bB
  · simp only [h_same, ↓reduceIte] at h_ok
    have h_bA_eq : bA = bB := eq_of_beq h_same
    subst h_bA_eq
    have h_rA_lt_rB : rA < rB := Nat.lt_of_add_lt_add_left h_nonempty
    have h_rB_nz : rB ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) h_rA_lt_rB)
    obtain ⟨_, h_sz, h_elem⟩ := updW_getElem? words bA _ updated h_ok
    refine ⟨h_sz, fun k bit h_ib h_bit => ?_⟩
    have h_old : words[k]? = some (words[k]'h_ib) := Array.getElem?_eq_getElem h_ib
    by_cases h_k : k = bA
    · subst h_k
      refine ⟨setW (words[k]'h_ib).toNat rA (if rB == 0 then 64 else rB) state,
        words[k]'h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [ite_eq_left rfl, h_old] at he
        exact he
      · rw [beq_false_of_ne h_rB_nz, ite_eq_right Bool.false_ne_true]
        rw [setW_testBit _ rA rB bit state (Nat.le_of_lt h_rA_lt_rB) (Nat.le_of_lt h_rB) h_bit]
        have h_iff := block_bit_range_same k rA rB bit
        by_cases h1 : rA ≤ bit ∧ bit < rB
        · rw [ite_eq_left h1, ite_eq_left (h_iff.mp h1)]
        · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (h_iff.mpr h2))]
    · refine ⟨words[k]'h_ib, words[k]'h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [ite_eq_right h_k] at he
        exact he.trans h_old
      · rw [ite_eq_right (block_bit_range_out_same bA k rA rB bit h_rA h_rB h_bit h_k)]
  · simp only [h_same, Bool.false_eq_true, ↓reduceIte] at h_ok
    have h_lt_div : bA < bB := by
      have h_ne : bA ≠ bB := fun h => h_same (beq_iff_eq.mpr h)
      omega
    cases h_init : updW words bA (fun word => setW word.toNat rA 64 state) with
    | error _ => simp only [h_init, Bind.bind, Except.bind] at h_ok; cases h_ok
    | ok initial =>
      obtain ⟨_, h_init_sz, h_init_elem⟩ := updW_getElem? words bA _ initial h_init
      have h_mid_step : ∃ middle,
          forIn (Std.Legacy.Range.mk (bA + 1) bB 1 (by decide)) middle (fillStep state) = .ok updated ∧
          middle.size = words.size ∧
          ∀ k, middle[k]? =
            if rB ≠ 0 ∧ k = bB then initial[bB]?.map (fun word => setW word.toNat 0 rB state)
            else initial[k]? := by
        by_cases h_rB_zero : rB = 0
        · subst h_rB_zero
          simp only [h_init, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
          exact ⟨initial, h_ok, h_init_sz, fun k => by simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]⟩
        · have h_bne : (rB != 0) = true := bne_iff_ne.mpr h_rB_zero
          simp only [h_init, h_bne, ↓reduceIte, Bind.bind, Except.bind] at h_ok
          cases h_m : updW initial bB (fun word => setW word.toNat 0 rB state) with
          | error _ => simp only [h_m] at h_ok; cases h_ok
          | ok mid =>
            simp only [h_m] at h_ok
            obtain ⟨_, h_mid_sz, h_mid_elem⟩ := updW_getElem? initial bB _ mid h_m
            refine ⟨mid, h_ok, h_mid_sz.trans h_init_sz, fun k => ?_⟩
            rw [h_mid_elem k]
            by_cases hk : k = bB
            · rw [ite_eq_left hk, ite_eq_left ⟨h_rB_zero, hk⟩]
            · rw [ite_eq_right hk, ite_eq_right (fun h => hk h.2)]
      obtain ⟨middle, h_loop, h_mid_sz, h_mid_elem⟩ := h_mid_step
      let fillWord : UInt64 := if state then UInt64.ofNat mask64 else 0
      obtain ⟨h_upd_sz, h_upd_elem⟩ := fill_range_getElem? (bA + 1) bB middle state updated h_loop
      refine ⟨h_upd_sz.trans h_mid_sz, fun k bit h_ib h_bit => ?_⟩
      have h_old : words[k]? = some (words[k]'h_ib) := Array.getElem?_eq_getElem h_ib
      have h_fill_bit : Nat.testBit fillWord.toNat bit = state := by
        dsimp only [fillWord]
        cases state
        · exact Nat.zero_testBit bit
        · simp only [↓reduceIte]
          have h_wm : (UInt64.ofNat mask64).toNat = mask64 := by decide
          rw [h_wm, testBit_mask64 bit h_bit]
      by_cases h_in_mid : bA + 1 ≤ k ∧ k < bB
      · refine ⟨fillWord, words[k]'h_ib, ?_, h_old, ?_⟩
        · have he := h_upd_elem k
          rw [ite_eq_left h_in_mid] at he
          exact he
        · rw [ite_eq_left (block_bit_range_mid bA rA bB rB k bit h_rA h_bit h_in_mid.1 h_in_mid.2), h_fill_bit]
      · have he_upd := h_upd_elem k
        rw [ite_eq_right h_in_mid, h_mid_elem k] at he_upd
        by_cases h_k_bB : rB ≠ 0 ∧ k = bB
        · obtain ⟨h_rB_nz, h_eq_bB⟩ := h_k_bB
          subst h_eq_bB
          have h_init_bB : initial[k]? = words[k]? := by
            have hi := h_init_elem k
            rw [ite_eq_right (Nat.ne_of_gt h_lt_div)] at hi
            exact hi
          rw [ite_eq_left ⟨h_rB_nz, rfl⟩, h_init_bB, h_old] at he_upd
          refine ⟨setW (words[k]'h_ib).toNat 0 rB state, words[k]'h_ib, he_upd, h_old, ?_⟩
          rw [setW_testBit _ 0 rB bit state (Nat.zero_le _) (Nat.le_of_lt h_rB) h_bit]
          have h_iff := block_bit_range_hi bA rA k rB bit h_rA h_lt_div
          by_cases h1 : 0 ≤ bit ∧ bit < rB
          · rw [ite_eq_left h1, ite_eq_left (h_iff.mp h1)]
          · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (h_iff.mpr h2))]
        · rw [ite_eq_right h_k_bB, h_init_elem k] at he_upd
          by_cases h_k_bA : k = bA
          · subst h_k_bA
            rw [ite_eq_left rfl, h_old] at he_upd
            refine ⟨setW (words[k]'h_ib).toNat rA 64 state, words[k]'h_ib, he_upd, h_old, ?_⟩
            rw [setW_testBit _ rA 64 bit state (Nat.le_of_lt h_rA) (Nat.le_refl 64) h_bit]
            have h_iff := block_bit_range_lo k rA bB rB bit h_lt_div h_bit
            by_cases h1 : rA ≤ bit ∧ bit < 64
            · rw [ite_eq_left h1, ite_eq_left (h_iff.mp h1)]
            · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (h_iff.mpr h2))]
          · rw [ite_eq_right h_k_bA] at he_upd
            refine ⟨words[k]'h_ib, words[k]'h_ib, he_upd.trans h_old, h_old, ?_⟩
            rw [ite_eq_right (block_bit_range_out_diff bA rA bB rB k bit h_rA h_rB h_bit h_in_mid h_k_bB h_k_bA)]

/-- Querying any in-bounds byte index on a `WellFormed` initialization mask
always succeeds, for both `.Lazy` and `.Materialized` storage. -/
theorem get_ok_of_wellFormed (mask : InitMask) (idx : Size)
    (valid : WellFormed mask) (inBounds : idx.bytes.toNat < mask.len.bytes.toNat) :
    ∃ b, mask.get idx = .ok b := by
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state => exact ⟨state, rfl⟩
    | Materialized mat =>
      cases mat with
      | mk words =>
        dsimp only [WellFormed] at valid
        dsimp only at inBounds
        have h_ib : idx.bytes.toNat / 64 < words.size :=
          div64_lt_of_lt_mul idx.bytes.toNat words.size (Nat.lt_of_lt_of_le inBounds valid)
        refine ⟨Nat.testBit (words[idx.bytes.toNat / 64]'h_ib).toNat (idx.bytes.toNat % 64), ?_⟩
        rw [get_materialized_eq, Array.getElem?_eq_getElem h_ib]

private theorem set_range_get_materialized (words : Array UInt64) (len : Size) (updated : InitMask)
    (range : AllocRange) (finish idx : Size) (state : Bool)
    (valid : len.bytes.toNat ≤ words.size * 64)
    (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ len.bytes.toNat)
    (idxInBounds : idx.bytes.toNat < len.bytes.toNat)
    (h_set : (InitMask.mk (.Materialized ⟨words⟩) len).setRange range state = .ok updated) :
    updated.get idx =
      if range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat then
        .ok state
      else
        (InitMask.mk (.Materialized ⟨words⟩) len).get idx := by
  by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
  · unfold InitMask.setRange at h_set
    simp only [endpoint, Bind.bind, Except.bind, full, and_self, ↓reduceIte,
      Pure.pure, Except.pure, Except.ok.injEq] at h_set
    subst h_set
    have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat := by
      have h_le := UInt64.le_iff_toNat_le.mp full.2
      have h0 : range.start.bytes.toNat = 0 := congrArg UInt64.toNat full.1
      exact ⟨h0 ▸ Nat.zero_le _, Nat.lt_of_lt_of_le idxInBounds h_le⟩
    rw [ite_eq_left h_in]
    rfl
  · have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
    rw [setRange_materialized_eq words len range finish state endpoint full h_fin_le] at h_set
    change (setRangeWords words (range.start.bytes.toNat / 64) (range.start.bytes.toNat % 64)
      (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state >>= fun newWords =>
        pure (InitMask.mk (.Materialized ⟨newWords⟩) len)) = .ok updated at h_set
    cases h_words : setRangeWords words
        (range.start.bytes.toNat / 64) (range.start.bytes.toNat % 64)
        (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state with
    | error _ => simp only [h_words, Bind.bind, Except.bind] at h_set; cases h_set
    | ok newWords =>
      simp only [h_words, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h_set
      subst h_set
      have h_ne_mul : (range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 <
          (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64 := by
        rw [div64_mul_add_eq, div64_mul_add_eq]; exact nonempty
      obtain ⟨_, h_bit⟩ := setRangeWords_bit_gen words _ _ _ _ state newWords
        (mod64_lt _) (mod64_lt _) h_ne_mul h_words
      have h_ib : idx.bytes.toNat / 64 < words.size :=
        div64_lt_of_lt_mul idx.bytes.toNat words.size (Nat.lt_of_lt_of_le idxInBounds valid)
      obtain ⟨w, oldW, hw, holdW, h_tb⟩ := h_bit (idx.bytes.toNat / 64) (idx.bytes.toNat % 64)
        h_ib (mod64_lt _)
      rw [div64_mul_add_eq, div64_mul_add_eq, div64_mul_add_eq] at h_tb
      rw [get_materialized_eq, get_materialized_eq, hw, holdW]
      dsimp only
      rw [h_tb]
      by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
      · rw [ite_eq_left h_in, ite_eq_left h_in]
      · rw [ite_eq_right h_in, ite_eq_right h_in]

/-- Pointwise byte-level specification of `InitMask.setRange` for an in-bounds
nonempty write on a `WellFormed` mask: indices inside `[range.start, finish)`
read as `.ok state`, and all other in-bounds indices preserve their prior
`mask.get` result. -/
theorem set_range_get (mask updated : InitMask) (range : AllocRange) (finish idx : Size)
    (state : Bool)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (idxInBounds : idx.bytes.toNat < mask.len.bytes.toNat)
    (h_set : mask.setRange range state = .ok updated) :
    updated.get idx =
      if range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat then
        .ok state
      else
        mask.get idx := by
  cases mask with
  | mk blocks len =>
    dsimp only at inBounds idxInBounds
    cases blocks with
    | Materialized mat =>
      cases mat with
      | mk oldBlocks =>
        exact set_range_get_materialized oldBlocks len updated range finish idx state
          valid endpoint nonempty inBounds idxInBounds h_set
    | Lazy initial =>
      by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
      · unfold InitMask.setRange at h_set
        simp only [endpoint, Bind.bind, Except.bind, full, and_self, ↓reduceIte,
          Pure.pure, Except.pure, Except.ok.injEq] at h_set
        subst h_set
        have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat := by
          have h_le := UInt64.le_iff_toNat_le.mp full.2
          have h0 : range.start.bytes.toNat = 0 := congrArg UInt64.toNat full.1
          exact ⟨h0 ▸ Nat.zero_le _, Nat.lt_of_lt_of_le idxInBounds h_le⟩
        rw [ite_eq_left h_in]
        rfl
      · by_cases same : initial == state
        · have h_eq_st : initial = state := eq_of_beq same
          subst h_eq_st
          have notGrow : ¬finish.bytes > len.bytes := by
            simpa only [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
          unfold InitMask.setRange at h_set
          simp only [endpoint, Bind.bind, Except.bind, full, ↓reduceIte,
            beq_self_eq_true, notGrow, Pure.pure, Except.pure, Except.ok.injEq] at h_set
          subst h_set
          by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
          · rw [ite_eq_left h_in]; rfl
          · rw [ite_eq_right h_in]
        · have h_diff : (initial == state) = false := Bool.eq_false_iff.mpr same
          have h_len_nz : len.bytes.toNat ≠ 0 :=
            Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) idxInBounds)
          have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
          rw [setRange_lazy_materialize_eq len initial state range finish endpoint full h_diff h_len_nz h_fin_le] at h_set
          let initWords := Array.replicate (len.bytes.toNat / 64 + 1)
            (if initial then UInt64.ofNat mask64 else 0)
          have h_cap : len.bytes.toNat ≤ initWords.size * 64 := by
            simp only [initWords, Array.size_replicate]; omega
          have h_mat := set_range_get_materialized initWords len updated range finish idx state
            h_cap endpoint nonempty inBounds idxInBounds h_set
          have h_get_mat : (InitMask.mk (.Materialized ⟨initWords⟩) len).get idx = .ok initial := by
            have h_ib_len : idx.bytes.toNat / 64 < len.bytes.toNat / 64 + 1 := by omega
            rw [get_materialized_eq]
            simp only [initWords, Array.getElem?_replicate, h_ib_len, ↓reduceIte]
            cases initial
            · exact congrArg Except.ok (Nat.zero_testBit _)
            · simp only [↓reduceIte]
              have h_wm : (UInt64.ofNat mask64).toNat = mask64 := by decide
              rw [h_wm, testBit_mask64 _ (mod64_lt _)]
          rw [h_get_mat] at h_mat
          exact h_mat

private theorem firstSetBit_spec_none (bits startBit : Nat) :
    ((List.range (64 - startBit)).find? fun offset =>
        Nat.testBit bits (startBit + offset)).map (· + startBit) = none ↔
      ∀ b, startBit ≤ b → b < 64 → Nat.testBit bits b = false := by
  simp only [Option.map_eq_none_iff, List.find?_eq_none, List.mem_range, Bool.not_eq_true]
  constructor
  · intro h b h_lo h_hi
    have h_off : b - startBit < 64 - startBit := by omega
    have h_eq : startBit + (b - startBit) = b := by omega
    simpa only [h_eq] using h (b - startBit) h_off
  · intro h off h_off
    exact h (startBit + off) (Nat.le_add_right _ _) (by omega)

private theorem firstSetBit_spec_some (bits startBit res : Nat)
    (h_some : ((List.range (64 - startBit)).find? fun offset =>
        Nat.testBit bits (startBit + offset)).map (· + startBit) = some res) :
    startBit ≤ res ∧ res < 64 ∧ Nat.testBit bits res = true ∧
      ∀ b, startBit ≤ b → b < res → Nat.testBit bits b = false := by
  rw [Option.map_eq_some_iff] at h_some
  obtain ⟨off, h_find, rfl⟩ := h_some
  have h_mem : off ∈ List.range (64 - startBit) := List.mem_of_find?_eq_some h_find
  rw [List.mem_range] at h_mem
  obtain ⟨h_true, xs, ys, h_eq_list, h_all_false⟩ := List.find?_eq_some_iff_append.mp h_find
  refine ⟨Nat.le_add_left _ _, by omega, by simpa only [Nat.add_comm] using h_true, fun b h_lo h_lt => ?_⟩
  have h_pw : List.Pairwise (· < ·) (List.range (64 - startBit)) := List.pairwise_lt_range
  rw [h_eq_list, List.pairwise_append, List.pairwise_cons] at h_pw
  obtain ⟨_, ⟨h_lt_ys, _⟩, _⟩ := h_pw
  have h_b_mem : b - startBit ∈ List.range (64 - startBit) := by
    rw [List.mem_range]; omega
  rw [h_eq_list, List.mem_append, List.mem_cons] at h_b_mem
  rcases h_b_mem with h_in_xs | h_eq_off | h_in_ys
  · have hf := h_all_false (b - startBit) h_in_xs
    have h_sum : startBit + (b - startBit) = b := by omega
    rw [h_sum] at hf
    exact Bool.eq_false_iff.mpr fun ht => by rw [ht] at hf; cases hf
  · omega
  · have := h_lt_ys (b - startBit) h_in_ys
    omega

private theorem searchBlk_spec (word : UInt64) (block startBit : Nat) (isInit : Bool)
    (h_block_fits : block * 64 + 63 ≤ mask64) :
    ∃ res?, searchBlk word block startBit isInit = .ok res? ∧
      match res? with
      | none => ∀ b, startBit ≤ b → b < 64 → Nat.testBit word.toNat b = !isInit
      | some idx =>
        ∃ bit, startBit ≤ bit ∧ bit < 64 ∧ idx.bytes.toNat = block * 64 + bit ∧
          Nat.testBit word.toNat bit = isInit ∧
          ∀ b, startBit ≤ b → b < bit → Nat.testBit word.toNat b = !isInit := by
  let bits := if isInit then word.toNat else mask64 - word.toNat
  have h_bits_tb : ∀ b, b < 64 → (Nat.testBit bits b = true ↔ Nat.testBit word.toNat b = isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [testBit_mask64_sub word.toNat b word.toNat_lt hb]
      cases word.toNat.testBit b <;> decide
    · simp only [↓reduceIte]
  have h_bits_false : ∀ b, b < 64 → (Nat.testBit bits b = false ↔ Nat.testBit word.toNat b = !isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [testBit_mask64_sub word.toNat b word.toNat_lt hb]
      cases word.toNat.testBit b <;> decide
    · simp only [↓reduceIte, Bool.not_true]
  cases h_fsb : ((List.range (64 - startBit)).find? fun offset =>
      Nat.testBit bits (startBit + offset)).map (· + startBit) with
  | none =>
    refine ⟨none, ?_, fun b h_lo h_hi => (h_bits_false b h_hi).mp ((firstSetBit_spec_none bits startBit).mp h_fsb b h_lo h_hi)⟩
    unfold searchBlk
    dsimp only [bits] at h_fsb ⊢
    rw [h_fsb]; rfl
  | some bit =>
    obtain ⟨h_lo, h_hi, h_tb, h_prev⟩ := firstSetBit_spec_some bits startBit bit h_fsb
    have h_fits : block * 64 + bit ≤ mask64 := by omega
    have h_lt264 : block * 64 + bit < 2 ^ 64 := by unfold mask64 at h_fits; omega
    let idx := Size.ofBytes (UInt64.ofNat (block * 64 + bit))
    have h_sfn : sizeFromN (block * 64 + bit) = .ok idx := by
      unfold sizeFromN; rw [ite_eq_left h_fits]
    refine ⟨some idx, ?_, bit, h_lo, h_hi, ?_, (h_bits_tb bit h_hi).mp h_tb, ?_⟩
    · unfold searchBlk
      dsimp only [bits] at h_fsb ⊢
      rw [h_fsb]
      dsimp only
      rw [h_sfn]
      rfl
    · simp only [idx, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_lt264]
    · intro b hb_lo hb_lt
      exact (h_bits_false b (Nat.lt_trans hb_lt h_hi)).mp (h_prev b hb_lo hb_lt)

private theorem search_blocks_list_spec (words : Array UInt64) (finish : Size) (isInit : Bool)
    (blocksList : List Nat)
    (h_sorted : List.Pairwise (· < ·) blocksList)
    (h_blocks_in : ∀ blk ∈ blocksList, blk < words.size)
    (h_blocks_fits : ∀ blk ∈ blocksList, blk * 64 + 63 ≤ mask64) :
    ∃ out,
      forIn blocksList (none, ⟨⟩) (fun (block : Nat) (_ : Option (Option Size) × PUnit) =>
        (do
          match ← searchBlk (← getB words block) block 0 isInit with
          | some index =>
            if index.bytes.toNat < finish.bytes.toNat then
              pure (ForInStep.done (some (some index), ⟨⟩))
            else
              pure (ForInStep.done (some none, ⟨⟩))
          | none => pure (ForInStep.yield (none, ⟨⟩)) :
          Except InitMaskError (ForInStep (Option (Option Size) × PUnit)))) = .ok (out, ⟨⟩) ∧
      match out with
      | none | some none =>
        ∀ blk (h_mem : blk ∈ blocksList) (b : Nat), b < 64 → blk * 64 + b < finish.bytes.toNat →
          Nat.testBit (words[blk]'(h_blocks_in blk h_mem)).toNat b = !isInit
      | some (some idx) =>
        ∃ blk, ∃ (h_mem : blk ∈ blocksList), ∃ bit, bit < 64 ∧
          idx.bytes.toNat = blk * 64 + bit ∧
          idx.bytes.toNat < finish.bytes.toNat ∧
          Nat.testBit (words[blk]'(h_blocks_in blk h_mem)).toNat bit = isInit ∧
          ∀ blk' (h_mem' : blk' ∈ blocksList) (b : Nat), b < 64 →
            blk' * 64 + b < idx.bytes.toNat →
            Nat.testBit (words[blk']'(h_blocks_in blk' h_mem')).toNat b = !isInit := by
  induction blocksList with
  | nil =>
    refine ⟨none, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons blk rest ih =>
    rw [List.pairwise_cons] at h_sorted
    obtain ⟨h_lt_rest, h_pw_rest⟩ := h_sorted
    have h_ib : blk < words.size := h_blocks_in blk (List.mem_cons_self ..)
    have h_fits : blk * 64 + 63 ≤ mask64 := h_blocks_fits blk (List.mem_cons_self ..)
    have h_gb : getB words blk = .ok (words[blk]'h_ib) := by
      unfold getB; rw [Array.getElem?_eq_getElem h_ib]
    obtain ⟨res?, h_sb, h_sb_prop⟩ := searchBlk_spec (words[blk]'h_ib) blk 0 isInit h_fits
    cases res? with
    | none =>
      obtain ⟨tailOut, h_tail, h_tail_prop⟩ := ih h_pw_rest
        (fun x hx => h_blocks_in x (List.mem_cons_of_mem _ hx))
        (fun x hx => h_blocks_fits x (List.mem_cons_of_mem _ hx))
      refine ⟨tailOut, ?_, ?_⟩
      · simp only [List.forIn_cons, h_gb, h_sb, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact h_tail
      · cases tailOut with
        | none =>
          intro x hx b hb h_lt_fin
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact h_sb_prop b (Nat.zero_le _) hb
          · exact h_tail_prop x hx_rest b hb h_lt_fin
        | some inner =>
          cases inner with
          | none =>
            intro x hx b hb h_lt_fin
            rcases List.mem_cons.mp hx with rfl | hx_rest
            · exact h_sb_prop b (Nat.zero_le _) hb
            · exact h_tail_prop x hx_rest b hb h_lt_fin
          | some idx =>
            obtain ⟨x, hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, h_prev_rest⟩ := h_tail_prop
            refine ⟨x, List.mem_cons_of_mem _ hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, ?_⟩
            intro x' hx' b hb h_lt_idx
            rcases List.mem_cons.mp hx' with rfl | hx'_rest
            · exact h_sb_prop b (Nat.zero_le _) hb
            · exact h_prev_rest x' hx'_rest b hb h_lt_idx
    | some idx =>
      obtain ⟨bit, _, hbit, h_idx_eq, h_tb, h_prev⟩ := h_sb_prop
      by_cases h_lt_fin : idx.bytes.toNat < finish.bytes.toNat
      · refine ⟨some (some idx), ?_, blk, List.mem_cons_self .., bit, hbit, h_idx_eq, h_lt_fin, h_tb, ?_⟩
        · simp only [List.forIn_cons, h_gb, h_sb, h_lt_fin, ↓reduceIte,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        · intro x' hx' b hb h_lt_idx
          rcases List.mem_cons.mp hx' with rfl | hx'_rest
          · exact h_prev b (Nat.zero_le _) (Nat.lt_of_add_lt_add_left (h_idx_eq ▸ h_lt_idx))
          · have hlt := h_lt_rest x' hx'_rest
            exact absurd h_lt_idx (by omega)
      · refine ⟨some none, ?_, ?_⟩
        · simp only [List.forIn_cons, h_gb, h_sb, h_lt_fin, ↓reduceIte,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        · have h_ge_fin : finish.bytes.toNat ≤ blk * 64 + bit :=
            h_idx_eq ▸ Nat.le_of_not_lt h_lt_fin
          intro x hx b hb h_lt
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact h_prev b (Nat.zero_le _) (Nat.lt_of_add_lt_add_left (Nat.lt_of_lt_of_le h_lt h_ge_fin))
          · have hlt := h_lt_rest x hx_rest
            exact absurd (Nat.lt_of_lt_of_le h_lt h_ge_fin) (by omega)

private theorem div64_of_blk_bit (n blk bit : Nat) (hbit : bit < 64) (heq : n = blk * 64 + bit) :
    n / 64 = blk ∧ n % 64 = bit := by omega

private theorem idx_in_start_block (s i b bit : Nat) (h_bit : bit < 64) (h_lo : s ≤ i)
    (h_lt : i < b * 64 + bit) (h_sb : s / 64 = b) :
    i / 64 = b ∧ s % 64 ≤ i % 64 ∧ i % 64 < bit := by omega

private theorem idx_in_only_block (s f i : Nat) (h_lo : s ≤ i) (h_lt : i < f)
    (h_not_more : ¬(s / 64 < (f - 1) / 64)) : i / 64 = s / 64 ∧ s % 64 ≤ i % 64 := by omega

private theorem idx_in_rng_of_ne_start (s f i : Nat) (h_lo : s ≤ i) (h_lt : i < f)
    (h_ne : i / 64 ≠ s / 64) : s / 64 + 1 ≤ i / 64 ∧ i / 64 ≤ (f - 1) / 64 := by omega

private theorem findBitPub_spec (words : Array UInt64) (len start finish : Size) (isInit : Bool)
    (h_cap : finish.bytes.toNat ≤ words.size * 64) :
    ∃ res?, findBitPub words start finish isInit = .ok res? ∧
      match res? with
      | none =>
        ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
          (InitMask.mk (.Materialized ⟨words⟩) len).get idx = .ok (!isInit)
      | some found =>
        start.bytes.toNat ≤ found.bytes.toNat ∧ found.bytes.toNat < finish.bytes.toNat ∧
          (InitMask.mk (.Materialized ⟨words⟩) len).get found = .ok isInit ∧
          ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < found.bytes.toNat →
            (InitMask.mk (.Materialized ⟨words⟩) len).get idx = .ok (!isInit) := by
  unfold findBitPub
  have h_fin_u64 := finish.bytes.toNat_lt
  by_cases h_empty : start.bytes.toNat ≥ finish.bytes.toNat
  · refine ⟨none, by rw [ite_eq_left h_empty]; rfl, fun idx h1 h2 => absurd (Nat.le_trans h1 (Nat.le_of_lt h2)) (by omega)⟩
  · rw [ite_eq_right h_empty]
    have h_lt_sf : start.bytes.toNat < finish.bytes.toNat := Nat.lt_of_not_ge h_empty
    let startBlock := start.bytes.toNat / 64
    let startBit := start.bytes.toNat % 64
    let endIncNat := finish.bytes.toNat - 1
    have h_end_lt264 : endIncNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) h_fin_u64
    have h_end_fits : endIncNat ≤ mask64 := Nat.le_of_lt_succ h_end_lt264
    have h_sfn : sizeFromN endIncNat = .ok (Size.ofBytes (UInt64.ofNat endIncNat)) := by
      unfold sizeFromN; rw [ite_eq_left h_end_fits]
    have h_endInc_bytes : (Size.ofBytes (UInt64.ofNat endIncNat)).bytes.toNat = endIncNat := by
      simp only [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_end_lt264]
    let endBlock := endIncNat / 64
    have h_sb_ib : startBlock < words.size :=
      div64_lt_of_lt_mul start.bytes.toNat words.size (Nat.lt_of_lt_of_le h_lt_sf h_cap)
    have h_eb_ib : endBlock < words.size :=
      div64_lt_of_lt_mul endIncNat words.size (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) h_lt_sf) Nat.zero_lt_one) h_cap)
    have h_sb_fits : startBlock * 64 + 63 ≤ mask64 := by
      have : start.bytes.toNat < 2 ^ 64 := start.bytes.toNat_lt
      dsimp only [startBlock]; unfold mask64; omega
    have h_gb0 : getB words startBlock = .ok (words[startBlock]'h_sb_ib) := by
      unfold getB; rw [Array.getElem?_eq_getElem h_sb_ib]
    obtain ⟨first?, h_sb0, h_sb0_prop⟩ := searchBlk_spec (words[startBlock]'h_sb_ib) startBlock startBit isInit h_sb_fits
    have h_get_eq : ∀ (idx : Size) (h_ib : idx.bytes.toNat / 64 < words.size),
        (InitMask.mk (.Materialized ⟨words⟩) len).get idx =
          .ok (Nat.testBit (words[idx.bytes.toNat / 64]'h_ib).toNat (idx.bytes.toNat % 64)) := by
      intro idx h_ib
      rw [get_materialized_eq, Array.getElem?_eq_getElem h_ib]
    dsimp only [endIncNat] at h_sfn h_endInc_bytes
    dsimp only [startBlock, startBit, endBlock, endIncNat] at h_gb0 h_sb0 ⊢
    simp only [h_sfn, Bind.bind, Except.bind, h_endInc_bytes, h_gb0, h_sb0]
    cases first? with
    | some firstIdx =>
      obtain ⟨bit, h_lo, h_hi, h_f_eq, h_tb, h_prev⟩ := h_sb0_prop
      by_cases h_lt_f : firstIdx.bytes.toNat < finish.bytes.toNat
      · refine ⟨some firstIdx, by simp only [h_lt_f, ↓reduceIte, Pure.pure, Except.pure], ?_⟩
        obtain ⟨h_div, h_mod⟩ := div64_of_blk_bit firstIdx.bytes.toNat startBlock bit h_hi h_f_eq
        refine ⟨by dsimp only [startBlock, startBit] at h_lo h_f_eq; omega, h_lt_f, ?_, ?_⟩
        · rw [h_get_eq firstIdx (h_div ▸ h_sb_ib)]
          simpa only [h_div, h_mod] using congrArg Except.ok h_tb
        · intro idx h_idx_lo h_idx_lt
          obtain ⟨h_idiv, h_imod_lo, h_imod_lt⟩ :=
            idx_in_start_block start.bytes.toNat idx.bytes.toNat startBlock bit h_hi h_idx_lo (h_f_eq ▸ h_idx_lt) rfl
          rw [h_get_eq idx (h_idiv ▸ h_sb_ib)]
          simpa only [h_idiv] using congrArg Except.ok (h_prev (idx.bytes.toNat % 64) h_imod_lo h_imod_lt)
      · refine ⟨none, by simp only [h_lt_f, ↓reduceIte, Pure.pure, Except.pure], ?_⟩
        intro idx h_idx_lo h_idx_lt
        have h_lt_first : idx.bytes.toNat < startBlock * 64 + bit :=
          h_f_eq ▸ Nat.lt_of_lt_of_le h_idx_lt (Nat.le_of_not_lt h_lt_f)
        obtain ⟨h_idiv, h_imod_lo, h_imod_lt⟩ :=
          idx_in_start_block start.bytes.toNat idx.bytes.toNat startBlock bit h_hi h_idx_lo h_lt_first rfl
        rw [h_get_eq idx (h_idiv ▸ h_sb_ib)]
        simpa only [h_idiv] using congrArg Except.ok (h_prev (idx.bytes.toNat % 64) h_imod_lo h_imod_lt)
    | none =>
      by_cases h_more : startBlock < endBlock
      · dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [ite_eq_left h_more]
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        let rngList := List.range' [startBlock + 1:endBlock + 1].start
          [startBlock + 1:endBlock + 1].size [startBlock + 1:endBlock + 1].step
        have h_mem_rng : ∀ x, x ∈ rngList ↔ (startBlock + 1 ≤ x ∧ x ≤ endBlock) := by
          intro x
          simp only [rngList, List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul]
          constructor
          · rintro ⟨i, hi, rfl⟩; omega
          · intro ⟨h1, h2⟩; exact ⟨x - (startBlock + 1), by omega, by omega⟩
        have h_pw_rng : List.Pairwise (· < ·) rngList := List.pairwise_lt_range'
        have h_in_rng : ∀ x ∈ rngList, x < words.size := fun x hx =>
          Nat.lt_of_le_of_lt ((h_mem_rng x).mp hx).2 h_eb_ib
        have h_fits_rng : ∀ x ∈ rngList, x * 64 + 63 ≤ mask64 := by
          intro x hx; have := ((h_mem_rng x).mp hx).2
          dsimp only [endBlock, endIncNat] at this; unfold mask64; omega
        obtain ⟨loopOut, h_loop, h_loop_prop⟩ := search_blocks_list_spec words finish isInit
          rngList h_pw_rng h_in_rng h_fits_rng
        dsimp only [rngList, startBlock, endBlock, endIncNat] at h_loop
        simp only [Bind.bind, Except.bind] at h_loop ⊢
        rw [h_loop]
        simp only [Pure.pure, Except.pure]
        have h_none_branch :
            (∀ blk (h_mem : blk ∈ rngList) (b : Nat), b < 64 → blk * 64 + b < finish.bytes.toNat →
              Nat.testBit (words[blk]'(h_in_rng blk h_mem)).toNat b = !isInit) →
            ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
              (InitMask.mk (.Materialized ⟨words⟩) len).get idx = .ok (!isInit) := by
          intro h_all idx h_idx_lo h_idx_lt
          by_cases hk : idx.bytes.toNat / 64 = startBlock
          · rw [h_get_eq idx (hk ▸ h_sb_ib)]
            have h_lo_mod : startBit ≤ idx.bytes.toNat % 64 := by
              dsimp only [startBlock, startBit] at hk ⊢; omega
            simpa only [hk] using congrArg Except.ok (h_sb0_prop (idx.bytes.toNat % 64) h_lo_mod (mod64_lt _))
          · have h_in_l : idx.bytes.toNat / 64 ∈ rngList :=
              (h_mem_rng _).mpr (idx_in_rng_of_ne_start start.bytes.toNat finish.bytes.toNat idx.bytes.toNat h_idx_lo h_idx_lt hk)
            rw [h_get_eq idx (h_in_rng _ h_in_l)]
            exact congrArg Except.ok (h_all (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
              (mod64_lt _) (by rw [div64_mul_add_eq]; exact h_idx_lt))
        cases loopOut with
        | none => exact ⟨none, rfl, h_none_branch h_loop_prop⟩
        | some inner =>
          cases inner with
          | none => exact ⟨none, rfl, h_none_branch h_loop_prop⟩
          | some found =>
            obtain ⟨blk, h_blk_mem, bit, hbit, h_f_eq, h_f_lt, h_f_tb, h_f_prev⟩ := h_loop_prop
            have h_blk_bounds := (h_mem_rng blk).mp h_blk_mem
            obtain ⟨h_f_div, h_f_mod⟩ := div64_of_blk_bit found.bytes.toNat blk bit hbit h_f_eq
            refine ⟨some found, rfl, ?_, h_f_lt, ?_, ?_⟩
            · dsimp only [startBlock] at h_blk_bounds; omega
            · rw [h_get_eq found (h_f_div ▸ h_in_rng blk h_blk_mem)]
              simpa only [h_f_div, h_f_mod] using congrArg Except.ok h_f_tb
            · intro idx h_idx_lo h_idx_lt
              by_cases hk : idx.bytes.toNat / 64 = startBlock
              · rw [h_get_eq idx (hk ▸ h_sb_ib)]
                have h_lo_mod : startBit ≤ idx.bytes.toNat % 64 := by
                  dsimp only [startBlock, startBit] at hk ⊢; omega
                simpa only [hk] using congrArg Except.ok (h_sb0_prop (idx.bytes.toNat % 64) h_lo_mod (mod64_lt _))
              · have h_in_l : idx.bytes.toNat / 64 ∈ rngList :=
                  (h_mem_rng _).mpr (idx_in_rng_of_ne_start start.bytes.toNat finish.bytes.toNat idx.bytes.toNat
                    h_idx_lo (Nat.lt_trans h_idx_lt h_f_lt) hk)
                rw [h_get_eq idx (h_in_rng _ h_in_l)]
                exact congrArg Except.ok (h_f_prev (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
                  (mod64_lt _) (by rw [div64_mul_add_eq]; exact h_idx_lt))
      · dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [ite_eq_right h_more]
        refine ⟨none, rfl, fun idx h_idx_lo h_idx_lt => ?_⟩
        obtain ⟨h_idiv, h_imod_lo⟩ := idx_in_only_block start.bytes.toNat finish.bytes.toNat idx.bytes.toNat h_idx_lo h_idx_lt h_more
        rw [h_get_eq idx (h_idiv ▸ h_sb_ib)]
        simpa only [h_idiv] using congrArg Except.ok (h_sb0_prop (idx.bytes.toNat % 64) h_imod_lo (mod64_lt _))

private theorem fromEndpoints_ok_of_le (a b : Size) (h : a.bytes.toNat ≤ b.bytes.toNat) :
    ∃ r, AllocRange.fromEndpoints a b = .ok r ∧ r.start = a ∧
      r.size.bytes.toNat = b.bytes.toNat - a.bytes.toNat := by
  have h_le : a.bytes ≤ b.bytes := UInt64.le_iff_toNat_le.mpr h
  have h_not_lt : ¬(b.bytes < a.bytes) := UInt64.not_lt.mpr h_le
  refine ⟨⟨a, Size.ofBytes (b.bytes - a.bytes)⟩, ?_, rfl, ?_⟩
  · unfold AllocRange.fromEndpoints Size.sub
    simp only [h_not_lt, ↓reduceIte, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp only [Size.ofBytes, UInt64.toNat_sub_of_le _ _ h_le]

/-- Equivalence between `InitMask.isRangeInitialized` and pointwise `InitMask.get`
on any nonempty in-bounds range of a `WellFormed` mask, together with the
existence of an uninitialized subrange witness whenever any byte in the range is
uninitialized. -/
theorem isRangeInitialized_nonempty_iff (mask : InitMask) (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    (mask.isRangeInitialized range = .ok (.ok ()) ↔
      ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
        mask.get idx = .ok true) ∧
    ((∃ idx : Size, range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat ∧
        mask.get idx = .ok false) →
      ∃ bad : AllocRange, mask.isRangeInitialized range = .ok (.error bad)) := by
  have h_not_oob : ¬(finish.bytes > mask.len.bytes) := by
    simpa only [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  cases mask with
  | mk blocks len =>
    dsimp only at inBounds h_not_oob
    cases blocks with
    | Lazy state =>
      unfold InitMask.isRangeInitialized InitMask.get
      simp only [endpoint, Bind.bind, Except.bind, h_not_oob, ↓reduceIte, Pure.pure, Except.pure]
      cases state
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨⟨(fun h => by cases h), fun h_all => ?_⟩, fun _ => ⟨range, rfl⟩⟩
        have h0 := h_all range.start (Nat.le_refl _) nonempty
        cases h0
      · simp only [↓reduceIte]
        exact ⟨⟨fun _ _ _ _ => trivial, fun _ => trivial⟩, fun ⟨_, _, _, hf⟩ => by cases hf⟩
    | Materialized mat =>
      cases mat with
      | mk words =>
        dsimp only [WellFormed] at valid
        have h_cap : finish.bytes.toNat ≤ words.size * 64 := Nat.le_trans inBounds valid
        obtain ⟨uninit?, h_fb0, h_fb0_prop⟩ := findBitPub_spec words len range.start finish false h_cap
        cases uninit? with
        | none =>
          have h_ir : (InitMask.mk (.Materialized ⟨words⟩) len).isRangeInitialized range = .ok (.ok ()) := by
            rw [isRangeInitialized_materialized_eq words len range finish endpoint h_not_oob]
            have h_step : ∀ r, findBitPub words range.start finish false = .ok r → r = none →
                (do
                  match ← findBitPub words range.start finish false with
                  | none => return (Except.ok () : Except AllocRange Unit)
                  | some uninitStart =>
                    let uninitEnd := (← findBitPub words uninitStart finish true).getD finish
                    return Except.error (← AllocRange.fromEndpoints uninitStart uninitEnd)) = .ok (.ok ()) := by
              intro r hr hnone; subst hnone; rw [hr]; rfl
            exact h_step none h_fb0 rfl
          simp only [h_ir]
          dsimp only [Bool.not_false] at h_fb0_prop
          exact ⟨⟨fun _ => h_fb0_prop, fun _ => trivial⟩,
            fun ⟨idx, h1, h2, hf⟩ => by rw [h_fb0_prop idx h1 h2] at hf; cases hf⟩
        | some uninitStart =>
          obtain ⟨h_us_lo, h_us_lt, h_us_get, _⟩ := h_fb0_prop
          obtain ⟨end?, h_fb1, h_fb1_prop⟩ := findBitPub_spec words len uninitStart finish true h_cap
          have h_end_ge : uninitStart.bytes.toNat ≤ (end?.getD finish).bytes.toNat := by
            cases end? with
            | none => exact Nat.le_of_lt h_us_lt
            | some _ => exact h_fb1_prop.1
          obtain ⟨bad, h_bad, _, _⟩ := fromEndpoints_ok_of_le uninitStart (end?.getD finish) h_end_ge
          have h_ir : (InitMask.mk (.Materialized ⟨words⟩) len).isRangeInitialized range = .ok (.error bad) := by
            rw [isRangeInitialized_materialized_eq words len range finish endpoint h_not_oob]
            have h_step : (do
                match ← findBitPub words range.start finish false with
                | none => return (Except.ok () : Except AllocRange Unit)
                | some u =>
                  let uninitEnd := (← findBitPub words u finish true).getD finish
                  return Except.error (← AllocRange.fromEndpoints u uninitEnd)) = .ok (.error bad) := by
              rw [h_fb0]; dsimp only [Bind.bind, Except.bind]; rw [h_fb1]; dsimp only [Bind.bind, Except.bind]; rw [h_bad]; rfl
            exact h_step
          simp only [h_ir]
          refine ⟨⟨(fun h => by cases h), fun h_all => ?_⟩, fun _ => ⟨bad, rfl⟩⟩
          have ht := h_all uninitStart h_us_lo h_us_lt
          rw [h_us_get] at ht
          cases ht

/-- After setting an in-bounds nonempty range to `true` on a `WellFormed` mask,
`isRangeInitialized` succeeds on that same range. -/
theorem isRangeInitialized_after_setRange_true (mask updated : InitMask)
    (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (h_set : mask.setRange range true = .ok updated) :
    updated.isRangeInitialized range = .ok (.ok ()) := by
  obtain ⟨u, h_u, h_len, h_wf⟩ := set_range_exists mask range finish true valid endpoint nonempty inBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u range finish h_wf endpoint nonempty (by rw [h_len]; exact inBounds)).1]
  intro idx h_lo h_hi
  rw [set_range_get mask u range finish idx true valid endpoint nonempty inBounds (Nat.lt_of_lt_of_le h_hi inBounds) h_u,
    ite_eq_left ⟨h_lo, h_hi⟩]

/-- Disjoint-frame preservation for `isRangeInitialized`: setting `writeRange`
to `state` does not change whether any disjoint nonempty in-bounds `queryRange`
is initialized. -/
theorem isRangeInitialized_frame (mask updated : InitMask)
    (writeRange queryRange : AllocRange) (writeFinish queryFinish : Size) (state : Bool)
    (valid : WellFormed mask)
    (wEnd : writeRange.endExclusive = .ok writeFinish)
    (qEnd : queryRange.endExclusive = .ok queryFinish)
    (wNonempty : writeRange.start.bytes.toNat < writeFinish.bytes.toNat)
    (qNonempty : queryRange.start.bytes.toNat < queryFinish.bytes.toNat)
    (wInBounds : writeFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (qInBounds : queryFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (disjoint : writeFinish.bytes.toNat ≤ queryRange.start.bytes.toNat ∨
      queryFinish.bytes.toNat ≤ writeRange.start.bytes.toNat)
    (h_set : mask.setRange writeRange state = .ok updated) :
    (updated.isRangeInitialized queryRange = .ok (.ok ()) ↔
      mask.isRangeInitialized queryRange = .ok (.ok ())) := by
  obtain ⟨u, h_u, h_len, h_wf⟩ := set_range_exists mask writeRange writeFinish state valid wEnd wNonempty wInBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u queryRange queryFinish h_wf qEnd qNonempty (by rw [h_len]; exact qInBounds)).1,
    (isRangeInitialized_nonempty_iff mask queryRange queryFinish valid qEnd qNonempty qInBounds).1]
  have h_pt : ∀ idx : Size, queryRange.start.bytes.toNat ≤ idx.bytes.toNat →
      idx.bytes.toNat < queryFinish.bytes.toNat → u.get idx = mask.get idx := by
    intro idx h_lo h_hi
    have h_out : ¬(writeRange.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < writeFinish.bytes.toNat) := by
      rcases disjoint with h1 | h2
      · exact fun ⟨_, hlt⟩ => Nat.not_lt.mpr (Nat.le_trans h1 h_lo) hlt
      · exact fun ⟨hle, _⟩ => Nat.not_lt.mpr (Nat.le_trans h2 hle) h_hi
    have h_get := set_range_get mask u writeRange writeFinish idx state valid wEnd wNonempty wInBounds
      (Nat.lt_of_lt_of_le h_hi qInBounds) h_u
    rw [ite_eq_right h_out] at h_get
    exact h_get
  exact ⟨fun h idx h1 h2 => (h_pt idx h1 h2).symm.trans (h idx h1 h2),
    fun h idx h1 h2 => (h_pt idx h1 h2).trans (h idx h1 h2)⟩

private theorem endExclusive_size_eq (range : AllocRange) (finish : Size)
    (endpoint : range.endExclusive = .ok finish) :
    finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat ∧
      finish.bytes - range.start.bytes = range.size.bytes := by
  unfold AllocRange.endExclusive AllocRange.end Size.add at endpoint
  by_cases h_wrap : range.start.bytes + range.size.bytes < range.start.bytes
  · simp only [h_wrap, ↓reduceIte, Except.mapError] at endpoint; cases endpoint
  · simp only [h_wrap, ↓reduceIte, Except.mapError, Except.ok.injEq] at endpoint
    subst endpoint
    have h_nw : ¬((range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat) := by
      simpa only [UInt64.lt_iff_toNat_lt] using h_wrap
    have h1 := range.start.bytes.toNat_lt
    have h2 := range.size.bytes.toNat_lt
    have h_fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
      by_cases h_lt : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64
      · exact h_lt
      · have h_mod : (range.start.bytes + range.size.bytes).toNat =
            range.start.bytes.toNat + range.size.bytes.toNat - 2 ^ 64 := by
          rw [UInt64.toNat_add]; omega
        omega
    constructor
    · simp only [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
    · apply UInt64.toNat_inj.mp
      have h_le : range.start.bytes ≤ (Size.ofBytes (range.start.bytes + range.size.bytes)).bytes := by
        simp only [Size.ofBytes, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
        exact Nat.le_add_right _ _
      rw [UInt64.toNat_sub_of_le _ _ h_le]
      simp only [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits, Nat.add_sub_cancel_left]

/-- Preparing an `InitCopy` over a nonempty in-bounds range whose bytes are all
uniformly equal to `state` yields the single-run descriptor
`⟨state, #[range.size.bytes]⟩`. -/
theorem prepareCopy_of_uniform (mask : InitMask) (range : AllocRange) (finish : Size) (state : Bool)
    (valid : WellFormed mask)
    (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (uniform : ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat →
      idx.bytes.toNat < finish.bytes.toNat → mask.get idx = .ok state) :
    mask.prepareCopy range = .ok ⟨state, #[range.size.bytes]⟩ := by
  obtain ⟨h_fin_eq, h_sub_eq⟩ := endExclusive_size_eq range finish endpoint
  have h_sz_nz : range.size.bytes ≠ 0 := fun h0 => by
    have h0' : range.size.bytes.toNat = 0 := congrArg UInt64.toNat h0
    omega
  have h_sz_beq : (range.size.bytes == 0) = false := beq_false_of_ne h_sz_nz
  have h_not_oob : ¬(finish.bytes > mask.len.bytes) := by
    simpa only [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  have h_lt_u64 : range.start.bytes < finish.bytes := UInt64.lt_iff_toNat_lt.mpr nonempty
  have h_not_gt_sf : ¬(range.start.bytes > finish.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_of_lt h_lt_u64)
  have h_not_le_fs : ¬(finish.bytes ≤ range.start.bytes) := UInt64.not_le.mpr h_lt_u64
  have h_get_start : mask.get range.start = .ok state := uniform range.start (Nat.le_refl _) nonempty
  have h_raic : mask.rangeAsInitChunks range = .ok ⟨mask, state, range.start, finish⟩ := by
    unfold InitMask.rangeAsInitChunks
    simp only [endpoint, Bind.bind, Except.bind, h_not_oob, ↓reduceIte, h_lt_u64, h_get_start,
      Pure.pure, Except.pure]
  let chunk0 : InitChunk := if state then .Init range.start finish else .Uninit range.start finish
  have h_next0 : (⟨mask, state, range.start, finish⟩ : InitChunkIter).next? =
      .ok (some (chunk0, ⟨mask, !state, finish, finish⟩)) := by
    have h_not_ge : ¬(range.start.bytes.toNat ≥ finish.bytes.toNat) := Nat.not_le.mpr nonempty
    cases mask with
    | mk blocks len =>
      dsimp only at inBounds h_not_oob h_get_start ⊢
      cases blocks with
      | Lazy s =>
        have h_s_eq : s = state := Except.ok.inj h_get_start
        subst h_s_eq
        unfold InitChunkIter.next?
        simp only [h_not_gt_sf, h_not_oob, decide_false, Bool.or_self, Bool.false_eq_true,
          ↓reduceIte, bne_self_eq_false, h_not_le_fs, Bind.bind, Except.bind, Pure.pure, Except.pure]
        change (if range.start.bytes.toNat ≥ finish.bytes.toNat then (Except.ok none : Except InitMaskError (Option (InitChunk × InitChunkIter))) else _) = _
        rw [ite_eq_right h_not_ge]
      | Materialized mat =>
        cases mat with
        | mk words =>
          dsimp only [WellFormed] at valid
          obtain ⟨found?, h_fb, h_fb_prop⟩ :=
            findBitPub_spec words len range.start finish (!state) (Nat.le_trans inBounds valid)
          have h_found_none : found? = none := by
            cases found? with
            | none => rfl
            | some f =>
              obtain ⟨h_lo, h_hi, h_f_get, _⟩ := h_fb_prop
              have h_u := uniform f h_lo h_hi
              rw [h_f_get] at h_u
              cases state <;> cases h_u
          subst h_found_none
          rw [next?_materialized_eq words len state range.start finish h_not_gt_sf h_not_oob h_not_ge]
          have h_step : (do
              let chunkEnd ← do
                let found ← findBitPub words range.start finish (!state)
                pure (found.getD finish)
              if chunkEnd.bytes ≤ range.start.bytes then throw (MemoryError.invalidChunkIterator range.start finish)
              let chunk := if state then InitChunk.Init range.start chunkEnd else InitChunk.Uninit range.start chunkEnd
              return some (chunk, InitChunkIter.mk (InitMask.mk (.Materialized ⟨words⟩) len) (!state) chunkEnd finish)) =
              Except.ok (some (chunk0, InitChunkIter.mk (InitMask.mk (.Materialized ⟨words⟩) len) (!state) finish finish)) := by
            rw [h_fb]
            simp only [Option.getD_none, h_not_le_fs, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure]
            rfl
          exact h_step
  have h_next1 : (⟨mask, !state, finish, finish⟩ : InitChunkIter).next? = .ok none := by
    unfold InitChunkIter.next?
    have h_not_ff : ¬(finish.bytes > finish.bytes) := UInt64.lt_irrefl _
    simp only [h_not_ff, h_not_oob, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    change (if finish.bytes.toNat ≥ finish.bytes.toNat then (Except.ok none : Except InitMaskError (Option (InitChunk × InitChunkIter))) else _) = Except.ok none
    rw [ite_eq_left (Nat.le_refl _)]
  have h_collect : InitMask.collectChunks ⟨mask, state, range.start, finish⟩ = .ok #[chunk0] :=
    collectChunks_single _ _ chunk0 nonempty h_next0 h_next1
  have h_chunk_isInit : chunk0.isInit = state := by dsimp only [chunk0]; cases state <;> rfl
  have h_chunk_range : chunk0.range = .ok ⟨range.start, range.size⟩ := by
    have h_not_lt : ¬(finish.bytes < range.start.bytes) := UInt64.not_lt.mpr (UInt64.le_of_lt h_lt_u64)
    cases state
    · simp only [chunk0, Bool.false_eq_true, ↓reduceIte, InitChunk.range, AllocRange.fromEndpoints,
        Size.sub, h_not_lt, h_sub_eq, Size.ofBytes, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
    · simp only [chunk0, ↓reduceIte, InitChunk.range, AllocRange.fromEndpoints,
        Size.sub, h_not_lt, h_sub_eq, Size.ofBytes, Except.mapError, Bind.bind, Except.bind,
        Pure.pure, Except.pure]
  unfold InitMask.prepareCopy
  simp only [h_sz_beq, Bool.false_eq_true, ↓reduceIte, h_raic, Bind.bind, Except.bind, h_collect]
  have h_get0 : (#[chunk0] : Array InitChunk)[0]? = some chunk0 := rfl
  rw [h_get0]
  dsimp only
  rw [← Array.forIn_toList]
  have h_tl : (#[chunk0] : Array InitChunk).toList = [chunk0] := rfl
  rw [h_tl]
  simp only [List.forIn_cons, List.forIn_nil, h_chunk_range, h_chunk_isInit,
    Bind.bind, Except.bind, Pure.pure, Except.pure, Array.push_empty]

/-- Applying a single-run `InitCopy` descriptor reduces directly to a single
`InitMask.setRange` over the multiplied destination span. -/
theorem applyCopy_singleton (destMask : InitMask) (destStart srcSize total : Size)
    (repeatCount : UInt64) (state : Bool)
    (nonzero : srcSize.bytes ≠ 0)
    (h_mul : Size.mul srcSize repeatCount = .ok total) :
    destMask.applyCopy ⟨state, #[srcSize.bytes]⟩ (allocRange destStart srcSize) repeatCount =
      destMask.setRange (allocRange destStart total) state := by
  have h_nz_beq : (srcSize.bytes == 0) = false := beq_false_of_ne nonzero
  have h_chk : ((#[srcSize.bytes] : Array UInt64).isEmpty || (#[srcSize.bytes] : Array UInt64).any (· == 0)) = false := by
    simp [h_nz_beq]
  have h_sz1 : (#[srcSize.bytes] : Array UInt64).size ≤ 1 := Nat.le_refl 1
  unfold InitMask.applyCopy
  dsimp only
  rw [h_chk, ite_eq_right Bool.false_ne_true, ite_eq_left h_sz1]
  simp only [allocRange, h_mul, Except.mapError, Bind.bind, Except.bind]

end Miri.Memory.InitMask.WriteProof

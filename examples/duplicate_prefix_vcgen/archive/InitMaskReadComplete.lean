import duplicate_prefix.InitMaskCopy

namespace DuplicatePrefix.InitMaskReadComplete
open Miri.ABI Miri.Memory InitMaskCopy

set_option maxRecDepth 16384
set_option maxHeartbeats 4500000

private theorem first_set_bit_le (word start candidate : Nat)
    (lower : start ≤ candidate) (width : candidate < 64) (set : Nat.testBit word candidate = true) :
    ∃ bit, firstSetBit word start = some bit ∧ bit ≤ candidate := by
  unfold firstSetBit
  unfold_init ".Miri.Memory.InitMaskMaterialized.firstSetBit"
  let offsets := List.range (64 - start)
  let test (offset : Nat) := Nat.testBit word (start + offset)
  change ∃ bit, (offsets.find? test).map (·+start) = some bit ∧ bit ≤ candidate
  have candWithin : candidate-start < offsets.length := by
    simp [offsets]
    omega
  have testAt : test offsets[candidate-start] = true := by
    have h : start+(candidate-start) = candidate := by omega
    simp [offsets, test, h, set]
  cases found : offsets.find? test with
  | none =>
    exact False.elim ((List.find?_eq_none.mp found) _ (List.getElem_mem candWithin) testAt)
  | some offset =>
    obtain ⟨_, i, within, eq, earlier⟩ := List.find?_eq_some_iff_getElem.mp found
    have first : i ≤ candidate-start := by
      apply Classical.byContradiction
      intro later
      have before := earlier (candidate-start) (by omega)
      rw [testAt] at before
      contradiction
    have index : i = offset := by simpa [offsets] using eq
    exact ⟨offset + start, rfl, by omega⟩

private theorem search_outcome (word : UInt64) (block start : Nat)
    (bounded : block*64+64 < 18446744073709551616) :
    ∃ found, searchBlock word block start false = .ok found ∧
      (∀ index, found = some index → block*64+start ≤ index.bytes.toNat ∧ index.bytes.toNat < block*64+64) ∧
      (∀ bit, start ≤ bit → bit < 64 → Nat.testBit word.toNat bit = false →
        ∃ index, found = some index ∧ index.bytes.toNat ≤ block*64+bit) := by
  let bits := 18446744073709551615 - word.toNat
  have search : searchBlock word block start false =
      (match firstSetBit bits start with
      | none => .ok none
      | some bit => (sizeFromBitIndex block bit).map some) := by
    unfold searchBlock
    unfold_init ".Miri.Memory.InitMaskMaterialized.searchBlock"
    change (do match firstSetBit bits start with
      | none => pure none
      | some bit => pure (some (← sizeFromBitIndex block bit))) = _
    cases firstSetBit bits start with
    | none => rfl
    | some bit => cases sizeFromBitIndex block bit <;> rfl
  cases found : firstSetBit bits start with
  | none =>
    refine ⟨none, by rw [search,found], by simp, ?_⟩
    intro bit lo hi clear
    have set : Nat.testBit bits bit = true := by simp [bits, complemented_bit word bit hi, clear]
    obtain ⟨first, firstFound, _⟩ := first_set_bit_le bits start bit lo hi set
    rw [found] at firstFound
    contradiction
  | some bit =>
    have facts := first_set_bit_facts bits start bit found
    let index := Size.ofBytes (UInt64.ofNat (block*64+bit))
    have indexFits : block*64+bit < 18446744073709551616 := by omega
    have indexBytes : index.bytes.toNat = block*64+bit := UInt64.toNat_ofNat_of_lt' indexFits
    have sized : sizeFromBitIndex block bit = .ok index := by
      unfold sizeFromBitIndex
      unfold_init ".Miri.Memory.InitMaskMaterialized.sizeFromBitIndex"
      exact size_from_nat_ok _ indexFits
    refine ⟨some index, by rw [search, found]; change (sizeFromBitIndex block bit).map some = _; rw [sized]; rfl, ?_, ?_⟩
    · intro other eq
      cases eq
      simp only [indexBytes]
      omega
    · intro candidate lo hi clear
      have set : Nat.testBit bits candidate = true := by simp [bits, complemented_bit word candidate hi, clear]
      obtain ⟨first, firstFound, before⟩ := first_set_bit_le bits start candidate lo hi set
      rw [found] at firstFound
      have firstEq := Option.some.inj firstFound
      exact ⟨index, rfl, by rw [indexBytes]; omega⟩

private theorem read_outcome (blocks : InitMaskMaterialized) (block start : Nat)
    (valid : block < blocks.blocks.size)
    (bounded : block*64+64 < 18446744073709551616) :
    ∃ found, read_search blocks block start = .ok found ∧
      (∀ index, found = some index → block*64+start ≤ index.bytes.toNat ∧ index.bytes.toNat < block*64+64) ∧
      (∀ bit, start ≤ bit → bit < 64 → Nat.testBit blocks.blocks[block].toNat bit = false →
        ∃ index, found = some index ∧ index.bytes.toNat ≤ block*64+bit) := by
  obtain ⟨found, answer, geometry, first⟩ := search_outcome blocks.blocks[block] block start bounded
  exact ⟨found, by simpa only [read_search, get_block_ok blocks.blocks block valid, Bind.bind, Except.bind] using answer,
    geometry, first⟩

private theorem loop_has_false (blocks : InitMaskMaterialized) (finish : Size)
    (start steps block bit : Nat) (index : start ≤ block) (inLoop : block < start+steps)
    (valid : block < blocks.blocks.size)
    (bounded : block*64+64 < 18446744073709551616)
    (byte : bit < 64) (within : block*64+bit < finish.bytes.toNat)
    (clear : Nat.testBit blocks.blocks[block].toNat bit = false) :
    ∃ found, forIn (List.range' start steps) ((none, ()) : Option (Option Size) × Unit)
      (search_step blocks finish) = .ok (some (some found), ()) := by
  induction steps generalizing start with
  | zero => omega
  | succ n ih =>
    have currentValid : start < blocks.blocks.size := by omega
    have currentBound : start*64+64 < 18446744073709551616 := by omega
    obtain ⟨out, answer, geometry, witness⟩ := read_outcome blocks start 0 currentValid currentBound
    cases h : out with
    | none =>
      have later : start < block := by
        apply Classical.byContradiction
        intro notLater
        have same : start = block := by omega
        subst start
        obtain ⟨found, foundEq, _⟩ := witness bit (Nat.zero_le _) byte clear
        rw [h] at foundEq
        contradiction
      obtain ⟨found, tail⟩ := ih (start+1) (by omega) (by omega)
      refine ⟨found, ?_⟩
      rw [List.range'_succ]
      simpa only [List.forIn_cons, search_step, answer, h, Bind.bind, Except.bind, Pure.pure, Except.pure] using tail
    | some found =>
      have inside : found.bytes.toNat < finish.bytes.toNat := by
        by_cases same : start = block
        · subst start
          obtain ⟨actual, actualEq, first⟩ := witness bit (Nat.zero_le _) byte clear
          have eq : found = actual := Option.some.inj (h.symm.trans actualEq)
          rw [eq]
          omega
        · have range := (geometry found h).2
          omega
      refine ⟨found, ?_⟩
      rw [List.range'_succ]
      simp only [List.forIn_cons, search_step, answer, h, Bind.bind, Except.bind, Pure.pure,
        Except.pure, inside, ↓reduceIte]

theorem of_find_bit_false_none (blocks : InitMaskMaterialized) (start finish : Size)
    (result : findBit blocks start finish false = .ok none)
    (storageFits : finish.bytes.toNat + 64 < 18446744073709551616) :
    MaterializedInitializedOn blocks start finish := by
  intro block valid bit byte lower upper
  apply Classical.byContradiction
  intro hbit
  have clear : Nat.testBit blocks.blocks[block].toNat bit = false := by
    cases eval : Nat.testBit blocks.blocks[block].toNat bit <;> simp_all
  let firstBlock := start.bytes.toNat / 64
  let firstBit := start.bytes.toNat % 64
  let lastBlock := (finish.bytes.toNat - 1) / 64
  have startLe : firstBlock ≤ block := by dsimp [firstBlock]; omega
  have rightLe : block ≤ lastBlock := by dsimp [lastBlock]; omega
  have firstValid : firstBlock < blocks.blocks.size := by omega
  have firstFits : firstBlock * 64 + 64 < 18446744073709551616 := by dsimp [firstBlock]; omega
  have targetFits : block * 64 + 64 < 18446744073709551616 := by omega
  obtain ⟨found, readFirst, foundBounds, witness⟩ := read_outcome blocks firstBlock firstBit firstValid firstFits
  have firstGet := get_block_ok blocks.blocks firstBlock firstValid
  have firstSearch : searchBlock blocks.blocks[firstBlock] firstBlock firstBit false = .ok found := by
    simpa only [read_search, firstGet, Bind.bind, Except.bind] using readFirst
  have endFits : finish.bytes.toNat - 1 < 18446744073709551616 := by omega
  have endNat : (Size.ofBytes (UInt64.ofNat (finish.bytes.toNat - 1))).bytes.toNat = finish.bytes.toNat - 1 :=
    UInt64.toNat_ofNat_of_lt' endFits
  have endOk := size_from_nat_ok (finish.bytes.toNat - 1) endFits
  unfold findBit at result
  unfold_init ".Miri.Memory.InitMaskMaterialized.findBit" at result
  unfold_init ".Miri.Memory.InitMaskMaterialized.findBitFast" at result
  unfold_init ".Miri.Memory.sizeBytes" at result
  simp only [show ¬start.bytes.toNat ≥ finish.bytes.toNat from by omega, ↓reduceIte] at result
  unfold InitMaskMaterialized.bitIndex at result
  unfold_init ".Miri.Memory.sizeBytes" at result
  unfold_init ".Miri.Memory.blockSize" at result
  unfold sizeFromNat at endOk
  rw [endOk] at result
  simp only [Bind.bind, Except.bind, endNat] at result
  unfold getBlock at firstGet
  rw [firstGet] at result
  simp only [Bind.bind, Except.bind] at result
  unfold searchBlock at firstSearch
  rw [firstSearch] at result
  simp only [Bind.bind, Except.bind] at result
  cases h : found with
  | some early =>
    have inside : early.bytes.toNat < finish.bytes.toNat := by
      by_cases same : firstBlock = block
      · subst block
        have fromFirst : firstBit ≤ bit := by dsimp [firstBlock, firstBit] at *; omega
        obtain ⟨actual, actualEq, byPos⟩ := witness bit fromFirst byte clear
        have same : early = actual := Option.some.inj (h.symm.trans actualEq)
        rw [same]
        omega
      · have stop := (foundBounds early h).2
        omega
    rw [h] at result
    simp [inside, Pure.pure, Except.pure] at result
  | none =>
    have more : firstBlock < block := by
      apply Classical.byContradiction
      intro notMore
      have same : firstBlock = block := by omega
      subst block
      have fromStart : firstBit ≤ bit := by dsimp [firstBlock,firstBit] at *; omega
      obtain ⟨actual, actualEq, _⟩ := witness bit fromStart byte clear
      rw [h] at actualEq
      contradiction
    have many : firstBlock < lastBlock := by omega
    obtain ⟨target, loop⟩ := loop_has_false blocks finish (firstBlock+1) ((lastBlock+1)-(firstBlock+1)) block bit
      (by omega) (by omega) valid targetFits byte upper clear
    have rangeLoop : forIn (Std.Legacy.Range.mk (firstBlock+1) (lastBlock+1) 1 (by decide))
        ((none, ()) : Option (Option Size) × Unit) (search_step blocks finish) = .ok (some (some target), ()) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      simpa [Std.Legacy.Range.size] using loop
    change forIn _ _ (fun block acc => search_step blocks finish block acc) = _ at rangeLoop
    simp only [search_step_raw_eq] at rangeLoop
    rw [h] at result
    change start.bytes.toNat / 64 < (finish.bytes.toNat-1) / 64 at many
    simp only [many, ↓reduceIte] at result
    have run :
        (do let result ← forIn (Std.Legacy.Range.mk (firstBlock+1) (lastBlock+1) 1 (by decide))
              ((none, ()) : Option (Option Size) × Unit) (fun block acc => search_step_raw blocks finish block acc)
            match result.1 with
            | some value => pure value
            | none => pure none) = .ok (some target) := by
      rw [rangeLoop]
      rfl
    have changed : (do
          let result ← forIn (Std.Legacy.Range.mk (firstBlock+1) (lastBlock+1) 1 (by decide))
            ((none, ()) : Option (Option Size) × Unit) (fun block acc => search_step_raw blocks finish block acc)
          match result.1 with
          | some value => pure value
          | none => pure none) = .ok none := by
      apply Eq.trans _ result
      congr 2
      · funext block acc
        unfold search_step_raw getBlock searchBlock
        unfold_init ".Miri.Memory.InitMaskMaterialized.getBlock"
        repeat' (first | rfl | (split <;> try simp_all only [Pure.pure, Except.pure]))
      · funext result
        obtain ⟨flag, unit⟩ := result
        cases flag <;> rfl
    rw [run] at changed
    let foundBit : Except InitMaskError (Option Size) → Bool
      | .ok (some _) => true
      | _ => false
    have impossible : true = false := congrArg foundBit changed
    cases impossible

/-- Successful execution of the initialization check entails every bit
of the checked interval is initialized. This includes materialized masks. -/
theorem of_is_range_initialized (mask : InitMask) (range : AllocRange) (finish : Size)
    (endpoint : range.endExclusive = .ok finish)
    (within : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (storageFits : finish.bytes.toNat+64 < 18446744073709551616)
    (result : mask.isRangeInitialized range = .ok (.ok ())) :
    InitializedOn mask range.start finish := by
  have notOutside : ¬finish.bytes > mask.len.bytes :=
    fun tooFar => Nat.not_lt.mpr within (UInt64.lt_iff_toNat_lt.mp tooFar)
  unfold InitMask.isRangeInitialized at result
  rw [endpoint] at result
  simp only [Bind.bind, Except.bind, notOutside, ↓reduceIte] at result
  cases mask with
  | mk masks len =>
    cases masks with
    | Lazy initialized =>
      cases initialized
      · simp [Pure.pure, Except.pure] at result
      · rfl
    | Materialized blocks =>
      dsimp only at result
      apply of_find_bit_false_none blocks range.start finish _ storageFits
      unfold findBit
      cases first : findBit blocks range.start finish false with
      | error error =>
        unfold findBit at first
        rw [first] at result
        contradiction
      | ok found =>
        cases found with
        | none =>
          unfold findBit at first
          exact first
        | some uninit =>
          unfold findBit at first
          rw [first] at result
          simp only [Bind.bind, Except.bind] at result
          cases tail : findBit blocks uninit finish true with
          | error error =>
            unfold findBit at tail
            rw [tail] at result
            contradiction
          | ok last =>
            unfold findBit at tail
            rw [tail] at result
            simp only [Bind.bind, Except.bind] at result
            let success : Except InitMaskError (Except AllocRange Unit) → Bool
              | .ok (.ok _) => true
              | _ => false
            cases endRange : AllocRange.fromEndpoints uninit (last.getD finish) <;>
              rw [endRange] at result <;>
              have impossible : false = true := congrArg success result
            all_goals cases impossible

/-- Shrink an initialized interval without changing the source mask. -/
theorem initialized_prefix (mask : InitMask) (start finish smaller : Size)
    (bound : smaller.bytes.toNat ≤ finish.bytes.toNat)
    (initialized : InitializedOn mask start finish) :
    InitializedOn mask start smaller := by
  cases mask with
  | mk masks len =>
    cases masks with
    | Lazy _ => exact initialized
    | Materialized blocks =>
      exact fun block valid bit width lower upper =>
        initialized block valid bit width lower (Nat.lt_of_lt_of_le upper bound)

#print axioms of_is_range_initialized
end DuplicatePrefix.InitMaskReadComplete

import CanonicalEntryFacts
import VerifyZeroCachedCanonical

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem Admitted.emittedAliasFrame {program options remaining headroom span before frame pointer length count allowSharedAllocation}
    (loaded : GeneratedBodySafety.loaded = .ok program)
    (admitted : Admitted program options remaining headroom span before frame pointer length count allowSharedAllocation) :
    frame.bodyIdentity = RootBody.reflected.body.identity ∧ frame.body = RootBody.reflected.body.body ∧
      frame.location = .mir ⟨0, 0⟩ ∧ frame.locals.size = 25 := by
  obtain ⟨_, identity, body, location, _⟩ := admitted.boundArguments
  rw [loadedRoot_eq loaded] at identity body
  refine ⟨identity, body, location, admitted.shape.localsAligned.trans ?_⟩
  rw [body]
  with_unfolding_all rfl

/-- The actual entry initializes two arguments. Later locals have an
empty layout cache, and only compiler-selected implicit locals are live. -/
theorem Admitted.aliasInitialTemporarySlot {program options remaining headroom span before frame pointer length count allowSharedAllocation}
    (loaded : GeneratedBodySafety.loaded = .ok program)
    (admitted : Admitted program options remaining headroom span before frame pointer length count allowSharedAllocation)
    (compiler : InitialCompilerControl before frame)
    (index : Nat) (temporary : 3 ≤ index) (within : index < 25) :
    frame.locals[index]? = some
      ⟨if #[6, 13, 14].contains index then .live (.immediate .uninit) else .dead, none⟩ := by
  obtain ⟨_, body, _, size⟩ := admitted.emittedAliasFrame loaded
  have valid : index < frame.locals.size := by omega
  have known : frame.locals[index]? = some frame.locals[index] := Array.getElem?_eq_getElem valid
  obtain ⟨alwaysLive, forBody, outputs⟩ := admitted.shape.localsUntouched
  have canonical : CallMachine.alwaysLiveVarsAndTemps RootBody.reflected.body.body = .ok #[6, 13, 14] := by
    with_unfolding_all rfl
  rw [body, canonical] at forBody
  have selected := Except.ok.inj forBody
  have value := outputs index _ temporary known
  have cache := compiler.temporariesUncached index _ temporary known
  rw [← selected] at value
  rw [known]
  cases stored : frame.locals[index]
  simp_all

theorem Admitted.aliasInitialArgumentSlots {program options remaining headroom span before frame pointer length count allowSharedAllocation}
    (admitted : Admitted program options remaining headroom span before frame pointer length count allowSharedAllocation) :
    ∃ buffer, Immediate.newSlice pointer length PreparedReflection.actual.runtime.target.base = .ok buffer ∧
      frame.locals[1]? = some ⟨.live (.immediate buffer), some RootCompilerFacts.sliceLayout⟩ ∧
      frame.locals[2]? = some
        ⟨.live (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 count)))),
          some RootCompilerFacts.usizeLayout⟩ := by
  obtain ⟨buffer, _, _, _, rebuilt, arg, n⟩ := admitted.boundArguments
  refine ⟨buffer, rebuilt, ?_, ?_⟩
  · have layout := admitted.argLayout
    cases found : frame.locals[1]? with
    | none => simp [found] at arg
    | some state =>
      cases state
      simp_all
  · have layout := admitted.countLayout
    cases found : frame.locals[2]? with
    | none => simp [found] at n
    | some state =>
      cases state
      simp_all


open RootZeroShallowReturn
theorem zeroCountAliasEntry {program options remaining headroom span before frame pointer length allowSharedAllocation}
    (loaded : GeneratedBodySafety.loaded = .ok program)
    (admitted : Admitted program options remaining headroom span before frame pointer length 0 allowSharedAllocation)
    (compiler : InitialCompilerControl before frame) :
    ZeroEntry frame before.machine := by
  obtain ⟨identity, body, location, size⟩ := admitted.emittedAliasFrame loaded
  have instanceEq := admitted.identity.trans (loadedRootInstance_eq loaded)
  obtain ⟨_, _, _, count⟩ := admitted.aliasInitialArgumentSlots
  have result : (frame.locals[0]'(by omega : 0 < frame.locals.size)) =
      ⟨.live (.immediate .uninit), none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans admitted.resultSlot)
  have value : (frame.locals[2]'(by omega : 2 < frame.locals.size)) =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))), some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans count)
  have unused (index : Nat) (bound : index < frame.locals.size) (lo : 3 ≤ index) (hi : index ≤ 5) :
      frame.locals[index] = ⟨.dead, none⟩ := by
    have actual := admitted.aliasInitialTemporarySlot loaded compiler index lo (by omega)
    have notImplicit : #[6,13,14].contains index = false := by
      have which : index = 3 ∨ index = 4 ∨ index = 5 := by omega
      rcases which with h | h | h <;> subst index <;> decide +kernel
    rw [notImplicit] at actual
    exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans actual)
  refine {
    body, identity, callee := instanceEq, location, size
    live0 := congrArg LocalState.value result
    uncached0 := congrArg LocalState.layout result
    dead3 := congrArg LocalState.value (unused 3 (by omega) (by decide) (by decide))
    dead4 := congrArg LocalState.value (unused 4 (by omega) (by decide) (by decide))
    dead5 := congrArg LocalState.value (unused 5 (by omega) (by decide) (by decide))
    uncached4 := congrArg LocalState.layout (unused 4 (by omega) (by decide) (by decide))
    uncached5 := congrArg LocalState.layout (unused 5 (by omega) (by decide) (by decide))
    zero := congrArg LocalState.value value
    cached2 := congrArg LocalState.layout value
    noClocks := admitted.stack.calleeClocksOff
    immediate := admitted.immediateLocals
    ghost := admitted.profile.ghostOff
    shallow := admitted.profile.shallow
    fixed := admitted.profile.fixed }

#print axioms zeroCountAliasEntry
end DuplicatePrefix.CanonicalCallDomain

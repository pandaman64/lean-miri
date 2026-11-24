import CanonicalSourceControl
import duplicate_prefix.ArchiveCatalogRoot

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem generatedInput_eq : GeneratedBodySafety.input = Program.imported := rfl

theorem loadedRoot_eq {program : BodyVCGen.LoadedProgram}
    (loaded : GeneratedBodySafety.loaded = .ok program) :
    program.root = RootBody.reflected.body := by
  have root := RootBody.generated_catalog_root
  rw [← generatedInput_eq] at root
  change GeneratedBodySafety.loaded.map (·.root) = .ok RootBody.reflected.body at root
  rw [loaded] at root
  exact Except.ok.inj root

open Lean Elab Term Meta in
elab "selectPreparedRoot" : term => do
  let definitions := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".Miri.Verification.BodyVCGen.loadPreparedRoot" then some name else none
  match definitions with
  | [name] => mkConstWithFreshMVarLevels name
  | _ => throwError "expected the source program's prepared-root query"

private def loadInstanceWithoutCatalog (input : ExecutionInput) (root : Nat) : Except String CallInstance := do
  let lowered ← lowerProgram input.document
  let prepared ← CallResolution.prepare lowered
  return (← selectPreparedRoot prepared root).1

private theorem projectRootInstance (input : ExecutionInput) (root : Nat) :
    (BodyVCGen.loadProgram input root).map (·.rootInstance) = loadInstanceWithoutCatalog input root := by
  unfold BodyVCGen.loadProgram loadInstanceWithoutCatalog
  cases lowerProgram input.document with
  | error failure => rfl
  | ok lowered =>
    simp only [bind, Except.bind]
    cases CallResolution.prepare lowered with
    | error failure => rfl
    | ok prepared =>
      simp only [bind]
      split <;> rfl

set_option cbv.maxSteps 5000000 in
private theorem importedRootInstance :
    loadInstanceWithoutCatalog Program.imported 0 = .ok RootBody.reflected.functionInstance := by
  cbv

/-- The selected instance is the exact key used by actual call dispatch. -/
theorem loadedRootInstance_eq {program : BodyVCGen.LoadedProgram}
    (loaded : GeneratedBodySafety.loaded = .ok program) :
    program.rootInstance = RootBody.reflected.functionInstance := by
  have root : (BodyVCGen.loadProgram Program.imported 0).map (·.rootInstance) =
      .ok RootBody.reflected.functionInstance :=
    (projectRootInstance Program.imported 0).trans importedRootInstance
  rw [← generatedInput_eq] at root
  change GeneratedBodySafety.loaded.map (·.rootInstance) = .ok RootBody.reflected.functionInstance at root
  rw [loaded] at root
  exact Except.ok.inj root

theorem Admitted.emittedFrame {program options remaining headroom span before frame pointer length count}
    (loaded : GeneratedBodySafety.loaded = .ok program)
    (admitted : Admitted program options remaining headroom span before frame pointer length count) :
    frame.bodyIdentity = RootBody.reflected.body.identity ∧ frame.body = RootBody.reflected.body.body ∧
      frame.location = .mir ⟨0, 0⟩ ∧ frame.locals.size = 25 := by
  obtain ⟨_, identity, body, location, _⟩ := admitted.boundArguments
  rw [loadedRoot_eq loaded] at identity body
  refine ⟨identity, body, location, admitted.shape.localsAligned.trans ?_⟩
  rw [body]
  with_unfolding_all rfl

/-- The actual entry initializes two arguments. Later locals have an
empty layout cache, and only compiler-selected implicit locals are live. -/
theorem Admitted.initialTemporarySlot {program options remaining headroom span before frame pointer length count}
    (loaded : GeneratedBodySafety.loaded = .ok program)
    (admitted : Admitted program options remaining headroom span before frame pointer length count)
    (compiler : InitialCompilerControl before frame)
    (index : Nat) (temporary : 3 ≤ index) (within : index < 25) :
    frame.locals[index]? = some
      ⟨if #[6, 13, 14].contains index then .live (.immediate .uninit) else .dead, none⟩ := by
  obtain ⟨_, body, _, size⟩ := admitted.emittedFrame loaded
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

theorem Admitted.initialArgumentSlots {program options remaining headroom span before frame pointer length count}
    (admitted : Admitted program options remaining headroom span before frame pointer length count) :
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

#print axioms Admitted.emittedFrame
#print axioms loadedRootInstance_eq
#print axioms Admitted.initialTemporarySlot
#print axioms Admitted.initialArgumentSlots

end DuplicatePrefix.CanonicalCallDomain

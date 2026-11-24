import duplicate_prefix.LenEntryControl

namespace DuplicatePrefix.LenRuntimeProfile

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem control_of_host (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (host : after.user.payload.payload.user.host = before.user.payload.payload.user.host) :
    let hooks := (PreparedContracts.actualConfig options () remaining span).terminators
    hooks.getControl after.user = hooks.getControl before.user := by
  dsimp only
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).terminators]
  simp only [EvalTerminatorMachine.genericHooks,host]

theorem accounted_flags (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let hooks := (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    let after := PtrMetadataReturn.accountedMachine options remaining span machine
    (hooks.getControl after.user).checkedArithmetic = (hooks.getControl machine.user).checkedArithmetic ∧
    (hooks.getControl after.user).gcInterval = (hooks.getControl machine.user).gcInterval ∧
    after.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
    after.threads = machine.threads := by
  dsimp only
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl⟩

end DuplicatePrefix.LenRuntimeProfile

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.LenRuntimeProfile.control_of_host,
      ``DuplicatePrefix.LenRuntimeProfile.accounted_flags] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved length runtime dependency {dependency}"

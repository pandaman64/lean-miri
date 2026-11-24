import duplicate_prefix.AsMutCallCore
import duplicate_prefix.AsMutDispatch
import duplicate_prefix.AsMutEvaluateCall
import duplicate_prefix.CallItemDispatch

namespace DuplicatePrefix.AsMutDispatchExact
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem dispatch
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (span : PreparedContracts.FixedSpanQuery) (value : Immediate Provenance)
    (before after : RootState) (destination : RuntimeStackPlace Provenance)
    (backend : before.machine.user.payload.payload.user.backend = .none)
    (race : before.machine.dataRace = none) :
    let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
    let operand : OpTy Provenance := ⟨.immediate value, RootCompilerFacts.sliceLayout⟩
    let args : Array (FnArg Provenance) := #[.Copy operand]
    AsMutCallCore.core h operand destination before = .ok () after →
    Call.initFnCall h () (budget+1) ⟨.Instance HelperCompilerFacts.asMutPtrCall.callee,
      .Rust, some HelperCompilerFacts.asMutPtrAbi, args, false, destination, some 7,.Unreachable⟩ before =
      .ok () after := by
  intro h operand args initialized
  have findMir := AsMutDispatch.find_mir options limits remaining span before args destination (some 7)
    .Unreachable backend race
  have rust : h.isRustCall .Rust = false := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.isRustCall .Rust = false
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    rfl
  have kind : h.instanceKind HelperCompilerFacts.asMutPtrCall.callee = pure (.Item 3) :=
    AsMutCalleeLeaves.instance_kind options limits remaining span
  apply CallItemDispatch.dispatch_one h _ before _ budget
  rw [CallItemDispatch.item_step_nounwind h HelperCompilerFacts.asMutPtrCall.callee 3
    HelperCompilerFacts.asMutPtrAbi args false destination (some 7) .Rust
    kind AsMutCallFacts.abi_flags.2.1 rust]
  unfold CallItemDispatch.itemStage
  simp only [bind,EStateM.bind]
  erw [findMir]
  simp only [bind,EStateM.bind]
  rw [AsMutCallCore.actual_entry_eq options limits remaining span operand destination]
  dsimp only [h] at initialized
  rw [initialized]
  rfl

end DuplicatePrefix.AsMutDispatchExact

#print axioms DuplicatePrefix.AsMutDispatchExact.dispatch

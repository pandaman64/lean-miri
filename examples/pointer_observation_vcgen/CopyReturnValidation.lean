import CopyTail

namespace PointerObservation.Copy

open Miri.ABI Miri.Input Miri.TreeBorrows Miri.Interpreter Miri.Verification Miri.Memory Miri.MIR Fixture

set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
attribute [local cbv_opaque] ValidityVisitor.validatePlace

/-- Write the copied scalar to the return local and optionally run its canonical validation. -/
def postCopyReturnWritePre (source : UInt8) (layout4 : LocalLayout)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (validate : Bool)
    (post : State → Prop) (onError : StepError → State → Prop) : Prop :=
    match postCopyLoadEntry source false layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let checked := ExecutionMachine.withValidation config limits
        let dest : RuntimePlace Provenance := ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 1), layout⟩
        let value : Immediate Provenance := .scalar (.fromScalarInt (ScalarInt.ofUInt8 source))
        let entry := {entry with machine := {entry.machine with memory}}
        let hooks := (ExecutionMachine.projectionHooks checked).place
        PlaceReadWriteWP.writeNoValidatePre hooks () value dest (fun _ after =>
          if validate then
            RvalueWP.actionPre (hooks.enforceValidity () layout)
              (fun enabled after => if enabled then
                RvalueWP.actionPre (hooks.validate () dest) (fun _ => post) onError after
                else post after) onError after
          else post after) onError entry

/-- Shallow validation of the written u8 leaves the output and every other
machine field unchanged, for arbitrary retained memory and continuations. -/
theorem postCopyLoad_validate (source : UInt8) (layout4 : LocalLayout)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (post : State → Prop) (onError : StepError → State → Prop) :
    postCopyReturnWritePre source layout4 memory true post onError =
    postCopyReturnWritePre source layout4 memory false post onError := by
  cbv

#print axioms postCopyLoad_validate
end PointerObservation.Copy

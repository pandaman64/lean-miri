import SuccessorGenerated

/-! The selected copy and observation path in the exported `copy_then_load`. -/
namespace CopySuccessorVC

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification
open GeneratedBodySafety

set_option maxRecDepth 65536

private theorem copy_node :
    ∃ span ty, mir_0_bb0_5 = .statement (.Intrinsic (.CopyNonOverlapping
      ⟨.Move ⟨5, #[]⟩, .Move ⟨6, #[]⟩, .Constant ⟨span, none, .Val (.Scalar (.Int 1 8)) ty⟩⟩)) :=
  ⟨_, _, rfl⟩

private theorem load_node :
    ∃ retag, mir_0_bb0_10 = .statement (.Assign ⟨0, #[]⟩
      (.Use (.Copy ⟨3, #[.Deref]⟩) retag)) := ⟨_, rfl⟩

section

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

/-- Feed the generated copy continuation into the generated load
continuation through the exact transfer rules of the four intervening
statements. Layout, validation and borrow policies remain those from the
supplied canonical configuration. Both sides preserve an error at any row. -/
theorem copy_and_load_pre_eq
    (config : Config) (limits : ExecutionMachine.Limits)
    (choose : State → C) (post : Bool → State → Prop) (onError : StepError → State → Prop)
    (before : State) :
    (transfer_0_bb0_5 config limits).pre (choose before) (fun _ afterCopy =>
      (transfer_0_bb0_6 config limits).pre (choose afterCopy) (fun _ afterAssign =>
        (transfer_0_bb0_7 config limits).pre (choose afterAssign) (fun _ afterDead6 =>
          (transfer_0_bb0_8 config limits).pre (choose afterDead6) (fun _ afterDead5 =>
            (transfer_0_bb0_9 config limits).pre (choose afterDead5) (fun _ afterDead4 =>
              (transfer_0_bb0_10 config limits).pre (choose afterDead4) post onError afterDead4)
              onError afterDead5) onError afterDead6) onError afterAssign)
        onError afterCopy) onError before ↔
    BodyCFG.nodePre config limits (choose before) (fun _ afterCopy =>
      BodyCFG.nodePre config limits (choose afterCopy) (fun _ afterAssign =>
        BodyCFG.nodePre config limits (choose afterAssign) (fun _ afterDead6 =>
          BodyCFG.nodePre config limits (choose afterDead6) (fun _ afterDead5 =>
            BodyCFG.nodePre config limits (choose afterDead5) (fun _ afterDead4 =>
              BodyCFG.nodePre config limits (choose afterDead4) post onError afterDead4 mir_0_bb0_10)
            onError afterDead5 mir_0_bb0_9) onError afterDead6 mir_0_bb0_8)
          onError afterAssign mir_0_bb0_7) onError afterCopy mir_0_bb0_6)
      onError before mir_0_bb0_5 := by
  simp only [(transfer_0_bb0_5 config limits).exact, (transfer_0_bb0_6 config limits).exact,
    (transfer_0_bb0_7 config limits).exact, (transfer_0_bb0_8 config limits).exact,
    (transfer_0_bb0_9 config limits).exact, (transfer_0_bb0_10 config limits).exact]
  rfl

end

-- Inspect the predicate field independently of the row equivalence proof.
open Lean Elab Command in
run_cmd do
  for (row, expected) in [
      (``transfer_0_bb0_5, ``CopyTreeWP.copyPre),
      (``transfer_0_bb0_10, ``PlaceReadWriteWP.copyPre)] do
    let some (.defnInfo info) := (← getEnv).find? row
      | throwError "missing generated transfer {row}"
    let value := info.value.getLambdaBody
    unless value.getAppFn.isConstOf ``GeneratedBodyVC.ReducedNode.mk do
      throwError "unexpected generated transfer shape for {row}"
    let args := value.getAppArgs
    let some predicate := args[args.size - 2]?
      | throwError "missing generated predicate for {row}"
    unless (predicate.find? (·.isConstOf expected)).isSome do
      throwError "generated transfer {row} lost {expected}"

#print axioms copy_and_load_pre_eq

end CopySuccessorVC

import ZeroAssignment
import ZeroTail

namespace DuplicatePrefix.ZeroTail
open Miri.MIR
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option cbv.maxSteps 10000000

/-- The imported standalone body writes Boolean true and reaches a normal
return terminator. These are the emitted operations consumed by the
assignment and Return proofs. -/
theorem zeroNodes :
    ((program.root.body.basicBlocks[1]?).bind fun block =>
      (block.statements[1]?).map Statement.kind) =
      some (.Assign ⟨0, #[]⟩ (.Use (.Constant ZeroBoolean.trueOperand) .Yes)) ∧
    ((program.root.body.basicBlocks[10]?).map fun block =>
      (block.statements.size, block.terminator.kind, block.cleanup)) =
      some (0, .Return, false) := by
  cbv

#print axioms zeroNodes
end DuplicatePrefix.ZeroTail

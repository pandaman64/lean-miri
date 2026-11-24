import duplicate_prefix.AsMutLocalStages
import duplicate_prefix.AsMutPassArgument
import duplicate_prefix.AsMutCallCore
namespace DuplicatePrefix.AsMutCurrentInstall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceMetadata
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def spanFrame (frame : CompilerFrameContext.ActualFrame) :=
  {frame with location := .unwinding ⟨73⟩}
def cacheFrame (frame : CompilerFrameContext.ActualFrame) (valid : (1 : MIR.LocalId) < frame.locals.size) :=
  LocalOperands.cachedLayoutFrame (spanFrame frame) 1 ActualReferenceMetadata.reference valid

def action (h : AsMutCallCore.RootHooks) (value : Immediate Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  AsMutCallCore.spanAt h (← h.localSpan HelperCompilerFacts.asMutPtrBody.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
    (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret) 0 ⟨1,#[]⟩ ty.ty false
  pure (1,1)


theorem install_of_copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (valid : 1 < frame.locals.size) (uncached : frame.locals[1].layout = none)
    (value : Immediate Provenance) (after : RootState) :
    let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
    Call.passArgument h () (.Copy ⟨.immediate value,reference⟩)
      (AsMutPassArgument.abi.args.getD 0 AsMutPassArgument.abi.ret)
      (AsMutPassArgument.abi.args.getD 0 AsMutPassArgument.abi.ret) 0 ⟨1,#[]⟩ 1 false
      (Storage.withCurrent frames (cacheFrame frame valid) machine) = .ok () after →
    action h value (Storage.withCurrent frames frame machine) = .ok (1,1) after := by
  intro h copied
  have spanAt := AsMutLocalStages.span1 options limits remaining span frames frame machine body identity callee
  have setSpan := CallEntryLocals.set_span options limits remaining span frames frame machine ⟨73⟩
  have layout := AsMutLocalStages.layout1 options limits remaining span frames (spanFrame frame) machine
    body identity callee valid uncached
  have setSpan' : AsMutCallCore.spanAt h ⟨73⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (spanFrame frame) machine) := setSpan
  have layout' : h.localLayout () 1 (Storage.withCurrent frames (spanFrame frame) machine) =
      .ok reference (Storage.withCurrent frames (cacheFrame frame valid) machine) := layout
  unfold action
  simp only [bind,EStateM.bind]
  rw [spanAt]
  simp only [bind,EStateM.bind]
  rw [setSpan']
  dsimp only
  rw [layout']
  dsimp only
  simp only [bind,EStateM.bind,reference_ty]
  rw [copied]
  rfl

end
end DuplicatePrefix.AsMutCurrentInstall

#print axioms DuplicatePrefix.AsMutCurrentInstall.install_of_copy

import duplicate_prefix.GuardFunctionConstant
import duplicate_prefix.PointerAddCurrentFacts

namespace DuplicatePrefix.PointerAddLanguageGuardFacts
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def constant : ConstOperand := ⟨⟨95⟩, none, .Val .ZeroSized 83⟩
theorem literal : constant.value = .Val .ZeroSized 83 := rfl
abbrev functionLayout := LanguageZeroFunctionFacts.functionLayout
theorem layout_eq : PreparedReflection.actual.compiler.runtime.lookup 83 = .ok functionLayout :=
  LanguageZeroFunctionFacts.functionLayout_query

theorem resolve_current
    (framesBefore : Array (Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = PointerAddCurrentFacts.body.body)
    (identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity)
    (function : frame.functionInstance = PointerAddCurrentFacts.call.callee)
    (location : frame.location = .mir ⟨0,2⟩) :
    CompilerProviders.resolveCurrent PreparedReflection.actual.compiler (PreparedReflection.fixedInstance GuardCompilerFacts.languageCall.callee).instanceKind.defId #[]
      (Storage.withCurrent framesBefore frame machine) =
      .ok GuardCompilerFacts.languageCall.callee (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerProviders.resolveCurrent
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [body, identity, function, location]
  unfold_languagezero_provider_lift
  with_unfolding_all rfl


theorem function_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = PointerAddCurrentFacts.body.identity.index)
    (location : frame.location = .mir ⟨0,2⟩)
    (fnInstance : frame.functionInstance = PointerAddCurrentFacts.call.callee) :
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime functions
      arithmetic externStatic MemoryErrors.constant constant none none
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit,functionLayout⟩ (Storage.withCurrent frames frame machine) := by
  unfold ConstantMachine.evalOperandWithLayout
  rw [literal]
  simp only [ConstantMachine.evalValueWithLayout, Option.map_none]
  unfold valueToOpWithLayout
  have layout : PreparedReflection.actual.compiler.runtime.lookup 83 = .ok functionLayout := layout_eq
  rw [layout]
  unfold_internal ".Interpreter.metadata"
  rfl

theorem function_operand [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = PointerAddCurrentFacts.body.identity.index)
    (location : frame.location = .mir ⟨0,2⟩)
    (fnInstance : frame.functionInstance = PointerAddCurrentFacts.call.callee) :
    OperandMachine.evalOperand (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (PreparedContracts.actualConfig options () remaining span) limits))
      ()  (.Constant constant) none
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit,functionLayout⟩ (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  change config.operands.constant () constant none state = _
  rw [constantAt]
  exact function_eval_at_bound source config.functions config.arithmetic externStatic
    frames frame machine bodyIndex location fnInstance

end
end DuplicatePrefix.PointerAddLanguageGuardFacts

#print axioms DuplicatePrefix.PointerAddLanguageGuardFacts.resolve_current
#print axioms DuplicatePrefix.PointerAddLanguageGuardFacts.function_operand

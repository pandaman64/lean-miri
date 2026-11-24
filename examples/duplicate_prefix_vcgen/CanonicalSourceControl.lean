import CanonicalCallDomain
import Miri.Interpreter.CallMachine

/-! Compiler control and local-layout cache facts needed by the specialized
source proofs for the canonical prepared call. -/
namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- Entry metadata for the pinned non-track-caller root. The two argument
layouts and the empty return layout are already specified by `Admitted`. -/
structure InitialCompilerControl (before : State) (frame : Frame) : Prop where
  noTrackCaller : frame.trackCallerArg = none
  highestRelevance : frame.extra.userRelevance = 255
  currentRelevant : ∃ thread, before.machine.threads.activeThread? = some thread ∧
    thread.topUserRelevantFrame = some (before.stack.frames.size - 1)
  temporariesUncached : ∀ index slot, 3 ≤ index → frame.locals[index]? = some slot → slot.layout = none

/-- The supported compiler-control subset keeps the whole count space, both
return carriers and both concrete and nonconcrete empty arguments. -/
def SourceSafetyGoal (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) : Prop :=
  ∀ program, GeneratedBodySafety.loaded = .ok program →
    ∀ (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (length count : UInt64),
      Admitted program options remaining preparedTagHeadroom span before frame pointer length count →
      InitialCompilerControl before frame →
      GeneratedBodySafety.requiredForEveryChoiceAt
        (PreparedContracts.actualConfig options () (remaining + 1) span) limits before

/-- The production raw frame constructor never seeds a layout cache or a
track-caller argument. ABI initialization may subsequently cache argument
layouts, whose exact supported shapes are in `Admitted`. -/
theorem rawFrameCacheEmpty (body : LoadedBody) (callee : FrameInstance) (extra : MachineHooks.FrameExtra)
    (continuation : ReturnContinuation) (destination : RuntimeStackPlace Provenance)
    (span : SpanRef) (identity : LocalsIdentity) :
    let frame : Frame := Miri.Interpreter.Frame.create body callee extra continuation destination span identity
    frame.trackCallerArg = none ∧ ∀ (index : Nat) (slot : LocalState Provenance LocalLayout),
      frame.locals[index]? = some slot → slot.layout = none := by
  dsimp only
  refine ⟨rfl, ?_⟩
  intro index slot lookup
  change (Array.replicate body.body.locals.size ⟨.dead, none⟩)[index]? = some slot at lookup
  obtain ⟨bound, found⟩ := Array.getElem?_eq_some_iff.mp lookup
  simpa using congrArg LocalState.layout found.symm

/-- The production relevance query assigns a local definition its top
rank when the compiler says it has no track-caller requirement. -/
theorem localDefinitionRelevance (hooks : FrameMetadata.CompilerHooks MiriMemoryKind Machine.RootUser)
    (frame : Frame) (before : State)
    (callerArg : hooks.requiresCallerLocation frame.functionInstance before = .ok false before)
    (localDef : hooks.isLocalDefinition frame.functionInstance before = .ok true before) :
    FrameMetadata.userRelevance hooks frame before = .ok 255 before := by
  simp [FrameMetadata.userRelevance, EStateM.bind, Bind.bind, callerArg, localDef, EStateM.pure, Pure.pure]

/-- Both projections refer to the same imported compiler document. -/
theorem compilerSourceComparator : PreparedContracts.SourceComparator :=
  ⟨by with_unfolding_all rfl⟩

#print axioms rawFrameCacheEmpty
#print axioms localDefinitionRelevance
#print axioms compilerSourceComparator

end DuplicatePrefix.CanonicalCallDomain

import duplicate_prefix.CallEntryFacts
import duplicate_prefix.Storage

namespace DuplicatePrefix.PointerAddFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem compute_local (framesBefore : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (ty : TyId) (layout : LocalLayout)
    (normalized : CompilerFrameContext.localType PreparedReflection.actual.compiler frame localId = .ok ty)
    (lookup : PreparedReflection.actual.compiler.runtime.lookup ty = .ok layout) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent framesBefore frame machine) =
    .ok layout (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  unfold_frame_query_lift
  simp only [pure, EStateM.pure, bind, EStateM.bind]
  rw [lookup]
  rfl

#print axioms compute_local
end DuplicatePrefix.PointerAddFacts

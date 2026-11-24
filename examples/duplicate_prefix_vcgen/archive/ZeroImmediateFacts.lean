import duplicate_prefix.LocalPlaces
import Miri.Input.CompilerFrameContext
import duplicate_prefix.ActualLocalCopy
namespace DuplicatePrefix.ZeroImmediateFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def AllImmediate (frame : CompilerFrameContext.ActualFrame) : Prop :=
  ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory)

theorem all_immediate_set (frame : CompilerFrameContext.ActualFrame) (id : MIR.LocalId)
    (slot : LocalState Provenance LocalLayout) (valid : id < frame.locals.size)
    (all : AllImmediate frame) (immediate : ∀ memory, slot.value ≠ .live (.indirect memory)) :
    AllImmediate {frame with locals := frame.locals.set id slot valid} := by
  intro entry member memory
  rcases Array.mem_or_eq_of_mem_set (w := valid) member with old | rfl
  · exact all entry old memory
  · exact immediate memory

theorem all_immediate_cache (frame : CompilerFrameContext.ActualFrame) (id : MIR.LocalId)
    (layout : LocalLayout) (valid : id < frame.locals.size) (all : AllImmediate frame) :
    AllImmediate (LocalPlaces.cachePlaceLayout frame id layout valid) := by
  apply all_immediate_set frame id _ valid all
  intro memory
  exact all frame.locals[id] (Array.mem_iff_getElem.mpr ⟨id,valid,rfl⟩) memory

theorem all_immediate_written (frame : CompilerFrameContext.ActualFrame) (id : MIR.LocalId)
    (layout : LocalLayout) (value : Immediate Provenance) (valid : id < frame.locals.size)
    (all : AllImmediate frame) :
    AllImmediate (ActualLocalCopy.written frame id layout valid value) := by
  apply all_immediate_set (LocalPlaces.cachePlaceLayout frame id layout valid) id _ _
    (all_immediate_cache frame id layout valid all)
  intro memory
  simp

end DuplicatePrefix.ZeroImmediateFacts

import RejectionEntryAfterLength

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter

/-- The emitted shared reference fills local 12 and the ensuing call caches
its usize destination. All other guard operands remain in place. -/
def BeforeLengthReturn.ofSharedReference
    (frame : CompilerFrameContext.ActualFrame) (count : UInt64) (reference : Immediate Provenance)
    (referenceLayout : LocalLayout) (size : frame.locals.size = 25)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩)
    (slot7 : frame.locals[7]? = some ⟨.live (.immediate .uninit), none⟩)
    (slot8 : frame.locals[8]? = some ⟨.live (.immediate .uninit), none⟩)
    (slot9 : frame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
      some RootCompilerFacts.usizeLayout⟩)
    (slot10 : frame.locals[10]? = some ⟨.live (.immediate .uninit), none⟩)
    (slot13 : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩)
    (immediate : ZeroImmediateFacts.AllImmediate frame) (noClocks : frame.extra.dataRace = none) :
    let shared := {frame with
      location := FrameLocation.mir ⟨2,12⟩
      locals := frame.locals.set 12 ⟨.live (.immediate reference), some referenceLayout⟩ (by omega)}
    BeforeLengthReturn (LocalPlaces.cachePlaceLayout shared 11 RootCompilerFacts.usizeLayout
      (by simp [shared, size])) count := by
  let shared := {frame with
    location := FrameLocation.mir ⟨2, 12⟩
    locals := frame.locals.set 12 ⟨.live (.immediate reference), some referenceLayout⟩ (by omega)}
  have valid11 : 11 < shared.locals.size := by simp [shared, size]
  have slot7' : frame.locals[7]'(by omega) = ⟨.live (.immediate .uninit), none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (show 7 < frame.locals.size by omega)).symm.trans slot7)
  have sharedImmediate : ZeroImmediateFacts.AllImmediate shared := by
    intro slot member memory
    change slot ∈ frame.locals.set 12 ⟨.live (.immediate reference), some referenceLayout⟩ (by omega) at member
    rcases Array.mem_or_eq_of_mem_set member with old | rfl
    · exact immediate slot old memory
    · simp
  refine {
    size := by simp [LocalPlaces.cachePlaceLayout, size]
    body := body
    identity := identity
    callee := callee
    temp := reference
    slot0 := ?_
    live7 := ?_
    slot8 := ?_
    slot9 := ?_
    slot10 := ?_
    cached11 := ?_
    live12 := ?_
    slot13 := ?_
    immediate := ?_
    noClocks := noClocks }
  all_goals
    first
    | change ZeroImmediateFacts.AllImmediate (LocalPlaces.cachePlaceLayout shared 11 RootCompilerFacts.usizeLayout valid11)
      exact ZeroImmediateFacts.all_immediate_cache shared 11 RootCompilerFacts.usizeLayout valid11 sharedImmediate
    | simp [LocalPlaces.cachePlaceLayout, Array.getElem_set, slot0, slot7', slot8, slot9, slot10, slot13]

#print axioms BeforeLengthReturn.ofSharedReference
end DuplicatePrefix.RootZeroShallowReturn

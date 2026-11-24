import RootRejectedAfterLen
import duplicate_prefix.PtrMetadataExecution

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter
open PtrMetadataExecution

/-- The caller shape before the retained slice-length call returns to block 3. -/
structure BeforeLengthReturn (frame : CompilerFrameContext.ActualFrame) (count : UInt64) where
  size : frame.locals.size = 25
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  temp : Immediate Provenance
  slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩
  live7 : (frame.locals[7]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  slot8 : frame.locals[8]? = some ⟨.live (.immediate .uninit), none⟩
  slot9 : frame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
    some RootCompilerFacts.usizeLayout⟩
  slot10 : frame.locals[10]? = some ⟨.live (.immediate .uninit), none⟩
  cached11 : (frame.locals[11]'(by rw [size]; decide)).layout = some RootCompilerFacts.usizeLayout
  live12 : (frame.locals[12]'(by rw [size]; decide)).value = .live (.immediate temp)
  slot13 : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩
  immediate : ZeroImmediateFacts.AllImmediate frame
  noClocks : frame.extra.dataRace = none

private theorem someSlot {frame : CompilerFrameContext.ActualFrame} {i : Nat}
    (inside : i < frame.locals.size) {slot : LocalState Provenance LocalLayout}
    (found : frame.locals[i]? = some slot) : frame.locals[i] = slot :=
  Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans found)

def BeforeLengthReturn.rejectionEntry (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (length count : UInt64)
    (before : BeforeLengthReturn frame count)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true) :
    RejectionEntry
      {writeFrame frame 11 (.scalar (.fromScalarInt (.ofUInt64 length)))
        (by rw [before.size]; decide) with location := .mir ⟨3, 0⟩} machine length count := by
  have bound : 11 < frame.locals.size := by rw [before.size]; decide
  have l0 := someSlot (by rw [before.size]; decide) before.slot0
  have l8 := someSlot (by rw [before.size]; decide) before.slot8
  have l9 := someSlot (by rw [before.size]; decide) before.slot9
  have l10 := someSlot (by rw [before.size]; decide) before.slot10
  have l13 := someSlot (by rw [before.size]; decide) before.slot13
  refine {
    body := before.body
    identity := before.identity
    callee := before.callee
    location := rfl
    size := by simp [writeFrame, before.size]
    temp := before.temp
    live12 := ?_
    live13 := ?_
    cache13 := ?_
    live0 := ?_
    cache0 := ?_
    live7 := ?_
    live8 := ?_
    cache8 := ?_
    live9 := ?_
    cache9 := ?_
    live10 := ?_
    cache10 := ?_
    live11 := ?_
    cache11 := ?_
    immediate := ?_
    noClocks := before.noClocks
    ghost := ghost
    shallow := shallow
    fixed := fixed }
  all_goals
    first
    | exact ZeroImmediateFacts.all_immediate_set frame 11 _ bound before.immediate (by simp)
    | simp [writeFrame, Array.getElem_set, l0, l8, l9, l10, l13,
        before.live7, before.live12, before.cached11]

#print axioms BeforeLengthReturn.rejectionEntry
end DuplicatePrefix.RootZeroShallowReturn

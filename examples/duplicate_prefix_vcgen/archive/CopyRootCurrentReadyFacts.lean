import duplicate_prefix.CopyRootCurrentGuardReach

namespace DuplicatePrefix.CopyRootCurrentReadyFacts
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open CopyRootCurrentGuardBody CopyRootCurrentGuardReach
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

structure Slots (frame : CompilerFrameContext.ActualFrame)
    (source destination : Scalar Provenance) (n : UInt64) : Prop where
  size : frame.locals.size = 17
  zero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  sourceAt : frame.locals[1]? = some ⟨.live (.immediate (.scalar source)),some CopyCompilerFacts.sourcePointerLayout⟩
  destinationAt : frame.locals[2]? = some ⟨.live (.immediate (.scalar destination)),some CopyCompilerFacts.destPointerLayout⟩
  countAt : frame.locals[3]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩
  unit : frame.locals[4]? = some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩
  condition : frame.locals[5]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩
  temporarySource : frame.locals[14]? = some ⟨.dead,none⟩
  temporaryDestination : frame.locals[15]? = some ⟨.dead,none⟩
  temporaryCount : frame.locals[16]? = some ⟨.dead,none⟩

theorem ready_slots (blocked : CompilerFrameContext.ActualFrame) (valid : 4 < blocked.locals.size)
    (source destination : Scalar Provenance) (n : UInt64)
    (before : blocked.locals =
      #[⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar source)),some CopyCompilerFacts.sourcePointerLayout⟩,
        ⟨.live (.immediate (.scalar destination)),some CopyCompilerFacts.destPointerLayout⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩,
        ⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩] ++
        Array.replicate 11 ⟨.dead,none⟩) :
    Slots (ready blocked valid) source destination n := by
  have kept (i : Nat) (neq : i ≠ 4) : (ready blocked valid).locals[i]? = blocked.locals[i]? := by
    simp [ready,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm neq]
  constructor
  · simp [ready,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,before]
  · rw [kept 0 (by decide),before];rfl
  · rw [kept 1 (by decide),before];rfl
  · rw [kept 2 (by decide),before];rfl
  · rw [kept 3 (by decide),before];rfl
  · simp [ready,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  · rw [kept 5 (by decide),before];rfl
  · rw [kept 14 (by decide),before];rfl
  · rw [kept 15 (by decide),before];rfl
  · rw [kept 16 (by decide),before];rfl

theorem direct (blocked : CompilerFrameContext.ActualFrame) (valid : 4 < blocked.locals.size)
    (all : CopyHelperCleanup.AllImmediate blocked) : CopyHelperCleanup.AllImmediate (ready blocked valid) :=
  LocalDirectness.written_at {blocked with location := .mir ⟨6,0⟩} 4 CopyHelperUnit.layout .uninit valid ⟨7,0⟩ all

end DuplicatePrefix.CopyRootCurrentReadyFacts

#print axioms DuplicatePrefix.CopyRootCurrentReadyFacts.ready_slots
#print axioms DuplicatePrefix.CopyRootCurrentReadyFacts.direct

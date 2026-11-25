import Copy
import GeneratedCopyRows
import Miri.Verification.CopyInitialWP

namespace PointerObservation.Copy

open Miri.ABI Miri.Input Miri.TreeBorrows Miri.Interpreter Miri.Verification Miri.Memory Miri.MIR Fixture

/-- Expected post-copy state for this one-allocation fixture. -/
def postCopyTree (source : UInt8) (stale : Bool) : Option (Config × State) := do
  let (config, before) ← (scenario source source stale).toOption
  let entry ← (before.machine.memory.live.get? allocId).map ULift.up
  let entry := entry.down
  let tags ← (before.machine.borrowTracker.map fun t => ULift.up t.global.protectedTags)
  let tree := entry.allocation.extra
  let read := tree.performBorrowAccessRange (.concrete BorTag.one) (Size.ofBytes 0)
    (Size.ofBytes 1) .Read tags.down .VisitChildrenOfAccessed
  let written := read.tree.performBorrowAccessRange (.concrete BorTag.one) (Size.ofBytes 1)
    (Size.ofBytes 1) .Write tags.down .VisitChildrenOfAccessed
  let original := before.machine.memory
  let live := original.live.insert allocId {entry with allocation := entry.allocation.setExtra written.tree}
  let memory := {original with live}
  let state := {before with machine := {before.machine with memory}}
  return (config, (Step.finishStatement 0 (state, .ok ())).1)

/-- Frame at the observer load, after caching the unit layout and ending
storage for the intrinsic's three temporaries. -/
def postCopyLoadEntry (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
    Option (Config × State) := do
  let (config, entry) ← postCopyTree source stale
  let frame ← entry.stack.currentFrame?.map ULift.up
  let cached ← (frame.down.getOrCacheLocalLayout 4 layout4).toOption.map ULift.up
  let frame ← (cached.down.1.replaceLocalValue 6 .dead).toOption.map ULift.up
  let frame ← (frame.down.replaceLocalValue 5 .dead).toOption.map ULift.up
  let frame ← (frame.down.replaceLocalValue 4 .dead).toOption.map ULift.up
  let frame := {frame.down with location := .mir ⟨0, 10⟩}
  return (config, {entry with stack := ⟨#[frame]⟩})

set_option maxHeartbeats 300000
set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

theorem postCopyTree_bytes (source : UInt8) (stale : Bool) :
    (postCopyTree source stale).bind (fun after => bytesAt 1 after.2) =
      some (.ok #[source]) := by
  cbv

theorem postCopyTree_selected (source : UInt8) (stale : Bool) :
    (postCopyTree source stale).bind (fun after => BodyCFG.selected after.2) =
      some (⟨0, 6⟩, mir_0_bb0_6) := by
  cbv

/-- The post-copy program counter and statement agree with the first
row of the emitted suffix. -/
theorem postCopyTree_selected_generated (source : UInt8) (stale : Bool) :
    (postCopyTree source stale).bind (fun after => BodyCFG.selected after.2) =
      (postCopyTree source stale).bind (fun (config, _) =>
        ((GeneratedBodySafety.window_0_bb0_5 config limits).drop 1).head?.map
          (fun row => (row.location.pc, row.reduced.node))) := by
  have generated (config : Config) :
      ((GeneratedBodySafety.window_0_bb0_5 config limits).drop 1).head?.map
        (fun row => (row.location.pc, row.reduced.node)) =
        some (⟨0, 6⟩, mir_0_bb0_6) := rfl
  have selected := postCopyTree_selected source stale
  cases next : postCopyTree source stale with
  | none => simp [next] at selected
  | some pair =>
    obtain ⟨config, entry⟩ := pair
    simpa only [next, Option.bind_some, generated] using selected

section

set_option maxHeartbeats 3000000
attribute [local cbv_opaque] Allocation.readScalar MemoryObservationWP.scalarFromImage
  Scalar.toUInt8 Scalar.fromScalarInt ScalarInt.ofUInt8
private theorem scalarFromImage_one (layout : TargetDataLayout) (start : UInt64)
    (byte : UInt8) (provenance : ProvenanceMap Provenance) :
    MemoryObservationWP.scalarFromImage layout ⟨⟨start⟩, ⟨1⟩⟩ false
      (.ok #[byte]) (.ok (.ok ())) provenance = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 byte)) :=
  CopyInitialWP.scalarFromImage_byte layout ⟨start⟩ byte provenance

attribute [local cbv_eval] MemoryObservationWP.readScalar_eq_image
  scalarFromImage_one CopyInitialWP.toUInt8_byte

/-- The typed observer reads the copied byte with the root tag. A stale child
reports the precise load failure and retains the copied byte. -/
theorem postCopyLoad_readRaw (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let ptr := pointer (if stale then child else BorTag.one) 1
        let op : OpTy Provenance := ⟨.indirect ⟨ptr.withOptionalProvenance, .none, none⟩, layout⟩
        RvalueWP.actionPre (PlaceMachine.readRaw config.access op)
          (fun value _ => stale = false ∧ match value with
            | .immediate immediate => immediate.value = .scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 source))
            | .place _ => False)
          (fun error after => stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source])) entry := by
  cases stale <;>
    cbv

/-- The immediate write to the return local preserves the symbolic byte. -/
theorem postCopyLoad_write (source : UInt8) (layout4 : LocalLayout)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) :
    match postCopyLoadEntry source false layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let checked := ExecutionMachine.withValidation config limits
        let dest : RuntimePlace Provenance := ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 1), layout⟩
        let value : Immediate Provenance := .scalar (.fromScalarInt (ScalarInt.ofUInt8 source))
        let entry := {entry with machine := {entry.machine with memory}}
        PlaceReadWriteWP.writeNoValidatePre (ExecutionMachine.projectionHooks checked).place
          () value dest (fun _ after => scalarAt after 0 = some source) (fun _ _ => False) entry := by
  cbv

end

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``postCopyTree_bytes, ``postCopyTree_selected, ``postCopyTree_selected_generated,
      ``postCopyLoad_readRaw, ``postCopyLoad_write] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms postCopyTree_bytes
#print axioms postCopyTree_selected
#print axioms postCopyTree_selected_generated
#print axioms postCopyLoad_readRaw
#print axioms postCopyLoad_write

end PointerObservation.Copy

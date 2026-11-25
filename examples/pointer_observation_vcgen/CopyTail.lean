import Copy
import GeneratedCopyRows

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

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``postCopyTree_bytes, ``postCopyTree_selected, ``postCopyTree_selected_generated] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms postCopyTree_bytes
#print axioms postCopyTree_selected
#print axioms postCopyTree_selected_generated

end PointerObservation.Copy

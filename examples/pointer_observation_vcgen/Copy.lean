import Miri.Frontend.ImportBodyVC
import pointer_observation_vcgen.Fixture

namespace PointerObservation.Copy

open Miri.ABI Miri.Frontend Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Verification
open PointerObservation.Fixture

set_option maxHeartbeats 10000000
set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

import_body_vc_mir "copy.mir.json" 0 as input

def scenario (source destination : UInt8) (stale : Bool) :
    Except String (Config × State) := do
  let (config, prepared, program) ← configure input 0
  let prepared := prepared.down
  let program := program.down
  let byteLayout ← layoutOfLocal prepared program 0
  let sourceLayout ← layoutOfLocal prepared program 1
  let destinationLayout ← layoutOfLocal prepared program 2
  let image ← ((Allocation.fromBytes (Prov := Provenance) #[source, destination] Align.ONE .Mut).map ULift.up).mapError reprStr
  let tree := BorrowTree.new BorTag.one (Size.ofBytes 2)
  let inserted := tree.newChild (Size.ofBytes 1) (.concrete BorTag.one) child
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 1) ⟨.Unique, true, .None⟩)
    (.ReservedFrz false) false
  if let .error error := inserted.outcome then throw (reprStr error)
  let machine ← initialMachine prepared image.down inserted.tree
  let scalar := pointerImmediate prepared
  let locals := #[localImmediate .uninit (some byteLayout.down),
    localImmediate (scalar BorTag.one 0) (some sourceLayout.down),
    localImmediate (scalar BorTag.one 1) (some destinationLayout.down),
    localImmediate (scalar (if stale then child else BorTag.one) 1) (some sourceLayout.down),
    localImmediate .uninit,
    localImmediate (scalar BorTag.one 0) (some sourceLayout.down),
    localImmediate (scalar BorTag.one 1) (some destinationLayout.down)]
  let frame := {frameAt prepared program byteLayout.down 5 with locals}
  return (config, ⟨⟨#[frame]⟩, machine.down⟩)

def rows := [mir_0_bb0_5, mir_0_bb0_6, mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9, mir_0_bb0_10]

def disabledLoad : StepError :=
  PlaceMachine.treeError false
    (.AccessFailure ⟨1, 2⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)))


/-- The successful observer reads the source byte. A stale observer reaches
the load with the changed destination and fails with the exact Tree Borrows UB. -/
def required (source destination : UInt8) (stale : Bool) : Prop :=
  match scenario source destination stale with
  | .error _ => False
  | .ok (config, entry) =>
    prefixPre config
      (fun after => stale = false ∧ scalarAt after 0 = some source)
      (fun error after => stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source]))
      5 rows entry

/-- Check the value and error postconditions on the executable selected prefix. -/
def checked (source destination : UInt8) (stale : Bool) : Bool :=
  match scenario source destination stale with
  | .error _ => false
  | .ok (config, entry) =>
    match executePrefix config 5 rows entry with
    | none => false
    | some (after, .ok ()) => decide (stale = false ∧ scalarAt after 0 = some source)
    | some (after, .error error) =>
      decide (stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source]))

theorem required_iff_checked (source destination : UInt8) (stale : Bool) :
    required source destination stale ↔ checked source destination stale = true := by
  unfold required checked
  cases launched : scenario source destination stale with
  | error _ => simp
  | ok entered =>
    obtain ⟨config, entry⟩ := entered
    dsimp only
    rw [prefixPre_iff_execute]
    cases observation : executePrefix config 5 rows entry with
    | none => simp
    | some result =>
      obtain ⟨after, outcome⟩ := result
      cases outcome with
      | error _ => simp [InstructionWP.resultPre]
      | ok value => cases value; simp [InstructionWP.resultPre]

#eval show IO Unit from do
  unless checked 73 13 false do throw (IO.userError "copy observer returned an unexpected value")
  unless checked 73 13 true do throw (IO.userError "copy stale observer did not yield the expected UB and bytes")
  unless checked 9 255 false do throw (IO.userError "copy observer did not follow the source byte")

open Lean Elab Command in
run_cmd liftTermElabM do
  for dependency in (← collectAxioms ``required_iff_checked) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "copy VC depends on unapproved axiom {dependency}"

#print axioms required_iff_checked

end PointerObservation.Copy

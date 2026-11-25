import Miri.Frontend.ImportBodyVC
import pointer_observation_vcgen.Fixture

/-! Imported MIR references and raw pointers carried through the first
reading or writing instruction, from a one-byte allocation. -/
namespace PointerObservation

open Miri.ABI Miri.DataStructures Miri.Frontend Miri.Interpreter Miri.Memory
open Miri.TreeBorrows Miri.Verification Fixture

set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

import_body_vc_mir "pointers.mir.json" 0 as input

def scenario (root : Nat) (initial : UInt8) (restricted : Bool) :
    Except String (Config × State) := do
  let (config, prepared, program) ← configure input root
  let prepared := prepared.down
  let program := program.down
  let output ← layoutOfLocal prepared program 0
  let argument ← layoutOfLocal prepared program 1
  let image ← ((Allocation.fromBytes (Prov := Provenance) #[initial] Align.ONE .Mut).map ULift.up).mapError reprStr
  let tree := BorrowTree.new BorTag.one (Size.ofBytes 1)
  let tree : ULift.{1} BorrowTree ← if restricted then do
    let inserted := tree.newChild Size.ZERO (.concrete BorTag.one) child
      (DedupRangeMap.new (Size.ofBytes 1) ⟨.Frozen, true, .Read⟩) .Frozen false
    let _ ← (inserted.outcome.map ULift.up).mapError reprStr
    pure (ULift.up inserted.tree)
  else pure (ULift.up tree)
  let machine ← initialMachine prepared image.down tree.down
  let frame := frameAt prepared program output.down 0
  let tag := if restricted then child else BorTag.one
  let locals := frame.locals.set! 0 (localImmediate .uninit (some output.down))
    |>.set! 1 (localImmediate (pointerImmediate prepared tag 0) (some argument.down))
  pure (config, ⟨⟨#[{frame with locals}]⟩, machine.down⟩)

private def mutableRows := [
  mir_0_bb0_0, mir_0_bb0_1, mir_0_bb0_2, mir_0_bb0_3, mir_0_bb0_4, mir_0_bb0_5]

private def rawRows := [mir_1_bb0_0, mir_1_bb0_1, mir_1_bb0_2, mir_1_bb0_3]
private def sharedRows := [mir_2_bb0_0, mir_2_bb0_1, mir_2_bb0_2]

private def tagAt (state : State) (localId : Nat) : Option UInt64 := do
  let frame ← state.stack.currentFrame?
  let .immediate (.scalar scalar) ← (frame.getLocalOperand localId).toOption | none
  let pointer ← (scalar.toPointer ⟨.little, .w64⟩).toOption
  let some (.concrete allocation tag) := pointer.provenance | none
  if allocation = allocId then some tag.value else none

inductive Observation
  | sharedRead
  | mutableWrite
  | rawWrite
  | frozenWrite

def selectedRows : Observation → Nat × Bool × List BodyCFG.Node
  | .sharedRead => (2, false, sharedRows)
  | .mutableWrite => (0, false, mutableRows)
  | .rawWrite => (1, false, rawRows)
  | .frozenWrite => (1, true, rawRows)

def observed (observation : Observation) (initial : UInt8)
    (after : State) (result : Except StepError Unit) : Bool :=
  match observation, result with
  | .sharedRead, .ok () => scalarAt after 0 == some initial && tagAt after 2 == some 3
  | .mutableWrite, .ok () =>
    decide (bytesAt 0 after = some (.ok #[73])) && tagAt after 2 == some 4
  | .rawWrite, .ok () =>
    decide (bytesAt 0 after = some (.ok #[73])) && tagAt after 2 == some 1
  | .frozenWrite, .error error =>
    decide (error = PlaceMachine.treeError true
      (.AccessFailure ⟨0, 1⟩ (.TransitionError 1 (.ChildAccessForbidden .Frozen)))) &&
      decide (bytesAt 0 after = some (.ok #[initial])) && tagAt after 2 == some 2
  | _, _ => false

/-- The observation of the selected MIR window from the prepared allocation.
The success and error observations both read the state left by the interpreter. -/
def required (observation : Observation) (initial : UInt8) : Prop :=
  let (root, restricted, rows) := selectedRows observation
  match scenario root initial restricted with
  | .error _ => False
  | .ok (config, before) =>
    prefixPre config (fun after => observed observation initial after (.ok ()) = true)
      (fun error after => observed observation initial after (.error error) = true) 0 rows before

def checked (observation : Observation) (initial : UInt8) : Bool :=
  let (root, restricted, rows) := selectedRows observation
  match scenario root initial restricted with
  | .error _ => false
  | .ok (config, before) =>
    match executePrefix config 0 rows before with
    | none => false
    | some (after, result) => observed observation initial after result

/-- The executable observation and the bounded VC have the same predicate
for every initial byte. The sample runs below evaluate the checker. -/
theorem required_iff_checked (observation : Observation) (initial : UInt8) :
    required observation initial ↔ checked observation initial = true := by
  rcases shape : selectedRows observation with ⟨root, restricted, rows⟩
  simp only [required, checked, shape]
  cases launch : scenario root initial restricted with
  | error => simp
  | ok entered =>
    obtain ⟨config, before⟩ := entered
    simp only
    rw [prefixPre_iff_execute]
    cases ran : executePrefix config 0 rows before with
    | none => simp
    | some result =>
      obtain ⟨after, outcome⟩ := result
      cases outcome with
      | error => rfl
      | ok value => cases value; rfl

#eval show IO Unit from do
  unless checked .sharedRead 13 && checked .sharedRead 255 do
    throw (IO.userError "shared reference load did not observe the byte through its fresh tag")
  unless checked .mutableWrite 13 do
    throw (IO.userError "mutable reference store did not update the byte through its fresh tag")
  unless checked .rawWrite 13 do
    throw (IO.userError "raw pointer store did not update the byte through the original tag")
  unless checked .frozenWrite 13 do
    throw (IO.userError "frozen tag did not produce the expected UB and retain the original byte")

open Lean Elab Command in
run_cmd liftTermElabM do
  for dependency in (← collectAxioms ``required_iff_checked) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "pointer observation VC depends on unapproved axiom {dependency}"

#print axioms required_iff_checked

end PointerObservation

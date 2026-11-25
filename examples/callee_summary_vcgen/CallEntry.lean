import Generated
import pointer_observation_vcgen.Fixture

/-! The prepared call-site state of the exported `miri_start` caller. -/

namespace CalleeSummaryExample

open Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory Miri.TreeBorrows Miri.Verification
open PointerObservation.Fixture

def callBorrow : BorTag := ⟨3, by decide⟩
def calleeBorrow : BorTag := ⟨4, by decide⟩

/-- Seed the caller immediately before its imported call. The two live
references correspond to the borrow of the stack byte and its two-phase
reborrow in the preceding MIR. -/
def atBorrowedCall : Except String (Config × ULift.{1} BodyVCGen.LoadedProgram × State) := do
  let (config, prepared, program) ← configure GeneratedBodySafety.input 0
  let compiled := prepared.down
  let loaded := program.down
  let output ← layoutOfLocal compiled loaded 0
  let byte ← layoutOfLocal compiled loaded 3
  let argument ← layoutOfLocal compiled loaded 5
  let allocation ← ((Allocation.fromBytes (Prov := Provenance) #[1] Align.ONE .Mut).map ULift.up).mapError reprStr
  let size := Size.ofBytes 1
  let tree := BorrowTree.new BorTag.one size
  let childLocation : Tree.LocationState := ⟨.ReservedFrz false, true, .Read⟩
  let borrow := tree.newChild Size.ZERO (.concrete BorTag.one) child
    (Miri.DataStructures.DedupRangeMap.new size childLocation) (.ReservedFrz false) false
  if let .error error := borrow.outcome then throw (reprStr error)
  let reborrow := borrow.tree.newChild Size.ZERO (.concrete child) callBorrow
    (Miri.DataStructures.DedupRangeMap.new size ⟨.ReservedFrz false, true, .Read⟩)
    (.ReservedFrz false) false
  if let .error error := reborrow.outcome then throw (reprStr error)
  let machine ← initialMachine compiled allocation.down reborrow.tree
  let base := machine.down
  let user := base.user
  let payload := user.payload
  let stored := payload.payload
  let stored := {stored with identitySupply := ⟨2⟩}
  let borrowTracker := base.borrowTracker.map fun tracker =>
    {tracker with global := {tracker.global with nextPointerTag := calleeBorrow}}
  let machine := {base with
    user := {user with payload := {payload with payload := stored}}, borrowTracker}
  let frame := frameAt compiled loaded output.down 7
  let slot : MemPlace Provenance := ⟨(pointer BorTag.one 0).withOptionalProvenance, .none, none⟩
  let reference (tag : BorTag) :=
    localImmediate (pointerImmediate compiled tag 0) (some argument.down)
  let locals := frame.locals.set! 0 (localImmediate .uninit (some output.down))
    |>.set! 3 ⟨.live (.indirect slot), some byte.down⟩
    |>.set! 4 (localImmediate .uninit (some byte.down))
    |>.set! 5 (reference callBorrow)
    |>.set! 6 (reference child)
  pure (config, program, ⟨⟨#[{frame with locals}]⟩, machine⟩)

def argumentHasStrongProtector (after : State) : Bool := Id.run do
  let some frame := after.stack.currentFrame? | return false
  let some active := frame.extra.borrowTracker | return false
  let some tracker := after.machine.borrowTracker | return false
  let some (allocation, called) := active.protectedTags[0]? | return false
  return decide (after.stack.frames.size = 2 ∧
    frame.location = .mir ⟨0, 0⟩ ∧ frame.bodyIdentity.index = 1 ∧
    frame.localsIdentity = .ofAllocationToken 2 ∧
    allocation = allocId ∧ called = calleeBorrow ∧
    tracker.global.protectedTags.get called = some .StrongProtector)

section

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 180000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail Std.HashMap.getElem?_emptyWithCapacity Std.HashMap.getElem?_empty
attribute [local cbv_opaque] Std.HashMap.emptyWithCapacity Std.HashMap.insert

theorem emittedCallMatchesRoot :
    (GeneratedBodySafety.loaded.toOption.bind fun program =>
      program.root.body.basicBlocks[0]?.map fun block =>
        (block.statements.size, BodyCFG.Node.terminator block.terminator)) =
      some (7, GeneratedBodySafety.mir_0_bb0_7) := by
  cbv

end

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``atBorrowedCall, ``argumentHasStrongProtector, ``emittedCallMatchesRoot] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

end CalleeSummaryExample

import CallEntry

/-! Physical writeback and return observations for the exported `update` body. -/
namespace CalleeSummaryExample

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.MIR
open PointerObservation.Fixture GeneratedBodySafety

set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-- Freeze the destination, literal width and retag flag at the emitted store. -/
theorem updateStoreNode :
    ∃ span ty, mir_1_bb0_0 = .statement (.Assign ⟨1, #[.Deref]⟩
      (.Use (.Constant ⟨span, none, .Val (.Scalar (.Int 42 1)) ty⟩) .Yes)) :=
  ⟨_, _, rfl⟩

/-- The protected write retains byte 42 through the tree's protector-end access. -/
theorem protectedWriteReleases (initial : UInt8) : (show Except String (Array UInt8) from do
    let size := Size.ofBytes 1
    let tree := BorrowTree.new BorTag.one size
    let parent := tree.newChild Size.ZERO (.concrete BorTag.one) child
      (Miri.DataStructures.DedupRangeMap.new size ⟨.ReservedFrz false, true, .Read⟩) (.ReservedFrz false) false
    let arg := parent.tree.newChild Size.ZERO (.concrete child) callBorrow
      (Miri.DataStructures.DedupRangeMap.new size ⟨.ReservedFrz false, true, .Read⟩) (.ReservedFrz false) false
    let tags := ({} : ProtectedTags).insert calleeBorrow .StrongProtector
    let read := arg.tree.performBorrowAccessRange (.concrete callBorrow) Size.ZERO size .Read
      tags .VisitChildrenOfAccessed
    let entered := read.tree.newChild Size.ZERO (.concrete callBorrow) calleeBorrow
      (Miri.DataStructures.DedupRangeMap.new size ⟨.ReservedFrz false, true, .None⟩) (.ReservedFrz false) true
    let write := entered.tree.performBorrowAccessRange (.concrete calleeBorrow) Size.ZERO size .Write
      tags .VisitChildrenOfAccessed
    unless parent.outcome.isOk && arg.outcome.isOk && read.status == .Completed &&
      entered.outcome.isOk && write.status == .Completed do
      throw "protected access failed"
    let allocation ← (Allocation.fromBytes (Prov := Provenance) #[initial] Align.ONE .Mut).mapError reprStr
    let target := allocation.withExtra write.tree
    let range := allocRange Size.ZERO size
    let layout : TargetDataLayout := ⟨.little, .w64⟩
    let scalar := Scalar.fromScalarInt (ScalarInt.ofUInt8 42)
    match Allocation.writeScalar layout range scalar target with
    | .error error _ => throw (reprStr error)
    | .ok () stored =>
      let released := stored.extra.releaseProtector calleeBorrow tags
      unless released.status == .Released do
        throw "protector release failed"
      ((stored.setExtra released.tree).getBytesUnchecked range).mapError reprStr) = .ok #[42] := by
  cbv

/-- Run the emitted callee window from the actual successor of the caller's
call step and check the caller state reached after Return. -/
def observeUpdateReturn : Except String (Config × State) :=
  match atBorrowedCall with
  | .error error => .error error
  | .ok (config, _, caller) => do
    let (entered, callOutcome) := ExecutionMachine.step config limits () caller
    let more ← (callOutcome.map ULift.up).mapError reprStr
    unless more.down && argumentHasStrongProtector entered do
      throw "the call did not enter update with its strong protector"
    let some (returned, result) := executePrefix config 0
      [mir_1_bb0_0, mir_1_bb0_1, mir_1_bb0_2] entered | throw "update prefix mismatch"
    if let .error error := result then throw (reprStr error)
    let tracker := returned.machine.borrowTracker.map (fun tracker =>
      tracker.global.protectedTags.get calleeBorrow)
    unless decide (returned.stack.frames.size = 1 ∧
        returned.stack.currentFrame?.map (·.location) = some (.mir ⟨1, 0⟩) ∧
        returned.stack.currentFrame?.map (·.localsIdentity) =
          caller.stack.currentFrame?.map (·.localsIdentity) ∧
        scalarAt returned 4 = some 7 ∧ bytesAt 0 returned = some (.ok #[42]) ∧ tracker = some none) do
      throw "update did not resume its caller with byte 42, result 7 and the protector released"
    return (config, returned)

def checkUpdateReturn : Except String Unit :=
  match observeUpdateReturn with
  | .ok _ => .ok ()
  | .error error => .error error

set_option compiler.extract_closed false in
#eval show IO Unit from match checkUpdateReturn with
  | .ok () => pure ()
  | .error error => throw (IO.userError error)

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``updateStoreNode, ``protectedWriteReleases] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms updateStoreNode
#print axioms protectedWriteReleases

end CalleeSummaryExample

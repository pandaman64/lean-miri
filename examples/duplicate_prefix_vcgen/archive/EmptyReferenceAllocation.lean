import duplicate_prefix.EmptyReferenceSteps
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.EmptyReferenceAllocation
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open EmptyReferenceSteps

def allocatedTracker (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.BorrowState :=
  {tracker with global := {tracker.global with nextPointerTag := TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh}}
def allocatedMachine {K U : Type} (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.MachineState K U :=
  {machine with borrowTracker := some (allocatedTracker tracker fresh)}

end DuplicatePrefix.EmptyReferenceAllocation

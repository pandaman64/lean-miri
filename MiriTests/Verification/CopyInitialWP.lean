import Miri.Verification.CopyInitialWP

/-! Symbolic cases for allocation identity and partial copy observations. -/
namespace MiriTests.Verification.CopyInitialWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Verification Std.WP

/-- With all IDs symbolic, the final destination wins, the retained source
is selected at the source ID, and a distinct observer uses its existing entry. -/
theorem arbitrary_observer_id
    (memory : MemoryState Provenance BorrowTree Unit) (source destination observer : AllocId)
    (read written : LocalAllocation Provenance BorrowTree Unit) :
    ((memory.live.insert source read).insert destination written)[observer]? =
      if observer = destination then some written
      else if observer = source then some read else memory.live[observer]? := by
  miri_copy_initial_wp

/-- An observing byte may overlap any part of the copied range. The copied
source snapshot and the original destination image remain symbolic. -/
theorem arbitrary_observer_byte (initial copied : Array UInt8) (start finish observed : Nat)
    (ordered : start ≤ finish) (bound : finish ≤ initial.size)
    (width : copied.size = finish - start) :
    (initial.extract 0 start ++ copied ++ initial.extract finish initial.size)[observed]? =
      if start ≤ observed ∧ observed < finish then copied[observed - start]? else initial[observed]? := by
  miri_copy_initial_wp

/-- After a real commit, a bare observer lookup has distinct same-ID and
different-ID continuations, even when physical copying returned an error. -/
theorem arbitrary_commit_result (config : PlaceMachine.AccessConfig Unit Unit)
    (before : MachineHooks.State Unit Unit) (destination observer : AllocId)
    (original : LocalAllocation Provenance BorrowTree Unit) (copied : Allocation Provenance BorrowTree)
    (failure : AllocError)
    (live : before.machine.memory.live[destination]? = some original) :
    CopyMemoryWP.commitPre config destination (.error failure copied) (fun _ _ => False)
      (fun error after =>
        error = config.memoryError (.allocation failure) ∧
        after.machine.memory.live[observer]? =
          if observer = destination then some {original with allocation := copied}
          else before.machine.memory.live[observer]?) before := by
  miri_copy_initial_wp

/-- The exact copy-then-load program rejects a failing source pointer with
the machine returned by resolution, before any byte or tree check. -/
theorem rejected_source_pointer (config : PlaceMachine.AccessConfig Unit Unit)
    (addresses : Unit → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (source destination : Pointer (Option Provenance)) (size : Size)
    (operand : OpTy Provenance) (before : MachineHooks.State Unit Unit)
    (result : MemoryStateHookResult Provenance BorrowTree Unit
      (PlaceMachine.AccessState Unit Unit) (Option (AllocId × Size × ProvenanceExtra)))
    (message : String)
    (resolution : (MemoryCopyMachine.genericHooks config addresses arithmetic).pointerAccess
      before.machine.memory ⟨before.machine, none⟩ source size = result)
    (failed : result.outcome = .error message)
    (post : RvalueImmTy Provenance → MachineHooks.State Unit Unit → Prop)
    (onError : StepError → MachineHooks.State Unit Unit → Prop) :
    wp (do
      GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source destination size 1 true
      PlaceMachine.readImmediate config operand) post onError before ↔
      onError (result.state.pendingError.getD (.callback message))
        {before with machine := {result.state.machine with memory := result.memory}} := by
  miri_copy_initial_wp

#print axioms arbitrary_observer_id
#print axioms arbitrary_observer_byte
#print axioms arbitrary_commit_result
#print axioms rejected_source_pointer

end MiriTests.Verification.CopyInitialWP

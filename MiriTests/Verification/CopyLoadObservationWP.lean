import Miri.Verification.CopyLoadObservationWP

namespace MiriTests.Verification.CopyLoadObservationWP

open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Verification
open Miri.Verification.CopyLoadObservationWP

variable {K U : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "Alloc" => Allocation Provenance BorrowTree
local notation "Entry" => LocalAllocation Provenance BorrowTree K
local notation "Memory" => MemoryState Provenance BorrowTree K
local notation "Hooks" => PlaceMachine.AccessState K U

/-- The normalizer exposes the identity test without needing either alias
outcome and preserves the committed memory passed to the synchronization. -/
example (config : Config) (memory : Memory) (written observed : AllocId) (entry other : Entry)
    (hooks : Hooks) (present : memory.live[observed]? = some other) :
    let committed := {memory with live := memory.live.insert written entry}
    MemoryLifecycle.getAllocRaw committed hooks observed config.globalKind config.globalHooks =
      ⟨committed, config.globalHooks.synchronizeMemory committed hooks,
        .ok (if observed = written then entry.allocation else other.allocation)⟩ := by
  by_cases alias : observed = written <;>
    simp only [miri_initial_wp, present, alias, ↓reduceIte] <;> rfl

/-- The exact physical-copy failure branch retains its partial image, and
a missing live key overrides the copy error at the pre-commit state. -/
example (config : Config) (before : State) (id : AllocId) (updated : Alloc)
    (failure : AllocError) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    CopyMemoryWP.commitPre config id (.error failure updated) post onError before =
      (match before.machine.memory.live[id]? with
      | none => onError (config.memoryError (.memoryUpdate (.unavailable id))) before
      | some entry =>
        let memory := {before.machine.memory with live :=
          (before.machine.memory.live.insert id {entry with allocation := updated})}
        onError (config.memoryError (.allocation failure)) {before with machine := {before.machine with memory}}) := by
  simp only [miri_initial_wp]
  cases before.machine.memory.live[id]? <;> rfl

end MiriTests.Verification.CopyLoadObservationWP

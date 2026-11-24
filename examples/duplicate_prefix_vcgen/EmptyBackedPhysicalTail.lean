import PhysicalReturnOfLedger
import PhysicalCarrierDistinct
import CanonicalCallRelease
import duplicate_prefix.RootPhysicalCarrierTransport

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open RootZeroShallowReturn CanonicalConfigFacts

set_option maxRecDepth 65536
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame
local notation "Entry" => LocalAllocation Provenance BorrowTree MiriMemoryKind

/-- A concrete empty source has a dormant protector to release. The physical
Bool goes to its own retained allocation and keeps the original output window. -/
theorem emptyBackedPhysicalTail
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (validation : options.limits.validation = fuel+1)
    (debugOff : options.place.debugAssertions = false)
    (entry result : Frame) (initial machine : MachineState)
    (pointer : Pointer (Option Provenance)) (id : AllocId) (tag : BorTag)
    (concrete : pointer.provenance = some (.concrete id tag))
    (initialTracker tracker : MachineHooks.BorrowState)
    (initialTracked : initial.borrowTracker = some initialTracker) (tracked : machine.borrowTracker = some tracker)
    (sameMask : tracker.global.protectedTags = initialTracker.global.protectedTags)
    (source : Entry) (present : machine.memory.live[id]? = some source)
    (holder : UniIndex) (node : TreeNode)
    (holderKey : source.allocation.extra.indexOfTag tag = some holder)
    (holderNode : source.allocation.extra.nodeAt holder = some node)
    (hidden : node.isExposed = false)
    (dormant : ∀ pos (valid : pos < source.allocation.extra.locations.entries.size),
      source.allocation.extra.locations.entries[pos].data.perms.get holder = none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (destination : PhysicalBoolDestination (Storage.withCurrent #[] entry initial) entry pointer 0)
    (disjoint : ∀ place key accessTag, entry.returnPlace = .memory place →
      place.mplace.ptr.provenance = some (.concrete key accessTag) → key ≠ id)
    (headroom : Nat) (profile : AllocationProfile (Storage.withCurrent #[] entry initial) entry headroom)
    (place : result.returnPlace = entry.returnPlace)
    (ledger : result.extra.borrowTracker = entry.extra.borrowTracker)
    (addresses : machine.user.addresses = initial.user.addresses)
    (extras : machine.user.payload.payload.user.runtime.extras = initial.user.payload.payload.user.runtime.extras)
    (unrelated : ∀ key, key ≠ id → machine.memory.live[key]? = initial.memory.live[key]?)
    (body : result.body = RootBody.reflected.body.body) (location : result.location = .mir ⟨10,0⟩)
    (slot : result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩)
    (noLocalClocks : result.extra.dataRace = none)
    (continues : result.returnContinuation = .stop true)
    (immediate : ZeroImmediateFacts.AllImmediate result) (noVarargs : result.vaList = #[])
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (raceOff : machine.dataRace = none)
    (backendOff : machine.user.payload.payload.user.backend = .none) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ final, SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] result machine) final ∧
      final.stack.frames = #[] ∧ ExecutionMachine.step cfg limits () final = (final,.ok false) := by
  let initialState := Storage.withCurrent #[] entry initial
  let currentState := Storage.withCurrent #[] result machine
  have saved := RootPhysicalCarrierTransport.transportDistinct initialState currentState entry result pointer 0
    id disjoint initialTracker tracker initialTracked tracked sameMask place ledger addresses unrelated destination
  have backing := RootPhysicalCarrierTransport.backing initialState currentState entry headroom profile id unrelated extras
  apply returnPhysicalOfLedger options limits remaining span fuel validation debugOff result machine pointer 0
    tracker tracked thread active saved
    (fun target key accessTag row atResult provenance live =>
      backing key row (disjoint target key accessTag (place.symm.trans atResult) provenance) live)
    ?_ body location false slot noLocalClocks continues immediate noVarargs ghost shallow unchecked gc fixed raceOff backendOff
  intro owned slotId slotTag slotEntry afterSlot _ rows slotLive outputReleased
  let final := StackPopRelease.commitTree machine.memory slotId slotEntry afterSlot
  have tail : StackPopRelease.Plan tracker.global.protectedTags [(slotId,slotTag)] machine.memory final :=
    .live slotId slotTag slotEntry afterSlot [] machine.memory final slotLive outputReleased (.nil final)
  have release := prependDormantRelease machine.memory final present dormant holderKey holderNode hidden
    tracker.global.protectedTags [(slotId,slotTag)] tail
  refine ⟨final, ?_, StackPopRelease.lookup_commit_same machine.memory slotId slotEntry afterSlot⟩
  simpa [rows,argumentLedger,concrete] using release

#print axioms emptyBackedPhysicalTail
end DuplicatePrefix.CanonicalCallDomain

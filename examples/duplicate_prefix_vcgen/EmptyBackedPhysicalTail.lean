import PhysicalReturnOfLedger
import EmptyAliasPhysicalCarrier
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
Bool uses its retained output window, including one in the same allocation. -/
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
    (original : Entry) (originalLive : initial.memory.live[id]? = some original)
    (sameBytes : source = {original with allocation := original.allocation.setExtra source.allocation.extra})
    (fresh : List BorTag)
    (transfer : EmptySharedWriteFrame.Transfer original.allocation.extra source.allocation.extra fresh)
    (vacant : ∀ index, source.allocation.extra.nodeAt index = none →
      ∀ position (valid : position < source.allocation.extra.locations.entries.size),
        source.allocation.extra.locations.entries[position].data.perms.get index = none)
    (oldTags : ∀ index node, original.allocation.extra.nodeAt index = some node → node.tag ∉ fresh)
    (unheld : ∀ freshTag ∈ fresh, tracker.global.protectedTags.contains freshTag = false)
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
  have saved := RootPhysicalCarrierTransport.transportEmpty initialState currentState entry result pointer
    id original source originalLive present sameBytes fresh transfer vacant oldTags initialTracker tracker
    initialTracked tracked sameMask (by rw [← sameMask]; exact unheld) place ledger addresses unrelated destination
  apply returnPhysicalOfLedger options limits remaining span fuel validation debugOff result machine pointer 0
    tracker tracked thread active saved ?_ ?_ body location false slot noLocalClocks continues immediate noVarargs ghost shallow unchecked gc fixed raceOff backendOff
  · intro _ key _ row _ _ live
    obtain ⟨old, oldLive⟩ : ∃ old, initial.memory.live[key]? = some old := by
      by_cases eq : key = id
      · subst key
        exact ⟨original,originalLive⟩
      · exact ⟨row, (unrelated key eq).symm.trans live⟩
    obtain ⟨extra, found, weak, sync⟩ := profile.extras key
      (MemoryCopyBridge.live_any_of_present initial.memory key old oldLive)
    change initial.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) =
      some (key,extra) at found
    have backtrace := AllocationBacktrace.of_lookup found
    rw [extras, backtrace, found]
    congr 2
    cases extra with
    | mk buffer syncState stack =>
      change buffer = none at weak
      change syncState = #[] at sync
      subst buffer
      subst syncState
      rfl
  · intro owned slotId slotTag slotEntry afterSlot _ rows slotLive outputReleased
    let final := StackPopRelease.commitTree machine.memory slotId slotEntry afterSlot
    have tail : StackPopRelease.Plan tracker.global.protectedTags [(slotId,slotTag)] machine.memory final :=
      .live slotId slotTag slotEntry afterSlot [] machine.memory final slotLive outputReleased (.nil final)
    have release := prependDormantRelease machine.memory final present dormant holderKey holderNode hidden
      tracker.global.protectedTags [(slotId,slotTag)] tail
    refine ⟨final, ?_, StackPopRelease.lookup_commit_same machine.memory slotId slotEntry afterSlot⟩
    simpa [rows,argumentLedger,concrete] using release

#print axioms emptyBackedPhysicalTail
end DuplicatePrefix.CanonicalCallDomain

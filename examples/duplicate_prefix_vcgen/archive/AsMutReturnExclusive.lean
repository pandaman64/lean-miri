import duplicate_prefix.AsMutPtrReturn
import duplicate_prefix.RetagReleaseFootprint
import duplicate_prefix.ActiveStackReleaseExclusive

namespace DuplicatePrefix.AsMutReturnExclusive
open Miri Miri.ABI Miri.Concurrency Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures
open CanonicalConfigFacts PreparedArguments SourceDomain Miri.Verification

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem pop
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent (frames.push caller) frame machine) length)
    (region : ExclusiveRegion (Storage.withCurrent (frames.push caller) frame machine) length storage tag)
    (owned : FrameState) (ledger : frame.extra.borrowTracker = some owned)
    (one : owned.protectedTags = #[(storage.id,tag)])
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (node : TreeNode) (nodeFound : storage.entry.allocation.extra.nodeAt region.source = some node)
    (unexposed : node.isExposed = false)
    (materialized : RetagReleaseFootprint.MaterializedWithin storage.entry.allocation.extra region.source
      storage.relativeStart.bytes (storage.relativeStart.bytes + length))
    (vacant : RetagReleaseFootprint.VacantRows storage.entry.allocation.extra)
    (fits : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (thread : ThreadRecord) (relevance : Nat)
    (current : machine.threads.activeThread? = some thread)
    (cached : FrameRelevance.top ⟨(frames.push caller).push frame⟩ thread.topUserRelevantFrame = some relevance) :
    let cfg := PreparedContracts.actualConfig options () remaining span
    let hooks := TypedMachineBindings.retagHooks cfg.access cfg.retag
    ∃ popped : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      TypedMachineBindings.popRaw hooks (Storage.withCurrent (frames.push caller) frame machine) =
        .ok frame (Storage.withCurrent frames caller popped) ∧
      popped.user = machine.user ∧ popped.dataRace = machine.dataRace ∧
      popped.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      (∃ presentThread, popped.threads.activeThread? = some presentThread) ∧
      ∃ next : InitializedRegion (Storage.withCurrent frames caller popped) length,
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        ∃ right : ExclusiveRegion (Storage.withCurrent frames caller popped) length next tag,
          right.tracker.retagMode = region.tracker.retagMode := by
  intro cfg hooks
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, table, globals, choice, wired, _, _, ensure, sync⟩ := fields.retagConstruction
  have ensureEq : hooks.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals := by
    change cfg.retag.ensureTreeExtra = _
    dsimp only [cfg]
    rw [wired]
    exact ensure
  have same : globals.synchronizeMemory machine.memory ⟨machine, none⟩ = ⟨machine, none⟩ := by
    rw [sync]
  have gives := RetagReleaseRights.region_owned (Storage.withCurrent (frames.push caller) frame machine)
    length storage tag region fits
  have all := RetagReleaseFootprint.active_of_footprint storage.entry.allocation.extra
    region.tracker.global.protectedTags region.source storage.relativeStart.bytes
    (storage.relativeStart.bytes + length) region.coherent materialized vacant gives
  obtain ⟨state, stack, user, race, fixed, activeThread, right, exactWP⟩ :=
    RetagReleaseRights.popExclusive_with_frame .global globals hooks ensureEq (frames.push caller) frame machine
      length storage tag region same owned ledger one root roots node nodeFound unexposed all fits thread relevance current cached
  have afterState : Storage.withCurrent frames caller state.machine = state := by
    cases state with
    | mk source machine =>
      cases source with
      | mk actual =>
        change actual = frames.push caller at stack
        subst actual
        rfl
  have exactPop := (ProtectorReleaseWP.popRawPre_iff hooks
    (fun actual reached => actual = frame ∧ reached = state) (fun _ _ => False)
    (Storage.withCurrent (frames.push caller) frame machine)).mp
    ((exactWP _ _).mpr ⟨rfl,rfl⟩)
  have ran : TypedMachineBindings.popRaw hooks (Storage.withCurrent (frames.push caller) frame machine) =
      .ok frame state := by
    cases outcome : TypedMachineBindings.popRaw hooks (Storage.withCurrent (frames.push caller) frame machine) with
    | error error reached => simp [RvalueWP.actionPre,outcome] at exactPop
    | ok actual reached =>
      simp [RvalueWP.actionPre,outcome] at exactPop
      obtain ⟨rfl,rfl⟩ := exactPop
      rfl
  refine ⟨state.machine, ?_, user, race, fixed, activeThread, ?_⟩
  · rw [afterState]
    exact ran
  · rw [afterState]
    exact right

end DuplicatePrefix.AsMutReturnExclusive

#print axioms DuplicatePrefix.AsMutReturnExclusive.pop

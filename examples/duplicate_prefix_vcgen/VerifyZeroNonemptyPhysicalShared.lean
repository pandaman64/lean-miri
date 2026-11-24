import PhysicalReturnWithSharedSlice
import PreparedAliasCompatibility
import CanonicalAliasEntryFacts
import duplicate_prefix.ActiveStackReleaseExclusive

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Verification
open RootZeroShallowReturn SourceDomain ArchiveForestProjection GeneralRangeMapOrigins PreparedArguments

set_option maxRecDepth 65536
set_option maxHeartbeats 6500000
set_option backward.isDefEq.respectTransparency false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame

private theorem zeroTickFields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (machine : MachineState) :
    let after := RootZeroCompleteState.tick options remaining span machine
    after.memory = machine.memory ∧ after.borrowTracker = machine.borrowTracker ∧
      after.threads = machine.threads ∧ after.dataRace = machine.dataRace ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.ghost = machine.user.payload.ghost ∧
      after.user.payload.validation = machine.user.payload.validation ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  dsimp only
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


/-- The actual zero-count arm performs no slice access. Its ordered frame
release and physical output write support the same heap allocation. -/
theorem zeroCountNonemptyPhysicalShared
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (fuel : Nat) (validation : options.limits.validation = fuel+1)
    (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (length : UInt64)
    (positive : 0 < length)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer length 0 true)
    (compiler : InitialCompilerControl before frame)
    (physical : PhysicalBoolDestination before frame pointer length true)
    (stack : before.stack.frames = #[frame]) (continuation : frame.returnContinuation = .stop true) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let machine := before.machine
  have state : before = Storage.withCurrent #[] frame machine := withFrames stack
  have entry := zeroCountAliasEntry loaded admitted compiler
  have nonempty : length ≠ 0 := by
    intro empty
    rw [empty] at positive
    exact (UInt64.lt_irrefl _ positive)
  obtain ⟨storage,tag,base,region,_,concrete,address,cached,_,_,_,⟨node,found,hidden⟩,extent⟩ :=
    admitted.sliceProtector nonempty
  obtain ⟨root,roots⟩ := extent.root nonempty
  let tracker := region.tracker
  obtain ⟨old,recorded,mode⟩ := admitted.profile.mode
  have same : old = tracker := Option.some.inj (recorded.symm.trans region.tracked)
  subst old
  obtain ⟨result, trace, body, _, _, extra, savedPlace, continues, args, _, _, location, slot, immediate⟩ :=
    RootZeroCompletePrefix.reaches_return options limits remaining span compilerSourceComparator
      admitted.profile.debugOff fuel validation #[] frame machine
      entry.body entry.identity entry.callee entry.location entry.size entry.live0 entry.uncached0
      entry.dead3 entry.dead4 entry.dead5 entry.uncached4 entry.uncached5 entry.zero entry.cached2
      entry.noClocks entry.immediate tracker region.tracked mode entry.ghost entry.shallow
      admitted.profile.unchecked admitted.profile.noGc entry.fixed
  let first := RootZeroCompleteState.tick options remaining span machine
  let second := RootZeroCompleteState.tick options remaining span first
  have firstFields := zeroTickFields options remaining span machine
  have secondFields := zeroTickFields options remaining span first
  have heap := secondFields.1.trans firstFields.1
  have borrowed := secondFields.2.1.trans firstFields.2.1
  have threads := secondFields.2.2.1.trans firstFields.2.2.1
  have addresses := secondFields.2.2.2.2.1.trans firstFields.2.2.2.2.1
  have stockExtras := secondFields.2.2.2.2.2.2.2.2.trans firstFields.2.2.2.2.2.2.2.2
  have resultPhysical : PhysicalBoolDestination (Storage.withCurrent #[] result second) result pointer length true :=
    physical.reframeAlias heap borrowed addresses savedPlace (congrArg (·.borrowTracker) extra)
  obtain ⟨thread, active, _⟩ := admitted.stack.active
  let ready : RetainedSlice second := {
    id := storage.id, tag := tag, entry := storage.entry
    present := by rw [show second.memory = machine.memory from heap]; exact storage.live
    tracker := tracker, tracked := borrowed.trans region.tracked
    source := region.source, root := root, indexed := region.tagKnown, roots := roots
    node := node, found := found, unexposed := hidden
    thread := thread, active := by rw [show second.threads = machine.threads from threads]; exact active
  }
  have backing (key : AllocId) (row : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (live : second.memory.live[key]? = some row) :
      second.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) =
        some (key, {weakMemory := none, backtrace := (AllocationBacktrace.get
          second.user.payload.payload.user.runtime.extras.allocations key)}) := by
    have oldLive : before.machine.memory.live[key]? = some row := by
      have same : second.memory = before.machine.memory := heap
      rwa [same] at live
    obtain ⟨effect,found,weak,sync⟩ := admitted.allocations.extras key
      (MemoryCopyBridge.live_any_of_present before.machine.memory key row oldLive)
    have source : second.user.payload.payload.user.runtime.extras =
        before.machine.user.payload.payload.user.runtime.extras := stockExtras
    rw [source,AllocationBacktrace.of_lookup found,found]
    congr 2
    cases effect
    simp_all
  let lower := storage.relativeStart.bytes
  let upper := lower + length
  have fits : lower.toNat + length.toNat < 2^64 :=
    Nat.lt_of_le_of_lt extent.extent storage.entry.allocation.extra.locations.size.bytes.toNat_lt
  have upperEq : upper.toNat = lower.toNat+length.toNat := by
    dsimp [upper]
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have scope : ScopedPhysicalRelease.VisitsWithin ready.entry.allocation.extra ready.source lower.toNat upper.toNat := by
    rw [upperEq]
    exact extent.visitsWithin
  have ghost := secondFields.2.2.2.2.2.1.trans (firstFields.2.2.2.2.2.1.trans entry.ghost)
  have shallow := secondFields.2.2.2.2.2.2.1.trans (firstFields.2.2.2.2.2.2.1.trans entry.shallow)
  have checked := (RootZeroCompleteState.tick_flags options remaining span first).1.trans
    ((RootZeroCompleteState.tick_flags options remaining span machine).1.trans admitted.profile.unchecked)
  have gc := (RootZeroCompleteState.tick_flags options remaining span first).2.trans
    ((RootZeroCompleteState.tick_flags options remaining span machine).2.trans admitted.profile.noGc)
  have race := secondFields.2.2.2.1.trans (firstFields.2.2.2.1.trans admitted.profile.raceOff)
  have backend := secondFields.2.2.2.2.2.2.2.1.trans
    (firstFields.2.2.2.2.2.2.2.1.trans admitted.profile.backendOff)
  obtain ⟨done, finish, empty, _, _⟩ := returnPhysicalWithSharedSlice options limits remaining span fuel validation
    admitted.profile.debugOff result second pointer length positive ready concrete false resultPhysical backing region.coherent
    lower upper base address upperEq (by rw [show second.user.addresses = machine.user.addresses from addresses]; exact cached)
    scope (fun query missing position bound => extent.vacant query missing _ (Array.mem_iff_getElem.mpr ⟨position,bound,rfl⟩))
    (RetagReleaseRights.region_owned before length storage tag region extent.extent)
    (body.trans entry.body) location true slot ((congrArg (·.dataRace) extra).trans entry.noClocks)
    (continues.trans continuation) immediate (args.trans admitted.stack.noVarargs) ghost shallow checked gc
    (by rw [show second.threads = machine.threads from threads]; exact entry.fixed) race backend
  exact GeneratedSafetyOfTrace.required program loaded config limits _ done admitted.entered
    (state.symm ▸ SuccessfulTrace.append trace finish) (by rw [state]; simp [empty,Storage.withCurrent])

#print axioms zeroCountNonemptyPhysicalShared
end DuplicatePrefix.CanonicalCallDomain

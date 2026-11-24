import duplicate_prefix.RootPositiveCachedReturn
import duplicate_prefix.RootPositiveReleaseAfterCopy
import duplicate_prefix.RootPhysicalReturnOfPlan

namespace DuplicatePrefix.RootPositivePhysicalPop
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PreparedArguments SourceDomain RootPositiveCachedReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 18000000

abbrev Frame := CompilerFrameContext.ActualFrame
abbrev State := MachineHooks.State MiriMemoryKind Machine.RootUser
abbrev MachineState := MachineHooks.MachineState MiriMemoryKind Machine.RootUser

def afterPop (frame : Frame) (charged : MachineState) (released : MemoryState Provenance BorrowTree MiriMemoryKind)
    (tracker : MachineHooks.BorrowState) (ledger : FrameState) (thread : ThreadRecord) : State :=
  ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] frame
    (ActualPopPlan.released charged released tracker ledger) (thread.topUserRelevantFrame.getD 0)⟩

/-- Expose the exact pre- and post-pop state used by physical copy-out.
Clock accounting leaves the keyed rows alone. The borrow ledger is discharged
in the order stored on the actual frame. -/
theorem prepare
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame result done : Frame) (initial last : MachineState)
    (length count base : UInt64) (copyTag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent #[] frame initial) length)
    (rights : ExclusiveRegion (Storage.withCurrent #[] frame initial) length storage copyTag)
    (holder : Holder storage.entry.allocation.extra rights.tracker.global.protectedTags copyTag rights.source
      storage.relativeStart length)
    (disjoint : count.toNat + count.toNat ≤ length.toNat)
    (allocation : Allocation Provenance BorrowTree)
    (copy : RootPositiveRootSuffix.ReadyAfterCopy options remaining span #[] frame initial
      length count base copyTag storage rights result last allocation)
    (slotId : AllocId) (slotTag : BorTag) (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotLive : initial.memory.live[slotId]? = some slot)
    (slotTree : BorrowTree)
    (slotRelease : slot.allocation.extra.releaseProtector slotTag rights.tracker.global.protectedTags =
      ⟨slotTree,.Released⟩)
    (separate : slotId ≠ storage.id)
    (owned : FrameState) (ledger : owned.protectedTags = #[(storage.id,holder.tag),(slotId,slotTag)]) :
    let tick := LanguageZeroStep.accountedMachine options remaining span
    let charged := tick (tick last)
    let cleaned := {done with location := .mir ⟨10,0⟩}
    ∃ thread released,
      charged.threads.activeThread? = some thread ∧
      charged.borrowTracker = some rights.tracker ∧
      StackPopRelease.Plan rights.tracker.global.protectedTags owned.protectedTags.toList charged.memory released ∧
      let state := afterPop cleaned charged released rights.tracker owned thread
      state.machine.memory.live[slotId]? = some {slot with allocation := slot.allocation.setExtra slotTree} ∧
      state.machine.borrowTracker = some {rights.tracker with global := rights.tracker.global.endCall owned} ∧
      state.machine.user.addresses = initial.user.addresses ∧
      state.machine.user.payload.payload.user.runtime.extras = initial.user.payload.payload.user.runtime.extras ∧
      state.machine.dataRace = none ∧ state.machine.user.payload.payload.user.backend = .none ∧
      state.machine.user.payload.ghost = false ∧ state.machine.user.payload.validation = .Shallow ∧
      (rights.tracker.global.endCall owned).protectedTags.contains slotTag = false := by
  dsimp only
  let tick := LanguageZeroStep.accountedMachine options remaining span
  let charged := tick (tick last)
  let clean := {done with location := .mir ⟨10,0⟩}
  let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨storage.entry.kind,allocation⟩
  have fields1 := CopyRootGuardState.accounted_fields options remaining span last
  have fields2 := CopyRootGuardState.accounted_fields options remaining span (tick last)
  have memory : charged.memory = last.memory := fields2.1.trans fields1.1
  have tracked : charged.borrowTracker = some rights.tracker := fields2.2.1.trans (fields1.2.1.trans copy.tracker)
  have threads : charged.threads = last.threads := fields2.2.2.1.trans fields1.2.2.1
  obtain ⟨thread, active⟩ := copy.active
  have chargedActive : charged.threads.activeThread? = some thread := by rw [threads]; exact active
  obtain ⟨released, steps, row, tagFree⟩ :=
    RootPositiveReleaseAfterCopy.plan rights.tracker owned ledger separate copy.present slotLive copy.disjoint
      storage.entry.allocation.extra rights.source holder.index holder.root storage.relativeStart count length disjoint
      holder.coherent holder.sourceNode holder.node holder.atSource holder.atHolder holder.unexposed holder.roots
      holder.atCopyTag holder.atHolderTag holder.lineage holder.unheld holder.fits holder.retained
      copy.copiedTree slotTree slotRelease
  have plan : StackPopRelease.Plan rights.tracker.global.protectedTags owned.protectedTags.toList charged.memory released :=
    by rw [memory]; exact steps
  let state := afterPop clean charged released rights.tracker owned thread
  have stateMemory : state.machine.memory = released := by
    unfold state afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have stateTracker : state.machine.borrowTracker = some {rights.tracker with global := rights.tracker.global.endCall owned} := by
    unfold state afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have stateUser : state.machine.user = charged.user := by
    unfold state afterPop GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have stateRace : state.machine.dataRace = none := by
    have race : state.machine.dataRace = charged.dataRace := by
      unfold state afterPop GenericPopFrame.afterRelevanceAt
      split <;> rfl
    exact race.trans (fields2.2.2.2.1.trans (fields1.2.2.2.1.trans copy.race))
  have address : state.machine.user.addresses = initial.user.addresses :=
    (congrArg (·.addresses) stateUser).trans (fields2.2.2.2.2.1.trans (fields1.2.2.2.2.1.trans copy.addresses))
  have backing : state.machine.user.payload.payload.user.runtime.extras = initial.user.payload.payload.user.runtime.extras :=
    (congrArg (·.payload.payload.user.runtime.extras) stateUser).trans
      (fields2.2.2.2.2.2.2.2.2.1.trans (fields1.2.2.2.2.2.2.2.2.1.trans copy.backing))
  have backend : state.machine.user.payload.payload.user.backend = .none :=
    (congrArg (·.payload.payload.user.backend) stateUser).trans
      (fields2.2.2.2.2.2.2.2.1.trans (fields1.2.2.2.2.2.2.2.1.trans copy.backend))
  have ghost : state.machine.user.payload.ghost = false :=
    (congrArg (·.payload.ghost) stateUser).trans (fields2.2.2.2.2.2.1.trans (fields1.2.2.2.2.2.1.trans copy.ghost))
  have shallow : state.machine.user.payload.validation = .Shallow :=
    (congrArg (·.payload.validation) stateUser).trans
      (fields2.2.2.2.2.2.2.1.trans (fields1.2.2.2.2.2.2.1.trans copy.shallow))
  exact ⟨thread,released,chargedActive,tracked,plan,by rw [stateMemory]; exact row,stateTracker,
    address,backing,stateRace,backend,ghost,shallow,tagFree⟩

#print axioms prepare
end DuplicatePrefix.RootPositivePhysicalPop

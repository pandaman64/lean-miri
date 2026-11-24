import PhysicalDestinationAfterCopy
import PhysicalReturnWithSharedSlice
import duplicate_prefix.RootPositiveRootSuffix

namespace DuplicatePrefix.RootAliasedReturnAfterCopy

open Miri Miri.ABI Miri.Concurrency Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open SourceDomain PreparedArguments CanonicalCallDomain RootZeroShallowReturn
open AccessedCopyHolderRights PhysicalDestinationAfterCopy

set_option maxRecDepth 65536
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

/-- The actual root's successful return after the positive adjacent copy.
The saved result byte may be in the copied allocation outside the slice. -/
theorem returns
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1)
    (frame result done : CompilerFrameContext.ActualFrame)
    (machine last : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length count base : UInt64) (raw : BorTag)
    (storage : InitializedRegion (Storage.withCurrent #[] frame machine) length)
    (rights : ExclusiveRegion (Storage.withCurrent #[] frame machine) length storage raw)
    (slice : SliceHolder storage.entry.allocation.extra rights.tracker.global.protectedTags raw
      storage.relativeStart length)
    (disjoint : count.toNat + count.toNat ≤ length.toNat)
    (nonempty : 0 < length)
    (allocation : Allocation Provenance BorrowTree)
    (copy : RootPositiveRootSuffix.ReadyAfterCopy options remaining span #[] frame machine
      length count base raw storage rights result last allocation)
    (cleanup : RootSuccessCleanupFacts.Shape result done RootCompilerFacts.boolLayout (.scalar (.fromBool true)))
    (body : frame.body = RootBody.reflected.body.body)
    (clocks : frame.extra.dataRace = none)
    (varargs : frame.vaList = #[])
    (continuation : frame.returnContinuation = .stop true)
    (pointer : Pointer (Option Provenance))
    (concrete : pointer.provenance = some (.concrete storage.id slice.tag))
    (address : pointer.offset.bytes.toNat = base.toNat+storage.relativeStart.bytes.toNat)
    (cached : machine.user.addresses.baseAddr.find? (·.allocId == storage.id) = some ⟨storage.id,base⟩)
    (physical : PhysicalBoolDestination (Storage.withCurrent #[] frame machine) frame pointer length true)
    (backing : ∀ key entry, machine.memory.live[key]? = some entry →
      machine.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) =
        some (key,{weakMemory := none,backtrace := (AllocationBacktrace.get
          machine.user.payload.payload.user.runtime.extras.allocations key)})) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let start := Storage.withCurrent #[] {done with location := .mir ⟨10,0⟩}
      (SourceControl.accounted cfg.terminators (Storage.withCurrent #[] done last)).machine
    ∃ final, ExecutionMachine.step cfg limits () start = (final,.ok true) ∧
      ExecutionMachine.step cfg limits () final = (final,.ok false) ∧ final.stack.frames = #[] := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let startFrame := {done with location := .mir ⟨10,0⟩}
  let startMachine := LanguageZeroStep.accountedMachine options remaining span last
  let start := Storage.withCurrent #[] startFrame startMachine
  have h := CopyRootGuardState.accounted_fields options remaining span last
  have mem : startMachine.memory = last.memory := h.1
  have tracked : startMachine.borrowTracker = some rights.tracker := h.2.1.trans copy.tracker
  have threads : startMachine.threads = last.threads := h.2.2.1
  have addresses : startMachine.user.addresses = machine.user.addresses := h.2.2.2.2.1.trans copy.addresses
  have extraRows : startMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras :=
    h.2.2.2.2.2.2.2.2.1.trans copy.backing
  have live : startMachine.memory.live[storage.id]? = some ⟨storage.entry.kind,allocation⟩ := by
    rw [mem]
    exact copy.present
  have retainedRows (key : AllocId) (separate : key ≠ storage.id) :
      startMachine.memory.live[key]? = machine.memory.live[key]? := by rw [mem]; exact copy.disjoint key separate
  have weak : PhysicalBoolDestination start startFrame pointer length true true :=
    PhysicalDestinationAfterCopy.transport frame startFrame (Storage.withCurrent #[] frame machine) start
      pointer length count storage.id storage.relativeStart base raw storage.entry allocation storage.live live
      retainedRows copy.sized copy.len copy.storageValid rights.tracker rights.tracked tracked slice concrete cached address
      (fun zero => by rw [zero] at nonempty; exact UInt64.lt_irrefl _ nonempty) disjoint copy.copiedTree
      addresses (cleanup.destination.trans copy.returnPlace)
      (congrArg MachineHooks.FrameExtra.borrowTracker (cleanup.extra.trans copy.extra)) physical
  obtain ⟨_,_,shape,coherent,sized,footprint⟩ :=
    AccessedCopyHolderRights.prefixCopy_retains_holder storage.entry.allocation.extra rights.tracker.global.protectedTags raw
      slice.source slice.holder slice.root storage.relativeStart count length disjoint slice.coherent slice.node slice.atSource
      slice.roots slice.atTag slice.lineage slice.unheld slice.fits slice.footprint
  have tree := copy.copiedTree
  dsimp only at tree
  rw [show Size.ofBytes storage.relativeStart.bytes = storage.relativeStart from rfl] at tree
  rw [← tree] at shape coherent sized footprint
  obtain ⟨thread,active⟩ := copy.active
  let retained : RetainedSlice startMachine :=
    { id := storage.id
      tag := slice.tag
      entry := ⟨storage.entry.kind,allocation⟩
      present := live
      tracker := rights.tracker
      tracked := tracked
      source := slice.holder
      root := slice.root
      indexed := by change allocation.extra.indexOfTag slice.tag = _; rw [shape]; exact slice.holderTag
      roots := by change allocation.extra.roots = _; rw [shape]; exact slice.roots
      node := slice.holderNode
      found := by change allocation.extra.nodeAt slice.holder = _; rw [shape]; exact slice.atHolder
      unexposed := slice.unexposed
      thread := thread
      active := by rw [threads]; exact active }
  let lo := storage.relativeStart.bytes
  let hi := lo+length
  have fits : lo.toNat+length.toNat < 2^64 := Nat.lt_of_le_of_lt slice.fits storage.entry.allocation.extra.locations.size.bytes.toNat_lt
  have endNat : hi.toNat = lo.toNat+length.toNat := by
    simp only [hi, UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have releaseScope : AccessedOnlyWithin allocation.extra retained.source lo.toNat hi.toNat := footprint.accessed
  have backingNow (key : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (present : startMachine.memory.live[key]? = some entry) :
      startMachine.user.payload.payload.user.runtime.extras.allocations.find? (·.1 == key) =
        some (key,{weakMemory := none,backtrace := (AllocationBacktrace.get
          startMachine.user.payload.payload.user.runtime.extras.allocations key)}) := by
    rw [extraRows]
    by_cases equal : key = storage.id
    · subst key
      exact backing storage.id storage.entry storage.live
    · exact backing key entry ((retainedRows key equal).symm.trans present)
  have slot : startFrame.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ := cleanup.output
  have ghost : startMachine.user.payload.ghost = false := h.2.2.2.2.2.1.trans copy.ghost
  have shallow : startMachine.user.payload.validation = .Shallow := h.2.2.2.2.2.2.1.trans copy.shallow
  have race : startMachine.dataRace = none := h.2.2.2.1.trans copy.race
  have backend : startMachine.user.payload.payload.user.backend = .none := h.2.2.2.2.2.2.2.1.trans copy.backend
  have fixed : startMachine.threads.fixedScheduling = true := by rw [threads]; exact copy.fixed
  have control : cfg.terminators.getControl startMachine.user = TerminatorClock.advance (cfg.terminators.getControl last.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have unchecked : (cfg.terminators.getControl startMachine.user).checkedArithmetic = false := by rw [control]; exact copy.unchecked
  have gc : (cfg.terminators.getControl startMachine.user).gcInterval = 0 := by rw [control]; exact copy.noGc
  obtain ⟨finish,_,empty,stopped,step⟩ :=
    returnPhysicalWithSharedSlice options limits remaining span fuel validation debug startFrame startMachine
      pointer length nonempty retained concrete true weak backingNow coherent lo hi base address endNat
      (by rw [addresses]; exact cached) releaseScope.visitsWithin footprint.vacant footprint.holderRights
      (cleanup.body.trans (copy.body.trans body)) rfl true slot
      (by change done.extra.dataRace = none; rw [cleanup.extra,copy.extra]; exact clocks)
      (cleanup.continuation.trans (copy.returnContinuation.trans continuation)) (cleanup.immediate copy.direct)
      (cleanup.varargs.trans (copy.varargs.trans varargs)) ghost shallow unchecked gc fixed race backend
  exact ⟨finish,step,stopped,empty⟩

#print axioms returns
end DuplicatePrefix.RootAliasedReturnAfterCopy

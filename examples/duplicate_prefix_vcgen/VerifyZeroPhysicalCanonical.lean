import VerifyZeroCachedCanonical
import ZeroCanonicalPhysicalPlan

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open Miri.TreeBorrows Miri.Verification
open RootZeroShallowReturn SourceDomain ArchiveForestProjection GeneralRangeMapOrigins

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

private theorem rebuildPointer (p : Pointer (Option Provenance)) :
    p = Pointer.new p.provenance (Size.ofBytes p.offset.bytes) := by
  cases p with
  | mk offset provenance => cases offset; rfl

private theorem exactExtras {P : Type} (rows : Array (AllocId × MemoryExtras.AllocationExtra P))
    (id : AllocId) (extra : MemoryExtras.AllocationExtra P)
    (lookup : rows.find? (·.1 == id) = some (id,extra))
    (weak : extra.weakMemory = none) (sync : extra.sync = #[]) :
    rows.find? (·.1 == id) = some (id, {weakMemory := none, backtrace := AllocationBacktrace.get rows id}) := by
  rw [lookup, AllocationBacktrace.of_lookup lookup]
  cases extra
  simp_all

private theorem grantForByte {tree : BorrowTree} {start : Size} {source : UniIndex}
    {tags : ProtectedTags} (grant : ByteWriteGrant tree start.bytes source tags)
    (extent : ReleaseRange tree source start 1) :
    OwnedOn (fun row => LocationRights tree row tags source)
      start.bytes (start.bytes + 1) tree.locations := by
  have fits : start.bytes.toNat + 1 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt extent.extent tree.locations.size.bytes.toNat_lt
  have endByte : (start.bytes + 1).toNat = start.bytes.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt fits]
  intro position inside _ starts stops
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  have below : segment.range.start ≤ start.bytes := by
    rw [UInt64.le_iff_toNat_le]
    change segment.range.start.toNat < (start.bytes + 1).toNat at starts
    omega
  exact grant segment member below (UInt64.lt_iff_toNat_lt.mpr stops)

/-- The actual count-zero branch writes true to any admitted interior
Boolean output byte, releases the ordered argument and output protector
ledger, and stops the root. -/
theorem zeroCountPhysical
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (fuel : Nat) (validation : options.limits.validation = fuel+1)
    (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (length : UInt64)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer length 0)
    (compiler : InitialCompilerControl before frame) (physical : PhysicalBoolDestination before frame pointer length)
    (stack : before.stack.frames = #[frame]) (continuation : frame.returnContinuation = .stop true) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let machine := before.machine
  have state : before = Storage.withCurrent #[] frame machine := withFrames stack
  have entry := zeroCountEntry loaded admitted compiler
  obtain ⟨place, id, allocation, relative, tag, base, tracker, owned, source, returnTag, holder,
    saved, layout, aligned, live, mutable, storage, mask, maskLength, provenance, fits, ptr, _,
    address, addressFits, cached, tracked, trackedFrame, ledger, _, coherent, sourceKey,
    sourceNode, holderKey, holderNode, extent, writeGrant, _, separated⟩ := physical.storage
  obtain ⟨old, oldTracker, mode⟩ := admitted.profile.mode
  have same : old = tracker := Option.some.inj (oldTracker.symm.trans tracked)
  subst old
  obtain ⟨node, atNode, nodeTag, parent, hidden⟩ := holderNode
  have ownedTag : returnTag ∈ owned.protectedTags.toList.map Prod.snd := by
    rw [ledger]
    simp
  obtain ⟨afterTree, outputReleased, treeFrame, afterCoherent, treeSize, owners⟩ :=
    physicalReleasePreservesParent allocation.allocation.extra tracker.global owned returnTag holder source
      node relative holderKey atNode nodeTag parent hidden coherent extent ownedTag (grantForByte writeGrant extent)
  obtain ⟨finalHeap, release, outputLive⟩ := admitted.zeroPhysicalPlan tracker tracked owned trackedFrame
    id returnTag allocation afterTree ledger live separated outputReleased
  obtain ⟨result, trace, resultBody, _, _, frameExtra, resultPlace, resultResume, args, _, resultSize,
    location, slot, immediate⟩ := RootZeroCompletePrefix.reaches_return options limits remaining span compilerSourceComparator
      admitted.profile.debugOff fuel validation #[] frame machine
      entry.body entry.identity entry.callee entry.location entry.size entry.live0 entry.uncached0
      entry.dead3 entry.dead4 entry.dead5 entry.uncached4 entry.uncached5 entry.zero entry.cached2
      entry.noClocks entry.immediate tracker tracked mode entry.ghost entry.shallow
      admitted.profile.unchecked admitted.profile.noGc entry.fixed
  let first := RootZeroCompleteState.tick options remaining span machine
  let second := RootZeroCompleteState.tick options remaining span first
  let charged := PtrMetadataReturn.accountedMachine options remaining span second
  have tails := zeroTickFields options remaining span second
  have initialFields := zeroTickFields options remaining span machine
  have middleFields := zeroTickFields options remaining span first
  have heap : charged.memory = machine.memory := tails.1.trans (middleFields.1.trans initialFields.1)
  have trackerNow : charged.borrowTracker = some tracker :=
    tails.2.1.trans (middleFields.2.1.trans (initialFields.2.1.trans tracked))
  have sameThreads : charged.threads = machine.threads :=
    tails.2.2.1.trans (middleFields.2.2.1.trans initialFields.2.2.1)
  obtain ⟨thread, current, _⟩ := admitted.stack.active
  have liveThread : charged.threads.activeThread? = some thread := by rw [sameThreads]; exact current
  have legalRelease : StackPopRelease.Plan tracker.global.protectedTags owned.protectedTags.toList
      charged.memory finalHeap := by rw [heap]; exact release
  let released := ActualPopPlan.released charged finalHeap tracker owned
  let passed := GenericPopFrame.afterRelevanceAt #[] result released (thread.topUserRelevantFrame.getD 0)
  let retState : State := ⟨⟨#[]⟩, passed⟩
  have resultHeap : retState.machine.memory = finalHeap := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  let finalTracker := {tracker with global := tracker.global.endCall owned}
  have resultTracker : retState.machine.borrowTracker = some finalTracker := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultUser : retState.machine.user = charged.user := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have resultRace : retState.machine.dataRace = charged.dataRace := by
    unfold retState passed GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have addresses : retState.machine.user.addresses = machine.user.addresses :=
    (congrArg (·.addresses) resultUser).trans (tails.2.2.2.2.1.trans
      (middleFields.2.2.2.2.1.trans initialFields.2.2.2.2.1))
  have extrasPreserved : retState.machine.user.payload.payload.user.runtime.extras =
      machine.user.payload.payload.user.runtime.extras :=
    (congrArg (·.payload.payload.user.runtime.extras) resultUser).trans
      (tails.2.2.2.2.2.2.2.2.trans (middleFields.2.2.2.2.2.2.2.2.trans initialFields.2.2.2.2.2.2.2.2))
  have race : retState.machine.dataRace = none :=
    resultRace.trans (tails.2.2.2.1.trans (middleFields.2.2.2.1.trans (initialFields.2.2.2.1.trans admitted.profile.raceOff)))
  have backend : retState.machine.user.payload.payload.user.backend = .none :=
    (congrArg (·.payload.payload.user.backend) resultUser).trans
      (tails.2.2.2.2.2.2.2.1.trans (middleFields.2.2.2.2.2.2.2.1.trans
        (initialFields.2.2.2.2.2.2.2.1.trans admitted.profile.backendOff)))
  have beforeGhost : charged.user.payload.ghost = false :=
    tails.2.2.2.2.2.1.trans (middleFields.2.2.2.2.2.1.trans (initialFields.2.2.2.2.2.1.trans entry.ghost))
  have ghost : retState.machine.user.payload.ghost = false := (congrArg (·.payload.ghost) resultUser).trans beforeGhost
  have shallow : retState.machine.user.payload.validation = .Shallow :=
    (congrArg (·.payload.validation) resultUser).trans
      (tails.2.2.2.2.2.2.1.trans (middleFields.2.2.2.2.2.2.1.trans (initialFields.2.2.2.2.2.2.1.trans entry.shallow)))
  have width := allocation.allocation.byteSize.bytes.toNat_lt
  have relativeFits := UInt64.lt_iff_toNat_lt.mp fits
  have absFits : base.toNat + relative.bytes.toNat < 2^64 := by omega
  have addNat : (base + relative.bytes).toNat = base.toNat + relative.bytes.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt absFits]
  have originalOffset : place.mplace.ptr.offset.bytes = base + relative.bytes :=
    UInt64.toNat.inj (address.trans addNat.symm)
  have exactPointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+relative.bytes)) := by
    exact (rebuildPointer place.mplace.ptr).trans (by rw [ptr,originalOffset])
  let finalEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {allocation with allocation := allocation.allocation.setExtra afterTree}
  let window : PhysicalBoolWindowWrite.Window retState.machine place := {
    layout, aligned, id, tag
    entry := finalEntry
    base
    offset := relative.bytes
    capacity := allocation.allocation.byteSize.bytes
    live := by rw [resultHeap]; exact outputLive
    cachedBase := by rw [addresses]; exact cached
    pointer := exactPointer
    bounds := by omega
    size := by change allocation.allocation.byteSize = Size.ofBytes allocation.allocation.byteSize.bytes; cases allocation.allocation.byteSize; rfl
    bytes := storage
    mutable
    maskValid := mask
    maskLength
    provenance := ProvenanceCopy.WellFormed.pointerBounds provenance }
  have newKey : window.entry.allocation.extra.indexOfTag window.tag = some source := by
    change afterTree.indexOfTag tag = some source
    rw [treeFrame]
    exact sourceKey
  obtain ⟨originalSource, sourceHere, _⟩ := sourceNode
  have newNode : window.entry.allocation.extra.nodeAt source = some originalSource := by
    change afterTree.nodeAt source = some originalSource
    rw [treeFrame]
    exact sourceHere
  obtain ⟨root, rootEq⟩ := extent.root (by decide)
  have roots : window.entry.allocation.extra.roots = #[root] := by
    change afterTree.roots = #[root]
    rw [treeFrame]
    exact rootEq
  have bound : window.offset.toNat + 1 ≤ window.entry.allocation.extra.locations.size.bytes.toNat := by
    change relative.bytes.toNat + 1 ≤ afterTree.locations.size.bytes.toNat
    rw [treeSize]
    exact extent.extent
  have effects : let ctx := (DuplicatePrefixPhysicalContexts.canonical options remaining span).writeContext
      (ctx.extras.get retState.machine.user).allocations.find? (·.1 == id) =
        some (id, {weakMemory := none, backtrace := (AllocationBacktrace.get
          ((ctx.extras.get retState.machine.user).allocations) id)}) := by
    dsimp only
    let actualRows := retState.machine.user.payload.payload.user.runtime.extras.allocations
    change actualRows.find? (·.1 == id) =
      some (id,{weakMemory := none, backtrace := AllocationBacktrace.get actualRows id})
    dsimp only [actualRows]
    obtain ⟨extra, location, weak, sync⟩ := admitted.allocations.extras id
      (MemoryCopyBridge.live_any_of_present before.machine.memory id allocation live)
    have baseFacts := exactExtras _ id extra location weak sync
    have extrasEq : retState.machine.user.payload.payload.user.runtime.extras =
        before.machine.user.payload.payload.user.runtime.extras := extrasPreserved
    rw [extrasEq]
    exact baseFacts
  have addressBound : place.mplace.ptr.offset.bytes.toNat + 1 < 2^64 := by omega
  have flagsFirst := RootZeroCompleteState.tick_flags options remaining span machine
  have flagsSecond := RootZeroCompleteState.tick_flags options remaining span first
  have fixed : second.threads.fixedScheduling = true := by rw [middleFields.2.2.1,initialFields.2.2.1]; exact entry.fixed
  have valid : 0 < result.locals.size := by omega
  have bool : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))), some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans slot)
  obtain ⟨updated, returned, stopped, _, _, _⟩ :=
    RootWindowPhysicalReturn.return_step_terminal options remaining span limits fuel validation
      admitted.profile.debugOff result second charged rfl
      (flagsSecond.1.trans (flagsFirst.1.trans admitted.profile.unchecked))
      (flagsSecond.2.trans (flagsFirst.2.trans admitted.profile.noGc)) fixed
      tracker owned trackerNow (by rw [frameExtra]; exact trackedFrame) finalHeap legalRelease thread liveThread
      retState rfl (resultBody.trans entry.body) location valid true
      (congrArg LocalState.value bool) (congrArg LocalState.layout bool)
      ((congrArg MachineHooks.FrameExtra.dataRace frameExtra).trans entry.noClocks) beforeGhost
      (resultResume.trans continuation) immediate (args.trans admitted.stack.noVarargs)
      place window (by rw [resultPlace,saved]; rfl) finalTracker resultTracker race backend ghost shallow
      source root originalSource newNode newKey roots afterCoherent bound owners effects addressBound
  rw [state]
  apply GeneratedSafetyOfTrace.required program loaded config limits _ _ (state ▸ admitted.entered)
    (SuccessfulTrace.append trace (.next returned (.refl _)))
  simp [CanonicalCopy.replaceAllocation,retState,Storage.withCurrent]

/-- Count zero discharges the emitted VC for either admitted return carrier,
with both empty and nonempty slice inputs. -/
theorem zeroCount
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (fuel : Nat) (validation : options.limits.validation = fuel+1)
    (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (length : UInt64)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer length 0)
    (compiler : InitialCompilerControl before frame) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  cases admitted.destination with
  | physicalRoot stack continuation physical =>
    exact zeroCountPhysical program loaded options limits remaining span fuel validation before frame pointer length
      admitted compiler physical stack continuation
  | cachedCaller cached _ =>
    exact zeroCountCached program loaded options limits remaining span fuel validation before frame pointer length
      admitted compiler cached

open Lean Elab Command in
run_cmd do
  for declaration in [``zeroCountPhysical, ``zeroCount] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved zero-count dependency {dependency}"

#print axioms zeroCount

end DuplicatePrefix.CanonicalCallDomain

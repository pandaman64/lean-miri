import RootLengthBranchReturn
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild

set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

/-- Compose the actual zero and rejection paths with the accepted-arm
execution proof over the shared length checkpoint. -/
theorem allCountSafetyByAcceptedArm
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (outside frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (uncached3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace=none) (all : ZeroImmediateFacts.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (defaultMode : tracker.retagMode=.Default)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (sizing : options.place.dynamicFuel = sizeFuel+1)
    (preciseOff : options.retag.preciseInteriorMut = false) (implicitOff : options.retag.implicitWrites = false)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut) (raceOff : machine.dataRace = none)
    (positiveLen : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent (older.push outside) frame machine)).entries.any
      (·.value.ty == 2) = false)
    (coherent : CoherentForest entry.allocation.extra) (parentNode : TreeNode)
    (parentStored : entry.allocation.extra.nodeAt parent = some parentNode)
    (roots : entry.allocation.extra.roots = #[root]) (parentFound : entry.allocation.extra.indexOfTag parentTag = some parent)
    (depth : BorrowTree.ZeroProtection.ParentDepth entry.allocation.extra.nodes)
    (rank : depth.depth parent < entry.allocation.extra.nodes.size)
    (tagFresh : entry.allocation.extra.indexOfTag tracker.global.nextPointerTag = none)
    (nodeFresh : ∀ index data, entry.allocation.extra.nodeAt index = some data → data.tag ≠ tracker.global.nextPointerTag)
    (unheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (room : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (aligned : entry.allocation.extra.tagMapping.deassigned.back? = none → entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (reuse : ∀ index, entry.allocation.extra.tagMapping.deassigned.back? = some index →
      index.toNat < entry.allocation.extra.nodes.size ∧ entry.allocation.extra.nodeAt index = none)
    (clean : VacantRows entry.allocation.extra)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights entry.allocation.extra row tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (extent : MaterializedWithin entry.allocation.extra parent offset (offset+len))
    (sourceSlot : frame.locals[1]? = some ⟨.live (.immediate (.scalarPair
      (.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))))
      (.fromScalarInt (.ofUInt64 len)))), some RootCompilerFacts.sliceLayout⟩)
    (ready : ActiveCaller older outside frame machine)
    (sameId : id = ready.id) (sameRoot : root = ready.root) (sameHolder : parent = ready.source)
    (sameTag : parentTag = ready.tag)
    (heldUnexposed : parentNode.isExposed = false)
    (resultSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩)
    (tempSlot : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩)
    (backend : machine.user.payload.payload.user.backend = .none)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (cacheValid : ∀ index, ready.thread.topUserRelevantFrame = some index → index < (older.push outside).size + 1)
    (tagHeadroom : tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615)
    (initialKeys : RetagInsertionCapacity.Ready entry.allocation.extra)
    (keySpace : entry.allocation.extra.nodes.size + 2 < 2^32)
    (keyAge : ∀ old i, entry.allocation.extra.indexOfTag old = some i → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (nodeAge : ∀ i data, entry.allocation.extra.nodeAt i = some data → data.tag.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectedAge : ∀ old, tracker.global.protectedTags.contains old = true → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (cachedRoot : ready.thread.topUserRelevantFrame = some (older.push outside).size)
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (entered : Miri.Verification.WholeBodyWP.entryMatchesLoaded program.root (Storage.withCurrent (older.push outside) frame machine))
    (acceptedArm : ∀ result final, RootLengthState (PreparedContracts.actualConfig options () (remaining+1) span)
      older outside frame result machine final ready entry offset len n tracker →
      ¬ n > len/2 → 0 < n.toNat →
      ∃ done, SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (older.push outside) result final) done ∧
        done.stack.frames.size < (Storage.withCurrent (older.push outside) result final).stack.frames.size) :
    GeneratedBodySafety.requiredForEveryChoiceAt (PreparedContracts.actualConfig options () (remaining+1) span)
      limits (Storage.withCurrent (older.push outside) frame machine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  by_cases zero : n = 0
  · have valid : 0 < frame.locals.size := by rw [size]; decide
    have checked0 : frame.locals[0] = ⟨.live (.immediate .uninit), none⟩ :=
      Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans resultSlot)
    let zeroEntry : ZeroEntry frame machine := {
      body, identity, callee, location, size
      live0 := congrArg (·.value) checked0
      uncached0 := congrArg (·.layout) checked0
      dead3, dead4, dead5, uncached4, uncached5
      zero := by rw [← zero]; exact live2
      cached2, noClocks
      immediate := all
      ghost, shallow, fixed }
    have sameTracker : tracker = ready.tracker := Option.some.inj (tracked.symm.trans ready.tracked)
    obtain ⟨done, trace, returned⟩ := executesZeroReturn options limits remaining span source debugOff fuel fuelEq
      older outside frame machine zeroEntry ready (by rw [← sameTracker]; exact defaultMode) noGc unchecked
    exact GeneratedSafetyOfTrace.required program loaded cfg limits _ done entered trace returned
  · obtain ⟨result, final, trace, ⟨post⟩⟩ :=
      reachesRootLengthGuard options limits remaining sizeFuel span source debugOff fuel fuelEq older outside frame machine
        body identity callee location size n zero unused dead3 uncached3 dead4 dead5 uncached4 uncached5 live2 cached2
        noClocks all tracker tracked defaultMode ghost shallow unchecked noGc fixed sizing preciseOff implicitOff
        id parentTag parent root base offset len entry fresh cached live allocationMut raceOff positiveLen bounded memoryBounds
        notNull cmp metadata noAlias coherent parentNode parentStored roots parentFound depth rank tagFresh nodeFresh
        unheld room aligned reuse clean bounds owners extent sourceSlot ready sameId sameRoot sameHolder sameTag heldUnexposed
        resultSlot tempSlot backend dispatch dispatchFuel cacheValid tagHeadroom initialKeys keySpace keyAge nodeAge protectedAge cachedRoot
    have leaves : ∃ done, SuccessfulTrace.Trace cfg limits (Storage.withCurrent (older.push outside) result final) done ∧
        done.stack.frames.size < (Storage.withCurrent (older.push outside) result final).stack.frames.size := by
      by_cases rejected : n > len/2
      · exact post.rejectionTrace options limits remaining span source debugOff fuel fuelEq rejected
      · apply acceptedArm result final post rejected
        have notEmpty : n.toNat ≠ 0 := by
          intro empty
          apply zero
          exact UInt64.toNat.inj (by simp [empty])
        omega
    obtain ⟨done, tail, returned⟩ := leaves
    exact GeneratedSafetyOfTrace.required program loaded cfg limits _ done entered (SuccessfulTrace.append trace tail)
      (by simpa only [Storage.withCurrent, Array.size_push] using returned)

#print axioms allCountSafetyByAcceptedArm
end DuplicatePrefix.RootZeroShallowReturn

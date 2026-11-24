import RootRejectionPrepared
import CanonicalCallDomain

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ArchiveForestProjection SourceDomain GeneralRangeMapOrigins RetagReleaseFootprint RetagSharedChild

set_option maxHeartbeats 5000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

/-- The saved rejection VC under the canonical prepared-call profile,
with the nested cached return and dense-key shape made explicit. -/
theorem rejectedFromCanonicalAdmitted
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining sizeFuel : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (outside frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (size : frame.locals.size=25) (n : UInt64) (positive : n ≠ 0)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (uncached3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (sizing : options.place.dynamicFuel = sizeFuel+1)
    (id : AllocId) (parentTag : BorTag) (parent root : UniIndex) (base offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live[id]? = some entry)
    (allocationMut : entry.allocation.mutability = .Mut)
    (positiveLen : 0 < len) (bounded : len ≤ 9223372036854775807)
    (memoryBounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (notNull : base + offset ≠ 0)
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
    (tempSlot : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩)
    (rejected : n > len / 2)
    (dispatch : Nat) (dispatchFuel : limits.callDispatch = dispatch+1)
    (tagHeadroom : tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615)
    (pool : entry.allocation.extra.tagMapping.deassigned = #[])
    (keyShape : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.size)
    (nodeRoom : entry.allocation.extra.nodes.size + 1 ≤ 4294967295)
    (keyAge : ∀ old i, entry.allocation.extra.indexOfTag old = some i → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (nodeAge : ∀ i data, entry.allocation.extra.nodeAt i = some data → data.tag.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectedAge : ∀ old, tracker.global.protectedTags.contains old = true → old.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (program : Miri.Verification.BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (pointer : Pointer (Option Provenance))
    (admitted : CanonicalCallDomain.Admitted program options remaining CanonicalCallDomain.preparedTagHeadroom span
      (Storage.withCurrent (older.push outside) frame machine) frame pointer len n) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent (older.push outside) frame machine) := by
  let profile := admitted.profile
  obtain ⟨selected, sameTracker, defaultMode⟩ := profile.mode
  have trackerEq : selected = tracker := Option.some.inj (sameTracker.symm.trans tracked)
  subst selected
  obtain ⟨thread, running, cache⟩ := admitted.stack.active
  have threadEq : thread = ready.thread := Option.some.inj (running.symm.trans ready.active)
  subst thread
  have cacheValid : ∀ index, ready.thread.topUserRelevantFrame = some index → index < (older.push outside).size + 1 := by
    intro index saved
    simpa only [Storage.withCurrent, Array.size_push] using cache index saved
  exact rejectedGeneratedSafety options limits remaining sizeFuel span source profile.debugOff fuel fuelEq
    older outside frame machine body identity callee location size n positive unused dead3 uncached3 dead4 dead5
    uncached4 uncached5 live2 cached2 admitted.stack.calleeClocksOff admitted.immediateLocals tracker tracked defaultMode
    profile.ghostOff profile.shallow profile.unchecked profile.noGc profile.fixed sizing
    profile.preciseInteriorMutOff profile.implicitWritesOff id parentTag parent root base offset len entry fresh cached live
    allocationMut profile.raceOff positiveLen bounded memoryBounds notNull ProjectionMetadataFacts.nullComparator profile.compilerRuntime profile.noSyntheticSliceCache
    coherent parentNode parentStored roots parentFound depth rank tagFresh nodeFresh unheld room aligned reuse clean bounds
    owners extent sourceSlot ready sameId sameRoot sameHolder sameTag heldUnexposed admitted.resultSlot tempSlot rejected
    profile.backendOff dispatch dispatchFuel cacheValid tagHeadroom pool keyShape nodeRoom keyAge nodeAge protectedAge
    program loaded admitted.entered

#print axioms rejectedFromCanonicalAdmitted
end DuplicatePrefix.RootZeroShallowReturn

import duplicate_prefix.SharedLenReleaseWatch
import RetainedSlice
import RejectionFromEnteredLength
import duplicate_prefix.LenExitFacts
import duplicate_prefix.SliceLenCompleteCurrent
import duplicate_prefix.SharedReborrowContinuity

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures Miri.Concurrency
open PtrMetadataExecution PtrMetadataHelper PtrMetadataComplete MetadataUncachedCall
open NonemptyReturnWatch ScopedPhysicalRelease SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual root guard's data after returning from slice length. -/
structure LengthBranchOfActiveSlice (config : CanonicalConfigFacts.RootConfig)
    (initial lenMachine : LenExitFacts.MachineState) (root : RetainedSlice initial)
    (allocation : LocalAllocation Provenance BorrowTree MiriMemoryKind) (beforeRelease : BorrowTree) (releaseChild : UniIndex)
    (lower upper length count : UInt64) (caller : CompilerFrameContext.ActualFrame) (final : LenExitFacts.MachineState) where
  guard : RejectionEntry caller final length count
  ready : RetainedSlice final
  id : ready.id = root.id
  source : ready.source = root.source
  tag : ready.tag = root.tag
  origin : ready.root = root.root
  allocationData : ready.entry =
    {allocation with allocation := allocation.allocation.setExtra ready.entry.allocation.extra}
  graph : ready.entry.allocation.extra =
    {beforeRelease with locations := ready.entry.allocation.extra.locations}
  rangeCapacity : ready.entry.allocation.extra.locations.size = allocation.allocation.extra.locations.size
  coherence : CoherentForest ready.entry.allocation.extra
  writable : OwnedOn (fun row => LocationRights ready.entry.allocation.extra row ready.tracker.global.protectedTags ready.source)
    lower upper ready.entry.allocation.extra.locations
  activeScope : AccessedWithin ready.entry.allocation.extra ready.source lower upper
  releaseOutside : RetainsOutside beforeRelease.locations ready.entry.allocation.extra.locations lower.toNat upper.toNat
  releaseForeign : FramesRows (fun initial final =>
    ∀ watch data, beforeRelease.nodeAt watch = some data → ¬ Ancestor beforeRelease watch releaseChild →
      (beforeRelease.locationStateAt final watch).map LocationState.accessed =
        (beforeRelease.locationStateAt initial watch).map LocationState.accessed)
    beforeRelease.locations ready.entry.allocation.extra.locations
  vacant : VacantRows ready.entry.allocation.extra
  stable : LenExitFacts.Stable lenMachine final
  unrelated : ∀ key, key ≠ root.id → final.memory.live[key]? = lenMachine.memory.live[key]?
  defaultMode : ready.tracker.retagMode = .Default
  gc : (config.terminators.getControl final.user).gcInterval = 0
  unchecked : (config.terminators.getControl final.user).checkedArithmetic = false

/-- Return from the entered length helper and expose the real root guard
state, without making a decision about the count. -/
theorem preparesFromEnteredLengthOfActiveSlice
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame)
    (caller frame : CompilerFrameContext.ActualFrame)
    (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64) (carrierValid : SliceCarrier.Valid machine carrier len)
    (size : frame.locals.size = 3)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some SharedReferenceMetadata.sharedLayout)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead) (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (body : frame.body = SliceLenFacts.body.body) (identity : frame.bodyIdentity = SliceLenFacts.body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) (located : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker) (defaultMode : tracker.retagMode = .Default)
    (noRace : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).entries.any (·.value.ty == 2) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < (frames.push caller).size+1)
    (borrowFrame : FrameState) (ownedFrame : frame.extra.borrowTracker = some borrowFrame)
    (count : UInt64)
    (root : RetainedSlice initial)
    (before : BeforeLengthReturn caller count)
    (callerLive : (caller.locals[11]'(by rw [before.size]; decide)).value = .live (.immediate .uninit))
    (returnPlace : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout)
    (resume : frame.returnContinuation = .goto (some 3) .Unreachable) (varargs : frame.vaList = #[])
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : machine.memory.live[root.id]? = some entry)
    (previous read : BorrowTree) (shared child : UniIndex) (tag : BorTag)
    (offset length : Size) (inside : DedupRangeMap Tree.LocationState)
    (created : SharedChildFrame previous read entry.allocation.extra shared child tag offset length inside)
    (ownedTags : borrowFrame.protectedTags = #[(root.id, tag)])
    (coherent : CoherentForest entry.allocation.extra)
    (roots : entry.allocation.extra.roots = #[root.root])
    (indexed : entry.allocation.extra.indexOfTag tag = some child)
    (node : TreeNode) (found : entry.allocation.extra.nodeAt child = some node) (tagged : node.tag = tag)
    (holderPresent : ∃ data, previous.nodeAt root.source = some data)
    (lineage : Ancestor previous root.source shared)
    (unheld : ∀ index data, previous.nodeAt index = some data → Ancestor previous index shared →
      ¬ Ancestor previous index root.source → (tracker.global.protectedTags.remove tag).contains data.tag = false)
    (fresh : ∀ index data, previous.nodeAt index = some data → data.tag ≠ tag)
    (extent : ∀ segment ∈ inside.iterAll.toList, segment.range.stop.toNat ≤ length.bytes.toNat)
    (readRights : ∀ point : UInt64, offset.bytes.toNat ≤ point.toNat →
      point.toNat < (offset.bytes + length.bytes).toNat → ∀ row, ValueAt entry.allocation.extra.locations point row →
        LocationAccessRights entry.allocation.extra row tracker.global.protectedTags child .Read)
    (holderRights : OwnedOn (fun row => LocationRights read row (tracker.global.protectedTags.remove tag) root.source)
      offset.bytes (offset.bytes + length.bytes) read.locations)
    (holderExtent : AccessedWithin entry.allocation.extra root.source offset.bytes (offset.bytes + length.bytes))
    (holderIndex : entry.allocation.extra.indexOfTag root.tag = some root.source)
    (holderNode : TreeNode) (holderFound : entry.allocation.extra.nodeAt root.source = some holderNode)
    (holderUnexposed : holderNode.isExposed = false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let callerBound : 11 < caller.locals.size := by rw [before.size]; decide
    let resumed := {writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 len))) callerBound with
      location := FrameLocation.mir ⟨3, 0⟩}
    ∃ finalMachine, SuccessfulTrace.Trace config limits
      (Storage.withCurrent (frames.push caller) frame machine)
      (Storage.withCurrent frames resumed finalMachine) ∧
      Nonempty (LengthBranchOfActiveSlice config initial machine root entry entry.allocation.extra child
        offset.bytes (offset.bytes + length.bytes) len count resumed finalMachine) ∧
      (caller.extra.userRelevance = 255 →
        (thread.topUserRelevantFrame = some frames.size ∨
          thread.topUserRelevantFrame = some (frames.push caller).size) →
        ∃ currentThread, finalMachine.threads.activeThread? = some currentThread ∧
          currentThread.topUserRelevantFrame = some frames.size) ∧
      finalMachine.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} := by
  let callerBound : 11 < caller.locals.size := by rw [before.size]; decide
  obtain ⟨releasedTree, exactGraph, coherentFinal, rangesSame, rights, vacant, scopeRetained, release⟩ :=
    created.releaseHolderWithFrame tracker.global.protectedTags coherent roots indexed node found tagged
      holderPresent lineage unheld fresh extent readRights holderRights
  have reader := ownership_from_bytes entry.allocation.extra.locations offset.bytes (offset.bytes + length.bytes)
    coherent.ranges _ readRights
  have sourceRelease := sharedReleaseFramesForeign entry.allocation.extra tracker.global.protectedTags tag child root.root node
    found (created.unexposed node found) indexed coherent roots offset.bytes (offset.bytes+length.bytes)
    (created.extent extent).1 (created.extent extent).2 created.frozen reader
  obtain ⟨observed, outcome, _, _, _, outside, foreignRows⟩ := sourceRelease
  have exactRelease := (release (· = releasedTree) (fun _ _ => False)).mpr rfl
  have finished : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags = ⟨releasedTree, .Released⟩ := by
    have fact := (Miri.Verification.ProtectorReleaseWP.releasePre_iff tag tracker.global.protectedTags
      (· = releasedTree) (fun _ _ => False) entry.allocation.extra).mp exactRelease
    rw [outcome] at fact
    exact outcome.trans (congrArg (fun tree => BorrowTree.ProtectorReleaseResult.mk tree .Released) fact)
  have same : observed = releasedTree :=
    congrArg BorrowTree.ProtectorReleaseResult.tree (outcome.symm.trans finished)
  subst observed
  let memory := StackPopRelease.commitTree machine.memory root.id entry releasedTree
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory memory := by
    rw [ownedTags]
    have checked := (release (· = releasedTree) (fun _ _ => False)).mpr rfl
    exact ActiveRelease.planSingleOfRelease machine.memory root.id entry present tag tracker.global.protectedTags releasedTree checked
  obtain ⟨final, leading, finalHeap, finalTracker, finalGhost, finalShallow, finalFixed,
      finalUnchecked, finalGc, finalActive, stable, topAfter⟩ :=
    SliceLenCompleteCurrent.returnsLengthObserved options limits remaining budget dispatchFuel span debug fuel validationFuel
      frames caller frame machine carrier len carrierValid size live0 uncached0 live1 cached1 dead2 uncached2
      body identity callee located noClocks tracker tracked defaultMode noRace backend ghost shallow dynamicFuel dynamicEq source
      cmp metadata notConstructed unchecked noGc fixed thread active cacheBound borrowFrame ownedFrame memory plan
      11 callerBound callerLive before.cached11 before.noClocks returnPlace 3 .Unreachable resume varargs
  have indexedAfter : releasedTree.indexOfTag root.tag = some root.source := by
    rw [exactGraph]
    exact holderIndex
  have rootsAfter : releasedTree.roots = #[root.root] := by rw [exactGraph]; exact roots
  have holderAfter : releasedTree.nodeAt root.source = some holderNode := by
    rw [exactGraph]
    exact holderFound
  let ready : RetainedSlice final :=
    { id := root.id
      tag := root.tag
      entry := {entry with allocation := entry.allocation.setExtra releasedTree}
      present := by rw [finalHeap]; simp [memory,StackPopRelease.commitTree]
      tracker := {tracker with global := tracker.global.endCall borrowFrame}
      tracked := finalTracker
      source := root.source
      root := root.root
      indexed := indexedAfter
      roots := rootsAfter
      node := holderNode
      found := holderAfter
      unexposed := holderUnexposed
      thread := finalActive.choose
      active := finalActive.choose_spec }
  let post := before.rejectionEntry caller final len count finalGhost finalShallow finalFixed
  have protectionEq : (tracker.global.endCall borrowFrame).protectedTags = tracker.global.protectedTags.remove tag := by
    unfold TreeBorrows.GlobalState.endCall
    rw [ownedTags]
    rfl
  have retainedAccess : OwnedOn (fun row => LocationRights ready.entry.allocation.extra row
      ready.tracker.global.protectedTags ready.source) offset.bytes (offset.bytes + length.bytes) ready.entry.allocation.extra.locations := by
    change OwnedOn (fun row => LocationRights releasedTree row (tracker.global.endCall borrowFrame).protectedTags root.source)
      offset.bytes (offset.bytes + length.bytes) releasedTree.locations
    rw [protectionEq]
    exact rights
  let branch : LengthBranchOfActiveSlice (PreparedContracts.actualConfig options () (remaining+1) span)
      initial machine root entry entry.allocation.extra child offset.bytes (offset.bytes + length.bytes) len count _ final := {
    guard := post
    ready := ready
    id := rfl
    source := rfl
    tag := rfl
    origin := rfl
    allocationData := rfl
    graph := exactGraph
    rangeCapacity := rangesSame
    coherence := coherentFinal
    writable := retainedAccess
    activeScope := activeFromOutside outside holderExtent
    releaseOutside := outside
    releaseForeign := foreignRows
    vacant := vacant
    stable := stable
    unrelated := by
      intro key different
      rw [finalHeap]
      simp [memory, StackPopRelease.commitTree, Std.ExtTreeMap.getElem?_insert, Ne.symm different]
    defaultMode := defaultMode
    gc := finalGc
    unchecked := finalUnchecked }
  exact ⟨final, leading, ⟨branch⟩, topAfter, finalTracker⟩

#print axioms preparesFromEnteredLengthOfActiveSlice
end DuplicatePrefix.RootZeroShallowReturn

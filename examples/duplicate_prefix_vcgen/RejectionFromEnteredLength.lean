import RetainedRootAfterLength
import duplicate_prefix.SliceLenCompleteCurrent
import duplicate_prefix.SharedReborrowContinuity

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.DataStructures Miri.Concurrency
open PtrMetadataExecution PtrMetadataHelper PtrMetadataComplete MetadataUncachedCall
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins RetagReleaseFootprint
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Starting at the entered length helper, execute its actual return and
the rejected branch, including both active protector releases. -/
theorem rejectionFromEnteredLength
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame)
    (outsideCaller caller frame anchor : CompilerFrameContext.ActualFrame)
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
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent ((older.push outsideCaller).push caller) frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent ((older.push outsideCaller).push caller) frame machine)).entries.any (·.value.ty == 2) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < ((older.push outsideCaller).push caller).size+1)
    (borrowFrame : FrameState) (ownedFrame : frame.extra.borrowTracker = some borrowFrame)
    (count : UInt64) (rejected : count > len / 2)
    (root : ActiveCaller older outsideCaller anchor initial)
    (before : BeforeLengthReturn caller count)
    (continuation : caller.returnContinuation = anchor.returnContinuation)
    (destination : caller.returnPlace = anchor.returnPlace)
    (arguments : caller.vaList = anchor.vaList)
    (ownership : caller.extra.borrowTracker = anchor.extra.borrowTracker)
    (callerLive : (caller.locals[11]'(by rw [before.size]; decide)).value = .live (.immediate .uninit))
    (returnPlace : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace (older.push outsideCaller).size caller 11 RootCompilerFacts.usizeLayout)
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
    (holderExtent : MaterializedWithin entry.allocation.extra root.source offset.bytes (offset.bytes + length.bytes))
    (holderIndex : entry.allocation.extra.indexOfTag root.tag = some root.source)
    (holderNode : TreeNode) (holderFound : entry.allocation.extra.nodeAt root.source = some holderNode)
    (holderUnexposed : holderNode.isExposed = false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ finalMachine, SuccessfulTrace.Trace config limits
      (Storage.withCurrent ((older.push outsideCaller).push caller) frame machine)
      (Storage.withCurrent older {putBool outsideCaller root.destinationIndex root.destinationBound false with
        location := .mir ⟨root.target, 0⟩} finalMachine) := by
  let callerBound : 11 < caller.locals.size := by rw [before.size]; decide
  obtain ⟨releasedTree, exactGraph, coherentFinal, _, rights, vacant, scopeRetained, release⟩ :=
    created.releaseHolderWithFrame tracker.global.protectedTags coherent roots indexed node found tagged
      holderPresent lineage unheld fresh extent readRights holderRights
  let memory := StackPopRelease.commitTree machine.memory root.id entry releasedTree
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory memory := by
    rw [ownedTags]
    have checked := (release (· = releasedTree) (fun _ _ => False)).mpr rfl
    exact ActiveRelease.planSingleOfRelease machine.memory root.id entry present tag tracker.global.protectedTags releasedTree checked
  obtain ⟨final, leading, finalHeap, finalTracker, finalGhost, finalShallow, finalFixed,
      finalUnchecked, finalGc, finalActive⟩ :=
    SliceLenCompleteCurrent.returnsLengthWithPlan options limits remaining budget dispatchFuel span debug fuel validationFuel
      (older.push outsideCaller) caller frame machine carrier len carrierValid size live0 uncached0 live1 cached1 dead2 uncached2
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
  let retained := RetainedRootBorrow.ofLengthRelease older outsideCaller anchor initial machine final root
    entry releasedTree tracker borrowFrame tag ownedTags finalHeap finalTracker indexedAfter rootsAfter holderNode holderAfter
    holderUnexposed coherentFinal offset.bytes (offset.bytes + length.bytes) (scopeRetained _ holderExtent) vacant rights
  let ready := ActiveCaller.afterLengthReturn older outsideCaller anchor caller initial final len count before root
    continuation destination arguments ownership retained finalActive
  let post := before.rejectionEntry caller final len count finalGhost finalShallow finalFixed
  obtain ⟨out, tail⟩ := executesRejectionReturn options limits remaining span source debug fuel validationFuel
    older outsideCaller _ final len count rejected post ready defaultMode finalGc finalUnchecked
  exact ⟨out, SuccessfulTrace.append leading tail⟩

#print axioms rejectionFromEnteredLength
end DuplicatePrefix.RootZeroShallowReturn

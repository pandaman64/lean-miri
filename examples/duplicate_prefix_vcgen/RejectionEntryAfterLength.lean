import RootRejectedAfterLen
import duplicate_prefix.PtrMetadataExecution

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.DataStructures Miri.Concurrency
open PtrMetadataExecution

/-- The caller shape before the retained slice-length call returns to block 3. -/
structure BeforeLengthReturn (frame : CompilerFrameContext.ActualFrame) (count : UInt64) where
  size : frame.locals.size = 25
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  temp : Immediate Provenance
  slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩
  live7 : (frame.locals[7]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  slot8 : frame.locals[8]? = some ⟨.live (.immediate .uninit), none⟩
  slot9 : frame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
    some RootCompilerFacts.usizeLayout⟩
  slot10 : frame.locals[10]? = some ⟨.live (.immediate .uninit), none⟩
  cached11 : (frame.locals[11]'(by rw [size]; decide)).layout = some RootCompilerFacts.usizeLayout
  live12 : (frame.locals[12]'(by rw [size]; decide)).value = .live (.immediate temp)
  slot13 : frame.locals[13]? = some ⟨.live (.immediate .uninit), none⟩
  immediate : ZeroImmediateFacts.AllImmediate frame
  noClocks : frame.extra.dataRace = none

private theorem someSlot {frame : CompilerFrameContext.ActualFrame} {i : Nat}
    (inside : i < frame.locals.size) {slot : LocalState Provenance LocalLayout}
    (found : frame.locals[i]? = some slot) : frame.locals[i] = slot :=
  Option.some.inj ((Array.getElem?_eq_getElem inside).symm.trans found)

def BeforeLengthReturn.rejectionEntry (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (length count : UInt64)
    (before : BeforeLengthReturn frame count)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true) :
    RejectionEntry
      {writeFrame frame 11 (.scalar (.fromScalarInt (.ofUInt64 length)))
        (by rw [before.size]; decide) with location := .mir ⟨3, 0⟩} machine length count := by
  have bound : 11 < frame.locals.size := by rw [before.size]; decide
  have l0 := someSlot (by rw [before.size]; decide) before.slot0
  have l8 := someSlot (by rw [before.size]; decide) before.slot8
  have l9 := someSlot (by rw [before.size]; decide) before.slot9
  have l10 := someSlot (by rw [before.size]; decide) before.slot10
  have l13 := someSlot (by rw [before.size]; decide) before.slot13
  refine {
    body := before.body
    identity := before.identity
    callee := before.callee
    location := rfl
    size := by simp [writeFrame, before.size]
    temp := before.temp
    live12 := ?_
    live13 := ?_
    cache13 := ?_
    live0 := ?_
    cache0 := ?_
    live7 := ?_
    live8 := ?_
    cache8 := ?_
    live9 := ?_
    cache9 := ?_
    live10 := ?_
    cache10 := ?_
    live11 := ?_
    cache11 := ?_
    immediate := ?_
    noClocks := before.noClocks
    ghost := ghost
    shallow := shallow
    fixed := fixed }
  all_goals
    first
    | exact ZeroImmediateFacts.all_immediate_set frame 11 _ bound before.immediate (by simp)
    | simp [writeFrame, Array.getElem_set, l0, l8, l9, l10, l13,
        before.live7, before.live12, before.cached11]

private theorem relevanceExists (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    ∃ relevant, FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some relevant := by
  cases cached : thread.topUserRelevantFrame with
  | some index => exact ⟨index, by simp [FrameRelevance.top]⟩
  | none => exact ⟨frames.size, by simp [FrameRelevance.top]⟩

/-- Structural release authority for the root, after a nested Len protector
has been released. The nested pop may update the tree and relevance cache. -/
structure RetainedRootBorrow (older : Array CompilerFrameContext.ActualFrame)
    (caller frame : CompilerFrameContext.ActualFrame)
    (initial final : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (root : ActiveCaller older caller frame initial) where
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  present : final.memory.live[root.id]? = some entry
  tracker : MachineHooks.BorrowState
  tracked : final.borrowTracker = some tracker
  indexed : entry.allocation.extra.indexOfTag root.tag = some root.source
  roots : entry.allocation.extra.roots = #[root.root]
  depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes
  children : GeneralBorrowGraph.ChildNodes entry.allocation.extra
  node : TreeNode
  found : entry.allocation.extra.nodeAt root.source = some node
  unexposed : node.isExposed = false
  authorized : ∀ position < entry.allocation.extra.locations.entries.size, ∃ slot,
    entry.allocation.extra.locations.index position = .ok slot ∧
      ActiveRelease.ReleaseOwnership entry.allocation.extra root.source root.root tracker.global.protectedTags slot

noncomputable def ActiveCaller.afterLengthReturn
    (older : Array CompilerFrameContext.ActualFrame) (caller anchor frame : CompilerFrameContext.ActualFrame)
    (initial final : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length count : UInt64) (before : BeforeLengthReturn frame count)
    (root : ActiveCaller older caller anchor initial)
    (continuation : frame.returnContinuation = anchor.returnContinuation)
    (destination : frame.returnPlace = anchor.returnPlace)
    (varargs : frame.vaList = anchor.vaList)
    (ownership : frame.extra.borrowTracker = anchor.extra.borrowTracker)
    (retained : RetainedRootBorrow older caller anchor initial final root)
    (running : ∃ thread, final.threads.activeThread? = some thread) :
    ActiveCaller older caller
      {writeFrame frame 11 (.scalar (.fromScalarInt (.ofUInt64 length)))
        (by rw [before.size]; decide) with location := .mir ⟨3, 0⟩} final := by
  let thread := Classical.choose running
  have active := Classical.choose_spec running
  let returned := {writeFrame frame 11 (.scalar (.fromScalarInt (.ofUInt64 length)))
    (by rw [before.size]; decide) with location := FrameLocation.mir ⟨3, 0⟩}
  let top := relevanceExists (older.push caller) returned thread
  exact {
    target := root.target
    unwind := root.unwind
    continuation := continuation.trans root.continuation
    destinationIndex := root.destinationIndex
    destinationBound := root.destinationBound
    destinationSlot := root.destinationSlot
    destinationLive := root.destinationLive
    destinationCached := root.destinationCached
    destination := destination.trans root.destination
    callerClocks := root.callerClocks
    varargs := varargs.trans root.varargs
    id := root.id
    tag := root.tag
    entry := retained.entry
    present := retained.present
    tracker := retained.tracker
    tracked := retained.tracked
    owned := root.owned
    ownership := ownership.trans root.ownership
    ownedTags := root.ownedTags
    source := root.source
    root := root.root
    indexed := retained.indexed
    roots := retained.roots
    depth := retained.depth
    children := retained.children
    node := retained.node
    found := retained.found
    unexposed := retained.unexposed
    authorized := retained.authorized
    thread := thread
    relevant := Classical.choose top
    active := active
    relevance := Classical.choose_spec top }

#print axioms BeforeLengthReturn.rejectionEntry
#print axioms ActiveCaller.afterLengthReturn
end DuplicatePrefix.RootZeroShallowReturn

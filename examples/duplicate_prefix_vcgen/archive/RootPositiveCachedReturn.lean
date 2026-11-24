import RootZeroShallowReturn
import duplicate_prefix.RootPositiveRootSuffix
import duplicate_prefix.RootCopiedHolderAuthorization

namespace DuplicatePrefix.RootPositiveCachedReturn

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PreparedArguments SourceDomain CopyHolderRights

set_option maxRecDepth 65536
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

abbrev Frame := CompilerFrameContext.ActualFrame
abbrev MachineState := MachineHooks.MachineState MiriMemoryKind Machine.RootUser

structure CallerSlot (older : Array Frame) (caller entry : Frame) where
  target : BasicBlockId
  unwind : UnwindAction
  index : MIR.LocalId
  valid : index < caller.locals.size
  old : Immediate Provenance
  live : caller.locals[index].value = .live (.immediate old)
  cached : caller.locals[index].layout = some RootCompilerFacts.boolLayout
  clocks : caller.extra.dataRace = none
  continuation : entry.returnContinuation = .goto (some target) unwind
  place : entry.returnPlace =
    .frameLocal older.size index none RootCompilerFacts.boolLayout caller.localsIdentity

/-- Structural evidence for the original mutable slice holder in the
post-retag tree used for the actual prefix copy. -/
structure Holder
    (tree : BorrowTree) (tags : ProtectedTags) (copyTag : BorTag) (source : UniIndex)
    (start : Size) (length : UInt64) where
  root : UniIndex
  roots : tree.roots = #[root]
  sourceNode : TreeNode
  atSource : tree.nodeAt source = some sourceNode
  atCopyTag : tree.indexOfTag copyTag = some source
  tag : BorTag
  index : UniIndex
  node : TreeNode
  atHolder : tree.nodeAt index = some node
  atHolderTag : tree.indexOfTag tag = some index
  unexposed : node.isExposed = false
  coherent : CoherentForest tree
  lineage : Ancestor tree index source
  unheld : ∀ candidate data, tree.nodeAt candidate = some data →
    Ancestor tree candidate source → ¬ Ancestor tree candidate index → tags.contains data.tag = false
  fits : start.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat
  retained : Footprint tree tags source index start.bytes (start.bytes + length)

/-- Use the retained mutable holder to release the actual root frame's
protector and copy the emitted true result into its suspended caller. -/
theorem returns
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1)
    (older : Array Frame) (caller frame result done : Frame)
    (machine last : MachineState) (length count base : UInt64) (copyTag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent (older.push caller) frame machine) length)
    (rights : ExclusiveRegion (Storage.withCurrent (older.push caller) frame machine) length storage copyTag)
    (holder : Holder storage.entry.allocation.extra rights.tracker.global.protectedTags copyTag rights.source
      storage.relativeStart length)
    (disjoint : count.toNat + count.toNat ≤ length.toNat)
    (allocation : Allocation Provenance BorrowTree)
    (after : RootPositiveRootSuffix.ReadyAfterCopy options remaining span (older.push caller) frame machine
      length count base copyTag storage rights result last allocation)
    (cleanup : RootSuccessCleanupFacts.Shape result done RootCompilerFacts.boolLayout (.scalar (.fromBool true)))
    (slot : CallerSlot older caller frame)
    (body : result.body = RootBody.reflected.body.body)
    (clocks : frame.extra.dataRace = none)
    (varargs : frame.vaList = #[])
    (owned : FrameState) (ownership : frame.extra.borrowTracker = some owned)
    (ledger : owned.protectedTags = #[(storage.id, holder.tag)]) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let resumed := {RootZeroShallowReturn.putBool caller slot.index slot.valid true with location := .mir ⟨slot.target,0⟩}
    let start := Storage.withCurrent (older.push caller) {done with location := .mir ⟨10,0⟩}
      (SourceControl.accounted config.terminators (Storage.withCurrent (older.push caller) done last)).machine
    ∃ popped, ExecutionMachine.step config limits () start = (Storage.withCurrent older resumed popped,.ok true) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let clean := {done with location := .mir ⟨10,0⟩}
  let machine10 := LanguageZeroStep.accountedMachine options remaining span last
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨storage.entry.kind,allocation⟩
  have counted := CopyRootGuardState.accounted_fields options remaining span last
  obtain ⟨indexed, roots, ⟨depth⟩, children, found, unexposed, authorized⟩ :=
    RootCopiedHolderAuthorization.authorize storage.entry.allocation.extra rights.tracker.global.protectedTags
      copyTag holder.tag rights.source holder.index holder.root storage.relativeStart count length disjoint
      holder.coherent holder.sourceNode holder.node holder.atSource holder.atHolder holder.unexposed holder.roots
      holder.atCopyTag holder.atHolderTag holder.lineage holder.unheld holder.fits holder.retained
  have tree_eq := after.copiedTree
  change allocation.extra = _ at tree_eq
  have indexed' : allocation.extra.indexOfTag holder.tag = some holder.index := by rw [tree_eq]; exact indexed
  have roots' : allocation.extra.roots = #[holder.root] := by rw [tree_eq]; exact roots
  have depth' : GeneralBorrowExposure.ParentDepth allocation.extra.nodes := by rw [tree_eq]; exact depth
  have children' : GeneralBorrowGraph.ChildNodes allocation.extra := by rw [tree_eq]; exact children
  have found' : allocation.extra.nodeAt holder.index = some holder.node := by rw [tree_eq]; exact found
  have permitted : ∀ position < allocation.extra.locations.entries.size, ∃ region,
      allocation.extra.locations.index position = .ok region ∧
      ActiveRelease.ReleaseOwnership allocation.extra holder.index holder.root rights.tracker.global.protectedTags region := by
    rw [tree_eq]
    exact authorized
  obtain ⟨thread, active⟩ := after.active
  let ready : RootZeroShallowReturn.ActiveCaller older caller clean machine10 :=
    { target := slot.target
      unwind := slot.unwind
      continuation := cleanup.continuation.trans (after.returnContinuation.trans slot.continuation)
      destinationIndex := slot.index
      destinationBound := slot.valid
      destinationSlot := slot.old
      destinationLive := slot.live
      destinationCached := slot.cached
      destination := cleanup.destination.trans (after.returnPlace.trans slot.place)
      callerClocks := slot.clocks
      varargs := cleanup.varargs.trans (after.varargs.trans varargs)
      id := storage.id
      tag := holder.tag
      entry := entry
      present := by unfold machine10; rw [counted.1]; exact after.present
      tracker := rights.tracker
      tracked := counted.2.1.trans after.tracker
      owned := owned
      ownership := (congrArg MachineHooks.FrameExtra.borrowTracker (cleanup.extra.trans after.extra)).trans ownership
      ownedTags := ledger
      source := holder.index
      root := holder.root
      indexed := indexed'
      roots := roots'
      depth := depth'
      children := children'
      node := holder.node
      found := found'
      unexposed := unexposed
      authorized := permitted
      thread := thread
      relevant := thread.topUserRelevantFrame.getD (older.push caller).size
      active := by unfold machine10; rw [counted.2.2.1]; exact active
      relevance := GenericPopFrame.top_nonempty (older.push caller) clean thread.topUserRelevantFrame }
  have countControl : cfg.terminators.getControl machine10.user = TerminatorClock.advance (cfg.terminators.getControl last.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have unchecked : (cfg.terminators.getControl machine10.user).checkedArithmetic = false := by
    rw [countControl]
    exact after.unchecked
  have noGc : (cfg.terminators.getControl machine10.user).gcInterval = 0 := by
    rw [countControl]
    exact after.noGc
  have fixed : machine10.threads.fixedScheduling = true := by unfold machine10; rw [counted.2.2.1]; exact after.fixed
  have valid0 : (0 : MIR.LocalId) < clean.locals.size := by change 0 < done.locals.size; rw [cleanup.size]; decide
  have retval : clean.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    (Array.getElem?_eq_some_iff.mp cleanup.output).2
  exact RootZeroShallowReturn.stepReturnToCaller options limits remaining span debug fuel validation true older caller clean machine10 ready
    (cleanup.body.trans body) rfl valid0 (by rw [retval]) (by rw [retval])
    (by change done.extra.dataRace = none; rw [cleanup.extra,after.extra]; exact clocks)
    (cleanup.immediate after.direct) (counted.2.2.2.2.2.1.trans after.ghost)
    (counted.2.2.2.2.2.2.1.trans after.shallow) fixed noGc unchecked

#print axioms returns
end DuplicatePrefix.RootPositiveCachedReturn

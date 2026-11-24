import ProtectedTagFresh
import duplicate_prefix.EmptyBackedShared
import duplicate_prefix.EmptyBackedRootLenCall
import duplicate_prefix.EmptySharedCapacity
import duplicate_prefix.EmptyIntegerLength

namespace DuplicatePrefix.EmptyBackedLength
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.DataStructures Miri.Concurrency
open ArchiveForestProjection CanonicalConfigFacts EmptyReferenceAllocation RetagSharedChild Miri.Verification.MutableRetagFootprint
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev Frame := CompilerFrameContext.ActualFrame
abbrev MachineState := MachineHooks.MachineState MiriMemoryKind Machine.RootUser

def sharedFrame (frame : Frame) (valid : 12 < frame.locals.size)
    (arithmetic : TargetDataLayout) (id : AllocId) (tag : BorTag) (address : UInt64) :=
  CopyHelperSteps.advance
    (ActualLocalCopy.written frame 12 SharedReferenceMetadata.sharedLayout valid
      (RetagReferencePlace.sliceValue arithmetic (Pointer.new (.concrete id tag) (Size.ofBytes address)) 0
        SharedReferenceMetadata.sharedLayout).imm) ⟨2,11⟩

/-- Backed zero-width shared references attach actual dormant children at each
retag. The retained helper returns zero, releases its protector, and retains
the exact backed tree in memory. -/
theorem returns_length
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (source : PreparedContracts.SourceComparator)
    (dynamicFuel fuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = fuel+1)
    (older : Array Frame) (frame : Frame) (machine : MachineState)
    (base offset : UInt64) (nonNull : base + offset ≠ 0)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (parentTag : BorTag)
    (found : machine.memory.live[id]? = some entry)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (parent : UniIndex) (parentNode : TreeNode)
    (parentKey : entry.allocation.extra.indexOfTag parentTag = some parent)
    (parentPresent : entry.allocation.extra.nodeAt parent = some parentNode)
    (parentTagEq : parentNode.tag = parentTag) (parentHidden : parentNode.isExposed = false)
    (parentDormant : ∀ pos (valid : pos < entry.allocation.extra.locations.entries.size),
      entry.allocation.extra.locations.entries[pos].data.perms.get parent = none)
    (forest : SourceDomain.CoherentForest entry.allocation.extra)
    (capacity : RetagInsertionCapacity.Ready entry.allocation.extra)
    (space : entry.allocation.extra.nodes.size + 2 < 2^32)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨2,11⟩)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (freshAgain : (allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (monotone : (allocatedTracker tracker fresh).global.nextPointerTag.value > tracker.global.nextPointerTag.value)
    (unprotectedNext : tracker.global.protectedTags.contains (allocatedTracker tracker fresh).global.nextPointerTag = false)
    (oldTags : ∀ index node, entry.allocation.extra.nodeAt index = some node →
      node.tag.value < tracker.global.nextPointerTag.value)
    (valid1 : 1 < frame.locals.size) (valid11 : 11 < frame.locals.size) (valid12 : 12 < frame.locals.size)
    (arg : frame.locals[1] = ⟨.live (.immediate
      (RetagReferencePlace.sliceValue
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 EmptyReferenceMetadata.reference).imm), some EmptyReferenceMetadata.reference⟩)
    (dest11 : frame.locals[11] = ⟨.live (.immediate .uninit),none⟩)
    (dest12 : frame.locals[12] = ⟨.live (.immediate .uninit),none⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (cacheBound : ∀ index, thread.topUserRelevantFrame = some index → index < older.size + 1)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 2) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let afterReference := sharedFrame frame valid12
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base id tracker.global.nextPointerTag (base+offset)
    let afterLength := LenCallResultFrame.resultFrame afterReference
      (by simpa [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using valid11) 0
    ∃ after newEntry,
      after.memory.live[id]? = some newEntry ∧
      (∀ key, key ≠ id → after.memory.live[key]? = machine.memory.live[key]?) ∧
      newEntry.allocation.extra.indexOfTag parentTag = some parent ∧
      (∃ node, newEntry.allocation.extra.nodeAt parent = some node ∧ node.isExposed = false) ∧
      (∀ pos (valid : pos < newEntry.allocation.extra.locations.entries.size),
        newEntry.allocation.extra.locations.entries[pos].data.perms.get parent = none) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent older frame machine) (Storage.withCurrent older afterLength after) ∧
      after.borrowTracker = some (allocatedTracker (allocatedTracker tracker fresh) freshAgain) ∧
      after.user.payload.ghost = false ∧ after.user.payload.validation = .Shallow ∧
      after.dataRace = none ∧ after.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).gcInterval = 0 ∧
      after.user.addresses = machine.user.addresses ∧
      after.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      after.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      after.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      ∃ threadAfter, after.threads.activeThread? = some threadAfter := by
  let afterReference := sharedFrame frame valid12
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base id tracker.global.nextPointerTag (base+offset)
  let original := entry.allocation.extra
  change original.nodes.size + 2 < 2^32 at space
  let tag₁ := tracker.global.nextPointerTag
  let once := allocatedTracker tracker fresh
  let tag₂ := once.global.nextPointerTag
  let inside := DedupRangeMap.new Size.ZERO sharedState
  have firstTag : original.indexOfTag tag₁ = none := by
    unfold BorrowTree.indexOfTag UniKeyMap.get
    have missing : original.tagMapping.mapping.find? (fun e => e.1 == tag₁) = none := by
      apply Array.find?_eq_none.mpr
      intro key member same
      obtain ⟨node, selected, identity⟩ := capacity.keys key member
      have old := oldTags key.2 node selected
      have new := identity.trans (beq_iff_eq.mp same)
      rw [new] at old
      exact (UInt64.lt_irrefl _ old)
    rw [missing]
    rfl
  have aligned (empty : original.tagMapping.deassigned.back? = none) :
      original.tagMapping.mapping.size = original.nodes.size := by
    have noFree := Array.back?_eq_none_iff.mp empty
    have balance : original.tagMapping.mapping.size + original.tagMapping.deassigned.size = original.nodes.size := capacity.balanced
    simpa [noFree] using balance
  have room (empty : original.tagMapping.deassigned.back? = none) : original.tagMapping.mapping.size ≤ 4294967295 := by
    rw [aligned empty]
    have h : original.nodes.size < 2^32 := capacity.headroom
    omega
  have oldReuse : ∀ index, original.tagMapping.deassigned.back? = some index →
      index.toNat < original.nodes.size ∧ original.nodeAt index = none :=
    fun index reused => capacity.free index (Array.mem_of_back? reused)
  have depthOf (tree : BorrowTree) (coherent : SourceDomain.CoherentForest tree) :=
    SourceDomain.CoherentForest.parentDepth coherent
  obtain ⟨depth, bounded, lower⟩ := depthOf original forest
  let depths : BorrowTree.ZeroProtection.ParentDepth original.nodes :=
    ⟨depth,bounded,fun index node old loc edge => by
      obtain ⟨last, prior⟩ := forest.parentPresent index node loc old edge
      exact ⟨last, prior, lower index node loc old edge⟩⟩
  obtain ⟨tight, below⟩ := BorrowTree.ZeroProtection.ParentDepth.tight original.nodes depths
  obtain ⟨map₁,index₁,installed₁,finished₁,key₁,roots₁,forest₁, ⟨node₁,present₁,open₁⟩,framed₁⟩ :=
    EmptySharedTree.attach original (Size.ofBytes offset) parentTag tag₁ parent parentNode
      parentKey parentPresent firstTag room aligned oldReuse forest tight (below parent parentNode parentPresent)
      capacity.rowVacant false
  let first := (original.newChild (Size.ofBytes offset) (.concrete parentTag) tag₁ inside .Frozen false).tree
  have vacancy₁ : original.nodeAt index₁ = none := by
    obtain ⟨m, i, eq, _, absent⟩ := RetagFrozenChild.select_slot original tag₁ firstTag room aligned oldReuse
    have same := congrArg (fun result => match result with | .Inserted _ idx => idx | _ => i) (eq.symm.trans installed₁)
    change i = index₁ at same
    exact same ▸ absent
  have clean := EmptySharedCapacity.preserveVacancy original (Size.ofBytes offset) parentTag tag₁ parent index₁
    parentNode map₁ false capacity installed₁ parentKey parentPresent vacancy₁ finished₁ framed₁
  have enough : original.nodes.size + 1 < 2^32 := by omega
  have nextReady : RetagInsertionCapacity.Ready first :=
    EmptySharedCapacity.preserves original (Size.ofBytes offset) parentTag tag₁ parent index₁ parentNode map₁
      inside false capacity enough firstTag installed₁ parentKey parentPresent vacancy₁ finished₁ clean
  have secondTag : first.indexOfTag tag₂ = none := by
    have different : tag₂ ≠ tag₁ := by
      intro eq
      have ordered : tag₂.value > tag₁.value := monotone
      rw [eq] at ordered
      exact UInt64.lt_irrefl _ ordered
    rw [show first.indexOfTag tag₂ = original.indexOfTag tag₂ from
      newChild_old_key original (Size.ofBytes offset) (.concrete parentTag) tag₁ tag₂ inside .Frozen false map₁ index₁ different installed₁]
    unfold BorrowTree.indexOfTag UniKeyMap.get
    have missing : original.tagMapping.mapping.find? (fun k => k.1 == tag₂) = none := by
      apply Array.find?_eq_none.mpr
      intro key member same
      obtain ⟨node, selected, identity⟩ := capacity.keys key member
      have old := oldTags key.2 node selected
      have new := identity.trans (beq_iff_eq.mp same)
      rw [new] at old
      exact UInt64.lt_asymm old monotone
    rw [missing]
    rfl
  have alignedNext (empty : first.tagMapping.deassigned.back? = none) :
      first.tagMapping.mapping.size = first.nodes.size := by
    have noFree := Array.back?_eq_none_iff.mp empty
    simpa [noFree] using nextReady.balanced
  have roomNext (empty : first.tagMapping.deassigned.back? = none) : first.tagMapping.mapping.size ≤ 4294967295 := by
    rw [alignedNext empty]
    have h := nextReady.headroom
    omega
  have reuseNext : ∀ index, first.tagMapping.deassigned.back? = some index →
      index.toNat < first.nodes.size ∧ first.nodeAt index = none :=
    fun index reused => nextReady.free index (Array.mem_of_back? reused)
  obtain ⟨depthNext, boundedNext, lowerNext⟩ := depthOf first forest₁
  let depthCert : BorrowTree.ZeroProtection.ParentDepth first.nodes :=
    ⟨depthNext,boundedNext,fun index node old loc edge => by
      obtain ⟨last, prior⟩ := forest₁.parentPresent index node loc old edge
      exact ⟨last, prior, lowerNext index node loc old edge⟩⟩
  obtain ⟨tightNext, belowNext⟩ := BorrowTree.ZeroProtection.ParentDepth.tight first.nodes depthCert
  obtain ⟨map₂, index₂, installed₂, finished₂, key₂, roots₂, forest₂, ⟨node₂,present₂,open₂⟩,framed₂⟩ :=
    EmptySharedTree.attach first (Size.ofBytes offset) tag₁ tag₂ index₁ node₁ key₁ present₁
      secondTag roomNext alignedNext reuseNext forest₁ tightNext (belowNext index₁ node₁ present₁) nextReady.rowVacant true
  let second := (first.newChild (Size.ofBytes offset) (.concrete tag₁) tag₂ inside .Frozen true).tree
  have noMaterialized := EmptySharedTree.childUnmaterialized first.locations index₂ second framed₂
  let firstEntry := {entry with allocation := entry.allocation.setExtra first}
  let retagged := {allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry first}
  have foundFirst : retagged.memory.live[id]? = some firstEntry := by
    simp [retagged, RetagEntry.updatedMemory, firstEntry]
  have preserved11 : 11 < afterReference.locals.size := by
    simpa [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using valid11
  have retained12 : 12 < afterReference.locals.size := by
    simpa [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using valid12
  have referenceStep :
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent older frame machine) = (Storage.withCurrent older afterReference retagged,.ok true) := by
    have result : original.newChild (Size.ofBytes offset) (.concrete parentTag) tag₁ inside .Frozen false = ⟨first,.ok ()⟩ := by
      cases computed : original.newChild (Size.ofBytes offset) (.concrete parentTag) tag₁ inside .Frozen false with
      | mk tree outcome =>
        change (original.newChild (Size.ofBytes offset) (.concrete parentTag) tag₁ inside .Frozen false).outcome = .ok () at finished₁
        rw [computed] at finished₁
        simp only [first, computed]
        exact congrArg (BorrowTree.ChildInsertResult.mk tree) finished₁
    have baseEq : (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base =
        (EmptyReferenceContext.config options remaining span).access.runtime.base := by
      rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
        CanonicalConfigFacts.actual_access_runtime options () remaining span]
    simpa only [afterReference, sharedFrame, retagged, baseEq, EmptyReferenceFacts.destination,
      EmptyReferenceFacts.location, EmptyReferenceInfo.layout, ite_true] using
      EmptyBackedShared.live_zero_statement options limits remaining span preciseOff implicitOff debug
      cmp dynamicFuel fuel dynamicEq validationFuel base offset parentTag id entry nonNull older frame machine
      body identity callee located tracker tracked mode fresh valid1 valid12 (congrArg LocalState.value arg)
      (congrArg LocalState.layout arg) (congrArg LocalState.value dest12) (congrArg LocalState.layout dest12)
      noClocks ghost shallow cachedAddress found first result metadata notConstructed
  have slot11 : afterReference.locals[11] = frame.locals[11] := by
    simp [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout,
      Array.getElem_set]
  obtain ⟨ctx⟩ := EmptyReferenceContext.exists_context options remaining span preciseOff implicitOff
  have done : first.newChild (Size.ofBytes offset) (.concrete tag₁) tag₂ inside .Frozen true = ⟨second,.ok ()⟩ := by
    cases computed : first.newChild (Size.ofBytes offset) (.concrete tag₁) tag₂ inside .Frozen true with
    | mk tree outcome =>
      change (first.newChild (Size.ofBytes offset) (.concrete tag₁) tag₂ inside .Frozen true).outcome = .ok () at finished₂
      rw [computed] at finished₂
      simp only [second, computed]
      exact congrArg (BorrowTree.ChildInsertResult.mk tree) finished₂
  obtain ⟨after, trace, memory, ledger, gh, sh, raceOff, fix, un, gc, addr, ty, be, ex, thread⟩ :=
    EmptyBackedRootLenCall.returns_zero options limits remaining budget dispatchFuel span ctx debug cmp dynamicFuel fuel
      dynamicEq validationFuel id firstEntry base offset tag₁ nonNull older afterReference retagged once rfl mode freshAgain
      cachedAddress foundFirst second done index₂ key₂ node₂ present₂ open₂ noMaterialized
      preserved11 ((congrArg LocalState.value slot11).trans (congrArg LocalState.value dest11))
      ((congrArg LocalState.layout slot11).trans (congrArg LocalState.layout dest11)) noClocks ghost shallow race
      thread active cacheBound metadata notConstructed body identity callee rfl source retained12
      (by
        have baseEq : (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base =
            (EmptyReferenceContext.config options remaining span).access.runtime.base := by
          rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
            CanonicalConfigFacts.actual_access_runtime options () remaining span]
        simp [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written,
          LocalPlaces.cachePlaceLayout, baseEq, tag₁])
      (by simp [afterReference, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout])
      backend unchecked noGc fixed
  let resultEntry := {entry with allocation := entry.allocation.setExtra second}
  have different₁ : parent ≠ index₁ := by
    intro same
    rw [same, vacancy₁] at parentPresent
    contradiction
  have vacancy₂ : first.nodeAt index₂ = none := by
    obtain ⟨m, i, eq, _, absent⟩ := RetagFrozenChild.select_slot first tag₂ secondTag roomNext alignedNext reuseNext
    have same := congrArg (fun result => match result with | .Inserted _ idx => idx | _ => i) (eq.symm.trans installed₂)
    change i = index₂ at same
    exact same ▸ absent
  have beforeTag := oldTags parent parentNode parentPresent
  have not₁ : parentTag ≠ tag₁ := by
    intro same
    rw [parentTagEq,same] at beforeTag
    exact UInt64.lt_irrefl _ beforeTag
  have not₂ : parentTag ≠ tag₂ := by
    intro same
    rw [parentTagEq,same] at beforeTag
    exact UInt64.lt_asymm beforeTag monotone
  have parentFirst : first.indexOfTag parentTag = some parent :=
    (newChild_old_key original (Size.ofBytes offset) (.concrete parentTag) tag₁ parentTag inside .Frozen false
      map₁ index₁ not₁ installed₁).trans parentKey
  have parentSecond : second.indexOfTag parentTag = some parent :=
    (newChild_old_key first (Size.ofBytes offset) (.concrete tag₁) tag₂ parentTag inside .Frozen true
      map₂ index₂ not₂ installed₂).trans parentFirst
  have older₁ := newChild_older_exposure original (Size.ofBytes offset) parentTag tag₁ parent index₁ parent map₁
    inside .Frozen false .Read rfl rfl rfl installed₁ parentKey parentNode parentPresent vacancy₁ different₁ finished₁
  have keptFirst : ∃ node, first.nodeAt parent = some node ∧ node.isExposed = false := by
    change (first.nodeAt parent).map TreeNode.isExposed = _ at older₁
    rw [parentPresent] at older₁
    cases picked : first.nodeAt parent with
    | none => simp [picked] at older₁
    | some node => exact ⟨node,rfl,by simpa [picked, parentHidden] using older₁⟩
  obtain ⟨prior, priorAt, priorHidden⟩ := keptFirst
  have different₂ : parent ≠ index₂ := by
    intro same
    rw [same, vacancy₂] at priorAt
    contradiction
  have older₂ := newChild_older_exposure first (Size.ofBytes offset) tag₁ tag₂ index₁ index₂ parent map₂
    inside .Frozen true .Read rfl rfl rfl installed₂ key₁ node₁ present₁ vacancy₂ different₂ finished₂
  have kept : ∃ node, second.nodeAt parent = some node ∧ node.isExposed = false := by
    change (second.nodeAt parent).map TreeNode.isExposed = _ at older₂
    rw [priorAt] at older₂
    cases picked : second.nodeAt parent with
    | none => simp [picked] at older₂
    | some node => exact ⟨node,rfl,by simpa [picked, priorHidden] using older₂⟩
  have cleanFirst := EmptySharedCapacity.preserveAbsentRow original.locations first index₁ parent different₁ framed₁ parentDormant
  have cleanSecond := EmptySharedCapacity.preserveAbsentRow first.locations second index₂ parent different₂ framed₂ cleanFirst
  refine ⟨after,resultEntry,?_,?_,parentSecond,kept,cleanSecond,.next referenceStep trace, ?_,
    gh, sh, raceOff, fix, un, gc, addr, ty, be, ex, thread⟩
  · rw [memory]
    simp [RetagEntry.updatedMemory, firstEntry, resultEntry, Allocation.setExtra, Allocation.mapExtra]
  · intro key other
    rw [memory]
    simp [retagged, RetagEntry.updatedMemory, Std.ExtTreeMap.getElem?_insert, Ne.symm other]
  · rw [ledger]
    simp only [EmptyBackedPointer.registeredTracker, EmptyBackedPointer.registeredGlobal,
      GlobalState.endCall, FrameState.addProtector, Array.foldl_push, Array.foldl_empty]
    have same : (((allocatedTracker once freshAgain).global.protectedTags).insert
        once.global.nextPointerTag .StrongProtector).remove once.global.nextPointerTag =
        (allocatedTracker once freshAgain).global.protectedTags :=
      ProtectedTags.remove_insert_of_absent _ _ _ unprotectedNext
    rw [same]

#print axioms returns_length
end
end DuplicatePrefix.EmptyBackedLength

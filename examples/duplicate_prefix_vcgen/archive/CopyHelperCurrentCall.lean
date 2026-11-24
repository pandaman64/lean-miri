import duplicate_prefix.AllocationBacktrace
import duplicate_prefix.GeneralBorrowScopedCopyHelperBody
import duplicate_prefix.CopyHelperReturnDriver
namespace DuplicatePrefix.CopyHelperCurrentCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem from_bb7
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨7,0⟩)
    (size : frame.locals.size = 17)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id, { weakMemory := none, backtrace := AllocationBacktrace.get (machine.user.payload.payload.user.runtime.extras.allocations) (id) }))
    (live : machine.memory.live[id]? = some ⟨kind, allocation⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (borrow : ScopedCopyAccess.Completed allocation.extra tracker.global.protectedTags tag offset n)

    (bounded : n ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (sourceLive : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (destLive : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+(offset+n))))))))
    (countLive : (frame.locals[3]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (sourceCached : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.sourcePointerLayout)
    (destCached : (frame.locals[2]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (countCached : (frame.locals[3]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate .uninit))
    (cached4 : (frame.locals[4]'(by omega)).layout = some CopyHelperUnit.layout)
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate (.scalar (.fromBool false))))
    (cached5 : (frame.locals[5]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (uncached14 : (frame.locals[14]'(by omega)).layout = none)
    (dead15 : (frame.locals[15]'(by omega)).value = .dead)
    (uncached15 : (frame.locals[15]'(by omega)).layout = none)
    (dead16 : (frame.locals[16]'(by omega)).value = .dead)
    (uncached16 : (frame.locals[16]'(by omega)).layout = none)
    (allImmediate : CopyHelperCleanup.AllImmediate frame)
    (localClocks : frame.extra.dataRace = none)
    (defaultMode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (zeroLive : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (zeroUncached : (frame.locals[0]'(by omega)).layout = none)
    (varargs : frame.vaList = #[])
    (borrowFrame : FrameState) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerOld : Immediate Provenance)
    (callerLive : caller.locals[callerId].value = .live (.immediate callerOld))
    (callerCached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let state := Storage.withCurrent (frames.push caller) frame machine
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
    ∃ result done finalMachine,
      finalMachine = GenericPopFrame.afterRelevanceAt (frames.push caller) done
        (ActualPopPlan.released
          (PointerAddCurrentReturn.accountedMachine options remaining span
            (CanonicalCopy.replaceAllocation writeState id kind result).machine)
          (CanonicalCopy.replaceAllocation writeState id kind result).machine.memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD (frames.push caller).size) ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {PointerAddCurrentReturn.writeFrame caller callerId .uninit callerValid with location := .mir ⟨target,0⟩} finalMachine) ∧
      finalMachine.memory.live[id]? = some ⟨kind,result⟩ ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧ result.extra = writeAccess.tree ∧
      CopyProvenanceBounds.AllocationBacking result ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have oldValid0 : (0 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have oldNode : frame.locals[0] = ⟨.live (.immediate .uninit),none⟩ := by
    cases slot : frame.locals[0] with
    | mk value layout =>
      have lv : value = .live (.immediate .uninit) := by simpa only [slot] using zeroLive
      have lc : layout = none := by simpa only [slot] using zeroUncached
      simp only [lv,lc]
  have returnSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ :=
    Array.getElem?_eq_some_iff.mpr ⟨oldValid0,oldNode⟩
  obtain ⟨result,done,bodyTrace,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,varargsDone,localsIdDone,
    sizeDone,locationDone,zeroDone,allDone,resultSize,resultLen,resultTree,resultBacking,resultBytes⟩ :=
    GeneralBorrowScopedCopyHelperBody.to_return options limits remaining span debugOff fuel validationFuel
      (frames.push caller) frame machine sourceBody identity callee location size returnSlot tracker id tag base offset sliceLen n kind allocation
      positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached
      borrow bounded sourceLive destLive countLive sourceCached destCached countCached live4 cached4 live5 cached5
      dead14 uncached14 dead15 uncached15 dead16 uncached16 allImmediate localClocks defaultMode ghost shallow
  let state := Storage.withCurrent (frames.push caller) frame machine
  let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
  let copied := (CanonicalCopy.replaceAllocation writeState id kind result).machine
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [sizeDone];decide
  have zeroNode : done.locals[0] = ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ :=
    (Array.getElem?_eq_some_iff.mp zeroDone).2
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList copied.memory copied.memory := by
    rw [empty]
    exact .nil _
  have returned := CopyHelperReturnDriver.return_step options limits remaining span debugOff fuel validationFuel
    frames caller done copied (bodyDone.trans sourceBody) (identityDone.trans identity) (calleeDone.trans callee)
    locationDone valid0 (congrArg LocalState.value zeroNode) (congrArg LocalState.layout zeroNode)
    (by rw [extraDone];exact localClocks) callerId callerValid callerOld callerLive callerCached callerClocks
    (by rw [returnDone];exact destination) target unwindAction (by rw [continuationDone];exact continuation)
    allDone (by rw [varargsDone];exact varargs) tracker borrowFrame tracked (by rw [extraDone];exact frameTracked)
    copied.memory plan thread active unchecked noGc fixed ghost shallow
  let finalMachine := GenericPopFrame.afterRelevanceAt (frames.push caller) done
    (ActualPopPlan.released (PointerAddCurrentReturn.accountedMachine options remaining span copied) copied.memory tracker borrowFrame)
    (thread.topUserRelevantFrame.getD (frames.push caller).size)
  refine ⟨result,done,finalMachine,rfl,?_,?_,resultSize,resultLen,resultTree,resultBacking,resultBytes⟩
  · exact SuccessfulTrace.append bodyTrace (.next returned (.refl _))
  · have memoryEq : finalMachine.memory = copied.memory := by
      unfold finalMachine GenericPopFrame.afterRelevanceAt
      split <;> rfl
    rw [memoryEq]
    exact CanonicalCopy.replace_lookup writeState id kind result

#print axioms from_bb7
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``from_bb7) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperCurrentCall

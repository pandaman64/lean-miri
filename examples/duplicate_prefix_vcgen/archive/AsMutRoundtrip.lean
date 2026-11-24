import duplicate_prefix.FrameRootRelevance
import duplicate_prefix.AsMutPtrBody
import duplicate_prefix.AsMutReturnStep

namespace DuplicatePrefix.AsMutRoundtrip
open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts PreparedArguments SourceDomain

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem helper
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (fuel sizeFuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (dynamicFuel : options.place.dynamicFuel = sizeFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (length base : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent (frames.push caller) frame machine) length)
    (region : ExclusiveRegion (Storage.withCurrent (frames.push caller) frame machine) length storage tag)
    (mode : region.tracker.retagMode = .Default)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (loc : frame.location = .mir ⟨0,0⟩)
    (size : frame.locals.size = 5)
    (zero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (positive : 0 < length) (signedFits : length.toNat < 9223372036854775808)
    (cachedBase : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id,base⟩)
    (nonzero : base + storage.relativeStart.bytes ≠ 0)
    (deadSlots : ∀ n, 2 ≤ n → n < 5 → frame.locals[n]? = some ⟨.dead,none⟩)
    (noClocks : frame.extra.dataRace = none)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (destCached : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (continuation : frame.returnContinuation = .goto (some 7) .Unreachable)
    (noVarargs : frame.vaList = #[])
    (owned : FrameState) (ledger : frame.extra.borrowTracker = some owned)
    (one : owned.protectedTags = #[(storage.id,tag)])
    (root : UniIndex) (roots : storage.entry.allocation.extra.roots = #[root])
    (node : TreeNode) (nodeFound : storage.entry.allocation.extra.nodeAt region.source = some node)
    (unexposed : node.isExposed = false)
    (materialized : RetagReleaseFootprint.MaterializedWithin storage.entry.allocation.extra region.source
      storage.relativeStart.bytes (storage.relativeStart.bytes + length))
    (vacant : RetagReleaseFootprint.VacantRows storage.entry.allocation.extra)
    (fits : storage.relativeStart.bytes.toNat + length.toNat ≤ storage.entry.allocation.extra.locations.size.bytes.toNat)
    (thread : ThreadRecord) (relevance : Nat)
    (current : machine.threads.activeThread? = some thread)
    (cached : FrameRelevance.top ⟨(frames.push caller).push frame⟩ thread.topUserRelevantFrame = some relevance)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (noAlias : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).entries.any
      (·.value.ty == 2) = false) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent (frames.push caller) frame machine
    let pointer := Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes))
    let value := Scalar.fromPointer cfg.access.runtime.base pointer
    let returned := {AsMutPtrReturn.writeFrame caller callerId (.scalar value) callerValid with location := FrameLocation.mir ⟨7,0⟩}
    frame.locals[1]? = some ⟨.live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer
      length ActualReferenceMetadata.reference).imm),some ActualReferenceMetadata.reference⟩ →
    ∃ popped : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace cfg limits before (Storage.withCurrent frames returned popped) ∧
      popped.user.addresses = machine.user.addresses ∧ popped.dataRace = machine.dataRace ∧
      popped.user = (AsMutCurrentCall.charged options (remaining+1) span machine).user ∧
      popped.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      (∃ presentThread, popped.threads.activeThread? = some presentThread) ∧
      (caller.extra.userRelevance = 255 →
        (thread.topUserRelevantFrame = some frames.size ∨ thread.topUserRelevantFrame = some (frames.push caller).size) →
        ∃ reported, popped.threads.activeThread? = some reported ∧ reported.topUserRelevantFrame = some frames.size) ∧
      ∃ next : InitializedRegion (Storage.withCurrent frames returned popped) length,
        next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
        next.entry = { storage.entry with allocation := storage.entry.allocation.setExtra next.entry.allocation.extra } ∧
        next.entry.allocation.extra.roots = storage.entry.allocation.extra.roots ∧
        next.entry.allocation.extra.locations.size = storage.entry.allocation.extra.locations.size ∧
        ∃ right : ExclusiveRegion (Storage.withCurrent frames returned popped) length next tag,
          right.tracker.retagMode = region.tracker.retagMode := by
  intro cfg before pointer value returned argument
  let inner := PreparedContracts.actualConfig options () remaining span
  have target : cfg.access.runtime = inner.access.runtime := by
    unfold cfg inner
    rw [actual_access_runtime, actual_access_runtime]
  have geometry : AsMutPtrCarrier.Valid machine (.inl pointer) length :=
    .positive storage.id tag base storage.relativeStart.bytes length storage.entry cachedBase storage.live
      positive nonzero signedFits storage.fits
  have slots (n : Nat) (bounded : n < 5) (slot : LocalState Provenance LocalLayout)
      (eq : frame.locals[n]? = some slot) : frame.locals[n]'(by omega) = slot :=
    Option.some.inj ((Array.getElem?_eq_getElem (show n < frame.locals.size by omega)).symm.trans eq)
  have z := slots 0 (by decide) _ zero
  have o := slots 1 (by decide) _ argument
  have a := slots 2 (by decide) _ (deadSlots 2 (by decide) (by decide))
  have b := slots 3 (by decide) _ (deadSlots 3 (by decide) (by decide))
  have c := slots 4 (by decide) _ (deadSlots 4 (by decide) (by decide))
  have copied : (frame.locals[1]'(by omega)).value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl pointer) inner.access.runtime.base length)) := by
    rw [o]
    simp only [PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,target]
  obtain ⟨done,trace,doneBody,_,_,doneExtra,doneReturn,doneContinuation,doneVarargs,_,kept,sizeDone,atReturn,
    result,d2,d3,d4⟩ :=
    AsMutPtrBody.actual_ten_statements options limits remaining span debugOff fuel validationFuel (frames.push caller)
      frame machine pointer length geometry size (by rw [z]) (by rw [z]) copied (by rw [o])
      (by rw [a]) (by rw [a]) (by rw [b]) (by rw [b]) (by rw [c]) (by rw [c])
      body identity callee loc noClocks region.tracker region.tracked mode ghost shallow sizeFuel dynamicFuel cmp metadata noAlias
  have direct : ∀ slot ∈ done.locals, ∀ memor, slot.value ≠ .live (.indirect memor) := by
    intro slot member memor malformed
    obtain ⟨n,inBounds,eq⟩ := Array.mem_iff_getElem.mp member
    have atSlot : done.locals[n]? = some slot := by
      rw [Array.getElem?_eq_getElem inBounds,eq]
    have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    · rw [atSlot] at result
      cases result
      cases malformed
    · rw [atSlot,argument] at kept
      cases kept
      cases malformed
    · rw [atSlot] at d2
      simp only [Option.map_some, Option.some.injEq] at d2
      rw [d2] at malformed
      cases malformed
    · rw [atSlot] at d3
      simp only [Option.map_some, Option.some.injEq] at d3
      rw [d3] at malformed
      cases malformed
    · rw [atSlot] at d4
      simp only [Option.map_some, Option.some.injEq] at d4
      rw [d4] at malformed
      cases malformed
  have valid0 : 0 < done.locals.size := by rw [sizeDone]; decide
  have resultSlot : done.locals[0] = ⟨.live (.immediate (.scalar value)),some CopyCompilerFacts.destPointerLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans result)
  let afterStatements := Storage.withCurrent (frames.push caller) done machine
  let stored : InitializedRegion afterStatements length := {storage with live := storage.live}
  let rights : ExclusiveRegion afterStatements length stored tag := {region with tracked := region.tracked}
  have cachedTop : FrameRelevance.top ⟨(frames.push caller).push done⟩ thread.topUserRelevantFrame = some relevance := by
    unfold FrameRelevance.top at cached ⊢
    simpa only [Array.isEmpty_push, Array.size_push] using cached
  obtain ⟨popped,ret,unchanged,race,finalUser,fixedStill,activeThread,exactThreads,next,idEq,offsetEq,physical,rootsStill,extentStill,resultRights,modeStill⟩ :=
    AsMutReturnStep.returns options limits remaining span fuel debugOff validationFuel frames caller done machine length base tag
      stored rights (doneBody.trans body) atReturn valid0 (by rw [resultSlot]) (by rw [resultSlot])
      (by rw [doneExtra]; exact noClocks) callerId callerValid destCached destLive callerClocks
      (by rw [doneReturn]; exact destination) (by rw [doneContinuation]; exact continuation) direct (by rw [doneVarargs]; exact noVarargs)
      owned (by rw [doneExtra]; exact ledger) one root roots node nodeFound unexposed materialized vacant fits
      thread relevance current cachedTop ghost shallow fixed unchecked noGc
  refine ⟨popped,SuccessfulTrace.append trace (.next ret (.refl _)),unchanged,race,finalUser,fixedStill,activeThread,?_,next,idEq,offsetEq,physical,rootsStill,extentStill,resultRights,modeStill⟩
  intro callerRank priorCache
  have index : relevance = thread.topUserRelevantFrame.getD (frames.push caller).size := by
    rcases priorCache with top | top
    · simpa [FrameRelevance.top, top, eq_comm] using cachedTop
    · simpa [FrameRelevance.top, top, eq_comm] using cachedTop
  rw [exactThreads,index]
  exact FrameRootRelevance.restoredAfterHelper frames caller done machine thread current callerRank priorCache

end DuplicatePrefix.AsMutRoundtrip

#print axioms DuplicatePrefix.AsMutRoundtrip.helper

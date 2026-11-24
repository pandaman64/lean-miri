import duplicate_prefix.RootCurrentCopyReady
import duplicate_prefix.CopyOwnershipTransport

namespace DuplicatePrefix.RootPositiveAfterAsMut
open Miri Miri.ABI Miri.MIR Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PreparedArguments SourceDomain
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- Carry the actual raw pointer and its exclusive allocation through pointer
addition and copy-argument preparation. The prior trace can come from the
checked as_mut_ptr round trip. -/
theorem through_copy_call
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (validation : options.limits.validation = fuel+1) (statementFuel : limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (incoming : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      before (Storage.withCurrent frames frame machine))
    (length count base : UInt64) (tag : BorTag)
    (storage : InitializedRegion (Storage.withCurrent frames frame machine) length)
    (rights : ExclusiveRegion (Storage.withCurrent frames frame machine) length storage tag)
    (positive : 0 < count.toNat) (countFits : count.toNat < 2^63)
    (disjoint : count.toNat + count.toNat ≤ length.toNat)
    (address : machine.user.addresses.baseAddr.find? (fun row => row.allocId == storage.id) = some ⟨storage.id,base⟩)
    (size : frame.locals.size = 25)
    (pointerSlot : frame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+storage.relativeStart.bytes)))))),
      some CopyCompilerFacts.destPointerLayout⟩)
    (temp16 : Immediate Provenance)
    (live16 : (frame.locals[16]'(by omega)).value = .live (.immediate temp16))
    (countSlot : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (unused : ∀i(v:i<frame.locals.size),17≤i→i≤23→(frame.locals[i]'v)=⟨.dead,none⟩)
    (unused24 : frame.locals[24]? = some ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,0⟩) (noClocks : frame.extra.dataRace = none)
    (mode : rights.tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (all : CopyHelperCleanup.AllImmediate frame) (noRace : machine.dataRace = none)
    (trackNone : frame.trackCallerArg = none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size) (relevant : frame.extra.userRelevance > 0)
    (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (source : PreparedContracts.SourceComparator) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let offset := storage.relativeStart.bytes
    let pointer := Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+offset)))
    let advanced := Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+offset+count)))
    ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits before (Storage.withCurrent frames result finalMachine) ∧
      result.location = .mir ⟨8,4⟩ ∧ result.locals.size = 25 ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals[17]? = some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[18]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[19]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      result.locals[21]? = some ⟨.live (.immediate (.scalar advanced)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      result.locals[24]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∀ i, i < 16 ∨ 24 < i → result.locals[i]? = frame.locals[i]?) ∧ CopyHelperCleanup.AllImmediate result ∧
      finalMachine.user.addresses = machine.user.addresses ∧ finalMachine.user.payload.ghost = false ∧
      finalMachine.user.payload.validation = .Shallow ∧
      ∃ (next : InitializedRegion (Storage.withCurrent frames result finalMachine) length)
        (nextRights : ExclusiveRegion (Storage.withCurrent frames result finalMachine) length next tag),
      next.id = storage.id ∧ next.relativeStart = storage.relativeStart ∧
      next.entry = storage.entry ∧ nextRights.tracker = rights.tracker := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let offset := storage.relativeStart.bytes
  let pointer : Scalar Provenance := Scalar.fromPointer cfg.access.runtime.base
    (Pointer.new (.concrete storage.id tag) (Size.ofBytes (base+offset)))
  have at15 := (Array.getElem?_eq_some_iff.mp pointerSlot).2
  have at2 := (Array.getElem?_eq_some_iff.mp countSlot).2
  have bound : offset.toNat+count.toNat ≤ storage.entry.allocation.byteSize.bytes.toNat := by
    exact Nat.le_trans (Nat.add_le_add_left (by omega) _) storage.fits
  obtain ⟨result,finalMachine,steps,b,i,f,e,r,c,a,localIdentity,track,sz,pc,s17,s18,s19,s21,s24,kept,direct,mem,tracker,addr,
      lastGhost,lastShallow⟩ :=
    RootCurrentCopyReady.from_bb7 options limits remaining span debug fuel validation statementFuel frames frame machine
      pointer count temp16 size (by rw [at15]) (by rw [at15]) live16 (by rw [at2]) (by rw [at2]) unused body identity callee location
      noClocks rights.tracker rights.tracked mode ghost shallow all storage.id tag base offset storage.entry rfl address storage.live
      positive countFits bound noRace trackNone thread active top relevant budget dispatch backend unchecked noGc fixed source unused24
  let next : InitializedRegion (Storage.withCurrent frames result finalMachine) length :=
    CopyOwnershipTransport.storageAfter storage mem
  let nextRights : ExclusiveRegion (Storage.withCurrent frames result finalMachine) length next tag :=
    CopyOwnershipTransport.rightsAfter rights mem tracker
  exact ⟨result,finalMachine,SuccessfulTrace.append incoming steps,pc,sz,b,i,f,e,r,c,a,localIdentity,track,
    s17,s18,s19,s21,s24,kept,direct,addr,lastGhost,lastShallow,next,nextRights,rfl,rfl,rfl,rfl⟩

end DuplicatePrefix.RootPositiveAfterAsMut

#print axioms DuplicatePrefix.RootPositiveAfterAsMut.through_copy_call

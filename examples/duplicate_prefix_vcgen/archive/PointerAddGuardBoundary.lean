import duplicate_prefix.PointerAddCurrentComplete

namespace DuplicatePrefix.PointerAddGuardBoundary
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

/-- The actual callee frame at the block containing the pointer offset. -/
structure Ready (frame : CompilerFrameContext.ActualFrame) (pointer : Scalar Provenance) (count : UInt64) : Prop where
  size : frame.locals.size = 12
  body : frame.body = PointerAddCurrentFacts.body.body
  identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity
  callee : frame.functionInstance = PointerAddCurrentFacts.call.callee
  location : frame.location = .mir ⟨6,0⟩
  noClocks : frame.extra.dataRace = none
  returnSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  pointerSlot : frame.locals[1]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩
  countSlot : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  unitValue : frame.locals[3]?.map (·.value) = some (.live (.immediate .uninit))
  boolValue : frame.locals[4]?.map (·.value) = some (.live (.immediate (.scalar (.fromBool false))))
  pointerTemporary : frame.locals[10]? = some ⟨.dead,none⟩
  countTemporary : frame.locals[11]? = some ⟨.dead,none⟩
  direct : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory)
  varargs : frame.vaList = #[]
  borrowFrame : frame.extra.borrowTracker = some {}

/-- A finite trace through the actual guard calls to the offset block. -/
structure Reaches (options : EvalConfigurationCore.Options)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array CompilerFrameContext.ActualFrame)
    (caller entered : CompilerFrameContext.ActualFrame)
    (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Scalar Provenance) (count : UInt64) where
  ready : CompilerFrameContext.ActualFrame
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent (older.push caller) entered initial)
    (Storage.withCurrent (older.push caller) ready machine)
  shape : Ready ready pointer count
  place : ready.returnPlace = entered.returnPlace
  continuation : ready.returnContinuation = entered.returnContinuation
  memory : machine.memory = initial.memory
  tracker : machine.borrowTracker = initial.borrowTracker
  addresses : machine.user.addresses = initial.user.addresses
  dataRace : machine.dataRace = initial.dataRace
  ghost : machine.user.payload.ghost = initial.user.payload.ghost
  validation : machine.user.payload.validation = initial.user.payload.validation
  checked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  thread : ThreadRecord
  active : machine.threads.activeThread? = some thread

private theorem observed_value (frame : CompilerFrameContext.ActualFrame)
    (index : Nat) (valid : index < frame.locals.size) (value : LocalValue Provenance)
    (observation : frame.locals[index]?.map (·.value) = some value) :
    frame.locals[index].value = value := by
  rw [getElem?_pos frame.locals index valid] at observation
  exact Option.some.inj observation

/-- Compose the checked guard path and offset block up to the caller's next block. -/
theorem returns (options : EvalConfigurationCore.Options)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (older : Array CompilerFrameContext.ActualFrame) (caller entered : CompilerFrameContext.ActualFrame)
    (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (guard : Reaches options limits remaining span older caller entered initial
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset)))) count)
    (tracker : MachineHooks.BorrowState) (tracked : initial.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : initial.user.payload.ghost = false)
    (shallow : initial.user.payload.validation = .Shallow)
    (cached : initial.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : initial.memory.live[id]? = some entry)
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (callerId : MIR.LocalId) (valid : callerId < caller.locals.size)
    (live : caller.locals[callerId].value = .live (.immediate .uninit))
    (layout : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : entered.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace older.size caller callerId CopyCompilerFacts.destPointerLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : entered.returnContinuation = .goto (some target) unwind) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let value := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset+count)))
    ∃ done finalMachine,
      finalMachine = PointerAddCurrentReturn.poppedMachine older caller done
        (PointerAddCurrentReturn.accountedMachine options remaining span guard.machine)
        (guard.thread.topUserRelevantFrame.getD (older.push caller).size) ∧
      finalMachine.memory = initial.memory ∧ finalMachine.borrowTracker = initial.borrowTracker ∧
      finalMachine.user.addresses = initial.user.addresses ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent (older.push caller) entered initial)
        (Storage.withCurrent older
          {PointerAddCurrentReturn.writeFrame caller callerId (.scalar value) valid with
            location := .mir ⟨target,0⟩} finalMachine) := by
  let shape := guard.shape
  have at0 := (Array.getElem?_eq_some_iff.mp shape.returnSlot).2
  have at1 := (Array.getElem?_eq_some_iff.mp shape.pointerSlot).2
  have at2 := (Array.getElem?_eq_some_iff.mp shape.countSlot).2
  have at10 := (Array.getElem?_eq_some_iff.mp shape.pointerTemporary).2
  have at11 := (Array.getElem?_eq_some_iff.mp shape.countTemporary).2
  have at3 : 3 < guard.ready.locals.size := by rw [shape.size]; decide
  have at4 : 4 < guard.ready.locals.size := by rw [shape.size]; decide
  have unit := observed_value guard.ready 3 at3 _ shape.unitValue
  have bool := observed_value guard.ready 4 at4 _ shape.boolValue
  obtain ⟨done,finalMachine,machineEq,memEq,trackEq,addressEq,suffix⟩ :=
    PointerAddCurrentComplete.trace_exact options limits remaining span debugOff fuel validationFuel
      older caller guard.ready guard.machine id tag base offset count entry shape.size
      (by rw [at0]) (by rw [at0]) (by rw [at1]) (by rw [at1]) (by rw [at2]) (by rw [at2])
      (by rw [at10]) (by rw [at10]) (by rw [at11]) (by rw [at11]) shape.body shape.identity shape.callee
      shape.location shape.noClocks tracker (guard.tracker.trans tracked) defaultMode
      (guard.ghost.trans ghostFalse) (guard.validation.trans shallow) (by rw [guard.addresses]; exact cached)
      (by rw [guard.memory]; exact present) positive fits bounds .uninit (.scalar (.fromBool false)) unit bool
      callerId valid live layout callerClocks (by rw [guard.place]; exact destination)
      target unwind (guard.continuation.trans continuation) shape.direct shape.varargs {} shape.borrowFrame rfl
      guard.thread guard.active guard.checked guard.noGc guard.fixed
  exact ⟨done,finalMachine,machineEq,memEq.trans guard.memory,trackEq.trans guard.tracker,
    addressEq.trans guard.addresses,SuccessfulTrace.append guard.trace suffix⟩

#print axioms returns

end DuplicatePrefix.PointerAddGuardBoundary

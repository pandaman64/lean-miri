import duplicate_prefix.EmptyWildcardLength
import duplicate_prefix.RootNonzeroEntry
import duplicate_prefix.RootRejectedPrefix

namespace DuplicatePrefix.EmptyWildcardPrefix
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.Concurrency
open EmptyWildcardLength EmptyReferenceAllocation RootZeroCompleteState
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem someSlot {a : Array (LocalState Provenance LocalLayout)} {i : Nat}
    (bound : i < a.size) {value : LocalState Provenance LocalLayout} (found : a[i]? = some value) : a[i] = value :=
  Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans found)

/-- A non-null unresolved wildcard-provenance empty slice takes the ordinary rejection path
for every nonzero count. The trace ends at the actual root Return. -/
theorem reaches_return
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
    (address count : UInt64) (nonNull : address ≠ 0) (nonzero : count ≠ 0)
    (unresolved : EmptyWildcardLocalValidator.Unresolved machine.user.addresses machine.memory address)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨0,0⟩) (size : frame.locals.size = 25)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (slot1 : frame.locals[1]? = some ⟨.live (.immediate
      (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base (Pointer.new .wildcard (Size.ofBytes address)) 0 EmptyReferenceMetadata.reference).imm), some EmptyReferenceMetadata.reference⟩)
    (slot2 : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (slot3 : frame.locals[3]? = some ⟨.dead,none⟩) (slot4 : frame.locals[4]? = some ⟨.dead,none⟩)
    (slot5 : frame.locals[5]? = some ⟨.dead,none⟩)
    (slot13 : frame.locals[13]? = some ⟨.live (.immediate .uninit),none⟩)
    (all : ZeroImmediateFacts.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (freshAgain : (allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
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
    ∃ result final,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent older frame machine) (Storage.withCurrent older result final) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧
      result.functionInstance = frame.functionInstance ∧ result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧
      result.returnContinuation = frame.returnContinuation ∧ result.vaList = frame.vaList ∧
      ZeroImmediateFacts.AllImmediate result ∧
      final.memory = machine.memory ∧ final.borrowTracker = some (allocatedTracker (allocatedTracker tracker fresh) freshAgain) ∧
      final.user.payload.ghost = false ∧ final.user.payload.validation = .Shallow ∧
      final.dataRace = none ∧ final.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl final.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl final.user).gcInterval = 0 ∧
      final.user.addresses = machine.user.addresses ∧
      final.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      final.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      final.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      ∃ threadAfter, final.threads.activeThread? = some threadAfter := by
  let ticked := tick options remaining span machine
  have sameUserBackend : ticked.user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
    unfold ticked tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have sameUserTypes : ticked.user.payload.payload.user.types = machine.user.payload.payload.user.types := by
    unfold ticked tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have bound (i : Nat) (b : i < 25) : i < frame.locals.size := by omega
  have cell2 := someSlot (bound 2 (by decide)) slot2
  have cell3 := someSlot (bound 3 (by decide)) slot3
  have cell4 := someSlot (bound 4 (by decide)) slot4
  have cell5 := someSlot (bound 5 (by decide)) slot5
  obtain ⟨shared, traceStart, b, ident, fn, extra, place, cont, args, localsId, trackCaller, countSize,
    pc, sh0, sh1, sh7, sh8, sh9, sh10, sh11, sh12, sh13, immediate⟩ :=
    RootNonzeroEntry.reachesSharedReference options limits remaining span source debug fuel validationFuel
      older frame machine body identity callee located size count nonzero unused
      (congrArg LocalState.value cell3) (congrArg LocalState.layout cell3)
      (congrArg LocalState.value cell4) (congrArg LocalState.value cell5)
      (congrArg LocalState.layout cell4) (congrArg LocalState.layout cell5)
      (congrArg LocalState.value cell2) (congrArg LocalState.layout cell2)
      noClocks all tracker tracked mode ghost shallow unchecked noGc fixed
  have boundShared (i : Nat) (b : i < 25) : i < shared.locals.size := by omega
  let valid12 := boundShared 12 (by decide)
  let valid11 := boundShared 11 (by decide)
  let materialized := sharedFrame shared valid12 address
  let validLength : 11 < materialized.locals.size := by
    simpa [materialized, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using valid11
  let returned := LenCallResultFrame.resultFrame materialized validLength 0
  have tickUnresolved : EmptyWildcardLocalValidator.Unresolved ticked.user.addresses ticked.memory address := by
    unfold ticked tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact unresolved
  obtain ⟨afterLen, traceLen, sameMemory, sameTracker, gh, sh, dr, fix, un, gc, addresses, types, back, extras, someThread⟩ :=
    returns_length options limits remaining budget dispatchFuel span preciseOff implicitOff debug cmp source
      dynamicFuel fuel dynamicEq validationFuel older shared ticked address nonNull tickUnresolved
      (b.trans body) (ident.trans identity) (fn.trans callee) pc tracker tracked mode fresh freshAgain
      (boundShared 1 (by decide)) valid11 valid12 (someSlot _ (sh1.trans slot1)) (someSlot _ sh11) (someSlot _ sh12)
      ((congrArg (·.dataRace) extra).trans noClocks)
      ((tick_ghost options remaining span machine).trans ghost)
      ((tick_shallow options remaining span machine).trans shallow)
      race (sameUserBackend.trans backend) thread active cacheBound
      ((congrArg (·.metadata) sameUserTypes).trans metadata)
      ((congrArg (fun types => types.entries.any (·.value.ty == 2)) sameUserTypes).trans notConstructed)
      ((tick_flags options remaining span machine).1.trans unchecked)
      ((tick_flags options remaining span machine).2.trans noGc) fixed
  have sameResult : returned.locals.size = 25 := by
    rw [LenCallResultFrame.size]
    simpa [materialized, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout] using countSize
  have boundResult (i : Nat) (b : i < 25) : i < returned.locals.size := by omega
  have sameSlot (i : Nat) (i11 : i ≠ 11) (i12 : i ≠ 12) : returned.locals[i]? = shared.locals[i]? := by
    rw [LenCallResultFrame.other _ _ _ _ i11]
    simp [materialized, sharedFrame, CopyHelperSteps.advance, ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout, Ne.symm i12]
  have result0 := someSlot (boundResult 0 (by decide)) ((sameSlot 0 (by decide) (by decide)).trans (sh0.trans slot0))
  have result7 := someSlot (boundResult 7 (by decide)) ((sameSlot 7 (by decide) (by decide)).trans sh7)
  have result8 := someSlot (boundResult 8 (by decide)) ((sameSlot 8 (by decide) (by decide)).trans sh8)
  have result9 := someSlot (boundResult 9 (by decide)) ((sameSlot 9 (by decide) (by decide)).trans sh9)
  have result10 := someSlot (boundResult 10 (by decide)) ((sameSlot 10 (by decide) (by decide)).trans sh10)
  have result11 := someSlot (boundResult 11 (by decide)) (LenCallResultFrame.value materialized validLength 0)
  let temp := (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
  have result12 : returned.locals[12]'(boundResult 12 (by decide)) = ⟨.live (.immediate temp),some SharedReferenceMetadata.sharedLayout⟩ := by
    apply someSlot
    rw [LenCallResultFrame.other _ _ _ _ (by decide)]
    simp [materialized, sharedFrame, temp, CopyHelperSteps.advance, ActualLocalCopy.written, LocalPlaces.cachePlaceLayout]
  have result13 := someSlot (boundResult 13 (by decide)) ((sameSlot 13 (by decide) (by decide)).trans (sh13.trans slot13))
  have allMaterialized : ZeroImmediateFacts.AllImmediate materialized := by
    exact ZeroImmediateFacts.all_immediate_written shared 12 _ _ valid12 immediate
  have allReturned := LenCallResultFrame.all_immediate materialized validLength 0 allMaterialized
  have rejected : count > (0 : UInt64) / 2 := by
    rw [show (0 : UInt64) / 2 = 0 from rfl]
    have pos : count.toNat ≠ 0 := fun eq => nonzero (UInt64.toNat_inj.mp eq)
    exact UInt64.lt_iff_toNat_lt.mpr (Nat.pos_of_ne_zero pos)
  let tracking := allocatedTracker (allocatedTracker tracker fresh) freshAgain
  obtain ⟨result, traceReject, bR, iR, fR, eR, pR, cR, aR, lR, sizeR, pcR, boolR, allR⟩ :=
    RootRejectedPrefix.executes options limits remaining span source debug fuel validationFuel older returned afterLen
      0 count rejected sameResult temp (congrArg LocalState.value result12)
      (congrArg LocalState.value result13) (congrArg LocalState.layout result13)
      (congrArg LocalState.value result0) (congrArg LocalState.layout result0)
      (congrArg LocalState.value result7) (congrArg LocalState.value result8) (congrArg LocalState.layout result8)
      (congrArg LocalState.value result9) (congrArg LocalState.layout result9)
      (congrArg LocalState.value result10) (congrArg LocalState.layout result10)
      (congrArg LocalState.value result11) (congrArg LocalState.layout result11)
      (b.trans body) (ident.trans identity) (fn.trans callee) rfl allReturned
      ((congrArg (·.dataRace) extra).trans noClocks) tracking sameTracker mode gh sh un gc fix
  let next := tick options remaining span
  let final := next (next (next afterLen))
  have preserve (get : MachineState → Prop) (keep : ∀ s, get (next s) = get s)
      (ready : get afterLen) : get final := by
    rw [show final = next (next (next afterLen)) from rfl, keep, keep, keep]
    exact ready
  let control := (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
  have endpoints (T : Type) (field : Machine.RootUser → T)
      (stable : ∀ m, field (next m).user = field m.user)
      (same : field afterLen.user = field ticked.user) : field final.user = field machine.user :=
    preserve (fun m => field m.user = field machine.user)
      (fun m => congrArg (· = field machine.user) (stable m))
      (same.trans (stable machine))
  refine ⟨result, final, SuccessfulTrace.append traceStart (SuccessfulTrace.append traceLen traceReject),
    bR.trans b, iR.trans ident, fR.trans fn, pcR, boolR, eR.trans extra, pR.trans place,
    cR.trans cont, aR.trans args, allR, sameMemory, sameTracker,
    preserve (fun st => st.user.payload.ghost = false) (fun m => congrArg (· = false) (tick_ghost options remaining span m)) gh,
    preserve (fun st => st.user.payload.validation = .Shallow) (fun m => congrArg (· = .Shallow) (tick_shallow options remaining span m)) sh,
    dr, fix, preserve (fun st => (control st.user).checkedArithmetic = false) (fun m => congrArg (· = false) (tick_flags options remaining span m).1) un,
    preserve (fun st => (control st.user).gcInterval = 0) (fun m => congrArg (· = 0) (tick_flags options remaining span m).2) gc, ?_, ?_, ?_, ?_, someThread⟩
  · refine endpoints _ (·.addresses) ?_ addresses
    intro m
    unfold next tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  · exact endpoints _ (·.payload.payload.user.types) (fun m => by
      unfold next tick SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl) types
  · exact endpoints _ (·.payload.payload.user.backend) (fun m => by
      unfold next tick SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl) back
  · exact endpoints _ (·.payload.payload.user.runtime.extras) (fun m => by
      unfold next tick SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl) extras

#print axioms reaches_return
end
end DuplicatePrefix.EmptyWildcardPrefix

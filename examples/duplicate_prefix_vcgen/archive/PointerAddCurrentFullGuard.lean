import duplicate_prefix.PointerAddGuardEntryCurrent
import duplicate_prefix.PointerAddCurrentGuardSuffix
import duplicate_prefix.PointerAddGuardBoundary
import duplicate_prefix.LanguageGuardCurrentRoundtrip
import duplicate_prefix.CopyRootGuardState

namespace DuplicatePrefix.PointerAddCurrentFullGuard
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open PointerAddGuardEntryCurrent
set_option maxRecDepth 65536
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

structure Initial (frame : CompilerFrameContext.ActualFrame) (pointer : Scalar Provenance) (count : UInt64) : Prop where
  size : frame.locals.size = 12
  body : frame.body = PointerAddCurrentFacts.body.body
  identity : frame.bodyIdentity = PointerAddCurrentFacts.body.identity
  callee : frame.functionInstance = PointerAddCurrentFacts.call.callee
  location : frame.location = .mir ⟨0,0⟩
  noClocks : frame.extra.dataRace = none
  zero : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  first : frame.locals[1]? = some ⟨.live (.immediate (.scalar pointer)),some CopyCompilerFacts.destPointerLayout⟩
  second : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  unit : frame.locals[3]? = some ⟨.dead,none⟩
  boolean : frame.locals[4]? = some ⟨.dead,none⟩
  tempPointer : frame.locals[10]? = some ⟨.dead,none⟩
  tempCount : frame.locals[11]? = some ⟨.dead,none⟩
  direct : CopyHelperCleanup.AllImmediate frame
  varargs : frame.vaList = #[]
  borrowFrame : frame.extra.borrowTracker = some ({} : FrameState)

private theorem readSlot (f : CompilerFrameContext.ActualFrame) (i : Nat) {row : LocalState Provenance LocalLayout}
    (h : f.locals[i]? = some row) (valid : i < f.locals.size) : f.locals[i] = row :=
  (Array.getElem?_eq_some_iff.mp h).2

private theorem scopes (xs : Array α) (a b c d : α) :
    ((((xs.push a).push b).push c).push d)[xs.size+2]? = some c ∧
    ((((xs.push a).push b).push c).push d)[xs.size]? = some a := by
  constructor <;> simp [Array.getElem_push,Nat.add_assoc]

/-- From the actual initialized ptr.add frame, execute both nested guard calls,
both returns, and the checked false successor into the offset block. -/
theorem reaches_offset_profile
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (callFuel : limits.callDispatch = budget+1)
    (validationFuel : options.limits.validation = fuel+1)
    (statementFuel : limits.validation = fuel+1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debug : options.place.debugAssertions = false)
    (older : Array CompilerFrameContext.ActualFrame) (root entered : CompilerFrameContext.ActualFrame)
    (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Scalar Provenance) (count : UInt64) (shape : Initial entered pointer count)
    (tracker : MachineHooks.BorrowState) (tracked : initial.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default) (noRace : initial.dataRace = none)
    (backend : initial.user.payload.payload.user.backend = .none)
    (ghost : initial.user.payload.ghost = false) (shallow : initial.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      initial.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      initial.user).gcInterval = 0)
    (fixed : initial.threads.fixedScheduling = true)
    (thread : ThreadRecord) (active : initial.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some older.size) :
    ∃ result : PointerAddGuardBoundary.Reaches options limits remaining span older root entered initial pointer count,
      result.machine.user.payload.payload.user.backend = initial.user.payload.payload.user.backend ∧
      result.machine.user.payload.payload.user.runtime.extras = initial.user.payload.payload.user.runtime.extras ∧
      (LanguageZeroEntryFacts.rank options.userRelevantCrates < root.extra.userRelevance →
        RuntimeZeroEntryFacts.rank options.userRelevantCrates < root.extra.userRelevance → result.thread = thread) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let tick := PointerAddCurrentReturn.accountedMachine options remaining span
  have v3 : 3 < entered.locals.size := by rw [shape.size]; decide
  have v4 : 4 < entered.locals.size := by rw [shape.size]; decide
  have at3 := readSlot entered 3 shape.unit v3
  have at4 := readSlot entered 4 shape.boolean v4
  let cached := cached entered v3 v4
  let state := guardState options remaining span older root entered initial v3 v4
  let dest := guardDestination older root entered v3 v4
  let frame := LanguageZeroInstalled.frame options state dest
  let pushed := LanguageZeroEntry.pushedMachine options state dest root
  have prefixTrace := reaches_guard options limits remaining budget callFuel span source debug older root entered initial
    shape.body shape.identity shape.callee shape.location v3 v4 (by rw [at3]) (by rw [at4]) (by rw [at4])
    shape.noClocks noRace backend ghost tracker tracked thread active top unchecked noGc fixed
  have chargedFields := CopyRootGuardState.accounted_fields options remaining span initial
  obtain ⟨pm,pt,pr,pa,pg,pv,pb,pe,pty,pf⟩ := CopyRootGuardState.language_push_fields options state dest root
  have pushedTracked : pushed.borrowTracker = some tracker := pt.trans (chargedFields.2.1.trans tracked)
  have pushedRace : pushed.dataRace = none := pr.trans (chargedFields.2.2.2.1.trans noRace)
  have pushedBackend : pushed.user.payload.payload.user.backend = .none := pb.trans (chargedFields.2.2.2.2.2.2.2.1.trans backend)
  have pushedGhost : pushed.user.payload.ghost = false := pg.trans (chargedFields.2.2.2.2.2.1.trans ghost)
  have pushedShallow : pushed.user.payload.validation = .Shallow := pv.trans (chargedFields.2.2.2.2.2.2.1.trans shallow)
  have pushedFixed : pushed.threads.fixedScheduling = true := pf.trans fixed
  have clock (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    cfg.terminators.getControl (tick before).user = TerminatorClock.advance (cfg.terminators.getControl before.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have pushedControl : cfg.terminators.getControl pushed.user = cfg.terminators.getControl (tick initial).user :=
    CopyRootGuardState.language_push_control options remaining span state dest root
  have pushedUnchecked : (cfg.terminators.getControl pushed.user).checkedArithmetic = false := by
    rw [pushedControl,clock]
    exact unchecked
  have pushedNoGc : (cfg.terminators.getControl pushed.user).gcInterval = 0 := by
    rw [pushedControl,clock]
    exact noGc
  have bodyMeta := LanguageZeroInstalled.metadata options state dest
  obtain ⟨langBody,langId,langFn,langPC,langCaller,langCont,langVa⟩ := bodyMeta
  have size : frame.locals.size = 3 := LanguageZeroInstalled.locals_size options state dest
  have a0 : 0 < frame.locals.size := by rw [size]; decide
  have a1 : 1 < frame.locals.size := by rw [size]; decide
  have a2 : 2 < frame.locals.size := by rw [size]; decide
  have rows : frame.locals = #[
    (⟨.live (.immediate .uninit),none⟩ : LocalState Provenance LocalLayout),
    ⟨.dead,none⟩,⟨.dead,none⟩] := by with_unfolding_all rfl
  have directFrame : CopyHelperCleanup.AllImmediate frame := by
    intro slot member ptr
    rw [rows] at member
    simp [Array.mem_def] at member
    rcases member with rfl | rfl | rfl <;> simp
  have s0 : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by rw [rows]; rfl
  have s1 : frame.locals[1]? = some ⟨.dead,none⟩ := by rw [rows]; rfl
  have s2 : frame.locals[2]? = some ⟨.dead,none⟩ := by rw [rows]; rfl
  have langClocks : frame.extra.dataRace = none := CopyRootGuardState.language_frame_clocks options state dest noRace
  have langBorrow : frame.extra.borrowTracker = some ({} : FrameState) :=
    CopyRootGuardState.language_frame_borrow options state dest tracker tracked
  have c4 : 4 < cached.locals.size := by
    simpa [cached,PointerAddGuardEntryCurrent.cached,PointerAddLanguageGuardUncached.cachedCaller,
      LocalPlaces.cachePlaceLayout,readySize] using v4
  have live4 : cached.locals[4].value = .live (.immediate .uninit) := by
    simp [cached,PointerAddGuardEntryCurrent.cached,ready,PointerAddLanguageGuardUncached.cachedCaller,
      SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout]
  have cache4 : cached.locals[4].layout = some RootCompilerFacts.boolLayout := by
    simp [cached,PointerAddGuardEntryCurrent.cached,PointerAddLanguageGuardUncached.cachedCaller,LocalPlaces.cachePlaceLayout]
  let rank := LanguageZeroEntryFacts.rank options.userRelevantCrates
  have stateDepth : state.stack.frames.size = older.size+2 := by
    simp [state,guardState,Storage.withCurrent,Nat.add_assoc]
  have computedActive : pushed.threads.activeThread? =
      some (PushThread.after thread state.stack.frames.size rank root.extra.userRelevance) :=
    PushThread.active_after (CallEntryFacts.freshRoot state.machine).1 thread state.stack.frames.size rank root.extra.userRelevance active
  have pushedActive : pushed.threads.activeThread? = some (PushThread.after thread (older.size+2) rank root.extra.userRelevance) := by
    simpa only [stateDepth] using computedActive
  let raw := LanguageGuardCurrentRoundtrip.runtimeRawState options remaining span (older.push root) cached frame pushed a1 a2
  let runtimeCaller := LanguageGuardCurrentRoundtrip.runtimeCaller frame a1 a2
  have runtimeMetadata : ∃ (t : ThreadRecord) (index : Nat) (other : CompilerFrameContext.ActualFrame),
      pushed.threads.activeThread? = some t ∧ FrameRelevance.top raw.stack t.topUserRelevantFrame = some index ∧
      raw.stack.frames[index]? = some other ∧ (rank < root.extra.userRelevance → t = thread ∧ other = root) := by
    by_cases rankEq : rank >= root.extra.userRelevance
    · refine ⟨{thread with topUserRelevantFrame := some (older.size+2)},older.size+2,runtimeCaller,?_,?_,?_,?_⟩
      · simpa [PushThread.after,rankEq] using pushedActive
      · simp [FrameRelevance.top]
      · exact (scopes older root cached runtimeCaller _).1
      · intro below
        have h1 := UInt8.lt_iff_toNat_lt.mp below
        have h2 := UInt8.le_iff_toNat_le.mp rankEq
        omega
    · refine ⟨thread,older.size,root,?_,?_,?_,?_⟩
      · simpa [PushThread.after,rankEq] using pushedActive
      · simp [FrameRelevance.top,top]
      · exact (scopes older root cached runtimeCaller _).2
      · exact fun _ => ⟨rfl,rfl⟩
  obtain ⟨t,index,other,activePushed,topPushed,foundPushed,earlierMeta⟩ := runtimeMetadata
  obtain ⟨middle,midThread,guardTrace,memMid,trackMid,addressMid,raceMid,ghostMid,shallowMid,
      backendMid,extrasMid,typesMid,fixedMid,uncheckedMid,gcMid,activeMid,keepMid⟩ :=
    LanguageGuardCurrentRoundtrip.returns_false_with_cache options limits remaining budget fuel callFuel validationFuel statementFuel
      span source debug (older.push root) cached frame pushed langBody langId langFn langPC a0 a1 a2
      (readSlot frame 0 s0 a0) (readSlot frame 1 s1 a1) (readSlot frame 2 s2 a2)
      langClocks directFrame langVa {} langBorrow rfl tracker pushedTracked mode pushedRace pushedBackend
      pushedGhost pushedShallow pushedUnchecked pushedNoGc pushedFixed t activePushed other index topPushed foundPushed
      .languageGuard (Or.inl rfl) c4 live4 cache4 shape.noClocks rfl 1 .Unreachable langCont
  let returned := LanguageGuardCurrentReturn.returnedCallerFrame cached .languageGuard c4 1
  have returnedSize : returned.locals.size = 12 := by
    simp [returned,LanguageGuardCurrentReturn.returnedCallerFrame,cached,PointerAddGuardEntryCurrent.cached,
      PointerAddLanguageGuardUncached.cachedCaller,LocalPlaces.cachePlaceLayout,readySize,shape.size]
  have b3 : 3 < returned.locals.size := by rw [returnedSize]; decide
  have b4 : 4 < returned.locals.size := by rw [returnedSize]; decide
  have unitLive : returned.locals[3].value = .live (.immediate .uninit) := by
    simp [returned,LanguageGuardCurrentReturn.returnedCallerFrame,LanguageGuardCurrentReturn.callerSlot,
      cached,PointerAddGuardEntryCurrent.cached,ready,PointerAddLanguageGuardUncached.cachedCaller,
      SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set]
  have unitCache : returned.locals[3].layout = none := by
    simp [returned,LanguageGuardCurrentReturn.returnedCallerFrame,LanguageGuardCurrentReturn.callerSlot,
      cached,PointerAddGuardEntryCurrent.cached,ready,PointerAddLanguageGuardUncached.cachedCaller,
      SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,at3]
  have boolLive : returned.locals[4].value = .live (.immediate (.scalar (.fromBool false))) := by
    simp [returned,LanguageGuardCurrentReturn.returnedCallerFrame,LanguageGuardCurrentReturn.callerSlot]
  have boolCache : returned.locals[4].layout = some RootCompilerFacts.boolLayout := by
    simp [returned,LanguageGuardCurrentReturn.returnedCallerFrame,LanguageGuardCurrentReturn.callerSlot,cache4]
  have midTracked : middle.borrowTracker = some tracker := trackMid.trans pushedTracked
  obtain ⟨suffix,unchangedSuffix⟩ := PointerAddCurrentGuardSuffix.from_false
    options limits remaining span debug fuel validationFuel (older.push root) returned middle
    shape.body shape.identity shape.callee rfl b3 b4 unitLive unitCache boolLive boolCache shape.noClocks
    tracker midTracked mode ghostMid shallowMid uncheckedMid gcMid fixedMid
  let switched := {returned with location := .mir ⟨5,0⟩}
  let ready := {ActualLocalCopy.written switched 3 CopyHelperUnit.layout b3 .uninit with location := .mir ⟨6,0⟩}
  let finalMachine := tick (tick middle)
  have unchanged (i : Nat) (h3 : i ≠ 3) (h4 : i ≠ 4) : ready.locals[i]? = entered.locals[i]? := by
    rw [show ready.locals[i]? = returned.locals[i]? from unchangedSuffix i h3]
    simp [returned,LanguageGuardCurrentReturn.returnedCallerFrame,LanguageGuardCurrentReturn.callerSlot,
      cached,PointerAddGuardEntryCurrent.cached,PointerAddGuardEntryCurrent.ready,
      PointerAddLanguageGuardUncached.cachedCaller,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,
      Ne.symm h3,Ne.symm h4]
  have unitSlot : ready.locals[3]?.map (·.value) = some (.live (.immediate .uninit)) := by
    simp [ready,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have boolSlot : ready.locals[4]?.map (·.value) = some (.live (.immediate (.scalar (.fromBool false)))) := by
    rw [show ready.locals[4]? = returned.locals[4]? from unchangedSuffix 4 (by decide)]
    simp [getElem?_pos returned.locals 4 b4,boolLive]
  let after3 := SourceSteps.liveFrame entered ⟨0,0⟩ 3 v3
  have v4' : 4 < after3.locals.size := by simpa [after3,SourceSteps.liveFrame] using v4
  have preparedDirect : CopyHelperCleanup.AllImmediate (PointerAddGuardEntryCurrent.ready entered v3 v4) :=
    LocalDirectness.live after3 ⟨0,1⟩ 4 v4' (LocalDirectness.live entered ⟨0,0⟩ 3 v3 shape.direct)
  have cachedDirect : CopyHelperCleanup.AllImmediate cached :=
    CopyHelperCleanup.all_immediate_cache (PointerAddGuardEntryCurrent.ready entered v3 v4) 4 RootCompilerFacts.boolLayout
      (by rw [readySize]; exact v4) preparedDirect
  have returnedDirect : CopyHelperCleanup.AllImmediate returned :=
    CopyHelperCleanup.all_immediate_set cached 4 _ c4 cachedDirect (by intro ptr; simp)
  have finalDirect : CopyHelperCleanup.AllImmediate ready :=
    LocalDirectness.written_at switched 3 CopyHelperUnit.layout .uninit b3 ⟨6,0⟩ returnedDirect
  have readyShape : PointerAddGuardBoundary.Ready ready pointer count := {
    size := by simp [ready,switched,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,returnedSize]
    body := shape.body
    identity := shape.identity
    callee := shape.callee
    location := rfl
    noClocks := shape.noClocks
    returnSlot := (unchanged 0 (by decide) (by decide)).trans shape.zero
    pointerSlot := (unchanged 1 (by decide) (by decide)).trans shape.first
    countSlot := (unchanged 2 (by decide) (by decide)).trans shape.second
    unitValue := unitSlot
    boolValue := boolSlot
    pointerTemporary := (unchanged 10 (by decide) (by decide)).trans shape.tempPointer
    countTemporary := (unchanged 11 (by decide) (by decide)).trans shape.tempCount
    direct := finalDirect
    varargs := shape.varargs
    borrowFrame := shape.borrowFrame }
  have addressTick (m : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
      (tick m).user.addresses = m.user.addresses := by
    unfold tick PointerAddCurrentReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have finalAddress : finalMachine.user.addresses = initial.user.addresses := by
    change (tick (tick middle)).user.addresses = _
    rw [addressTick,addressTick]
    exact addressMid.trans (pa.trans chargedFields.2.2.2.2.1)
  have stableThread (outerBelow : rank < root.extra.userRelevance)
      (innerBelow : RuntimeZeroEntryFacts.rank options.userRelevantCrates < root.extra.userRelevance) :
      midThread = thread := by
    obtain ⟨sameThread,sameFrame⟩ := earlierMeta outerBelow
    have activeRoot := keepMid older.size (by rw [sameThread]; exact top) (by simp)
      (by rw [sameFrame]; exact innerBelow)
    exact Option.some.inj (activeMid.symm.trans (activeRoot.trans (congrArg some sameThread)))
  obtain ⟨_,_,_,_,_,_,_,b1,e1,_⟩ := CopyRootGuardState.accounted_fields options remaining span middle
  obtain ⟨_,_,_,_,_,_,_,b2,e2,_⟩ := CopyRootGuardState.accounted_fields options remaining span (tick middle)
  exact ⟨{
    ready := ready
    machine := finalMachine
    trace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.append guardTrace suffix)
    shape := readyShape
    place := rfl
    continuation := rfl
    memory := memMid.trans (pm.trans chargedFields.1)
    tracker := trackMid.trans (pt.trans chargedFields.2.1)
    addresses := finalAddress
    dataRace := raceMid.trans noRace.symm
    ghost := (PointerAddCurrentReturn.accounted_ghost options remaining span (tick middle)).trans
      ((PointerAddCurrentReturn.accounted_ghost options remaining span middle).trans (ghostMid.trans ghost.symm))
    validation := (PointerAddCurrentReturn.accounted_validation options remaining span (tick middle)).trans
      ((PointerAddCurrentReturn.accounted_validation options remaining span middle).trans (shallowMid.trans shallow.symm))
    checked := by change (cfg.terminators.getControl (tick (tick middle)).user).checkedArithmetic = _;rw [clock,clock];exact uncheckedMid
    noGc := by change (cfg.terminators.getControl (tick (tick middle)).user).gcInterval = _;rw [clock,clock];exact gcMid
    fixed := fixedMid
    thread := midThread
    active := activeMid },
    b2.trans (b1.trans (backendMid.trans (pb.trans chargedFields.2.2.2.2.2.2.2.1))),
    e2.trans (e1.trans (extrasMid.trans (pe.trans chargedFields.2.2.2.2.2.2.2.2.1))), stableThread⟩

end DuplicatePrefix.PointerAddCurrentFullGuard

#print axioms DuplicatePrefix.PointerAddCurrentFullGuard.reaches_offset_profile

import duplicate_prefix.CopyRootCurrentGuardBody

namespace DuplicatePrefix.CopyRootCurrentGuardReach
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open CopyRootCurrentGuardBody
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

noncomputable def ready (frame : CompilerFrameContext.ActualFrame) (valid : 4 < frame.locals.size) :=
  {ActualLocalCopy.written {frame with location := .mir ⟨6,0⟩} 4 CopyHelperUnit.layout valid .uninit with
    location := .mir ⟨7,0⟩}

/-- Execute the emitted root copy call and both guard calls to enter bb7.0.
The prepared slots remain available for the actual copy intrinsic theorem. -/
theorem from_call
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (source destination : Scalar Provenance) (n : UInt64)
    (input : CopyRootEntry.Input options limits remaining span frames caller machine source destination n)
    (statementFuel : limits.validation = input.fuel+1) (mode : input.tracker.retagMode = .Default) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine source destination n input
    let blocked := returnedCopy options limits remaining span frames caller machine source destination n input
    let valid : 4 < blocked.locals.size := by
      have info := returned_metadata options limits remaining span frames caller machine source destination n input
      rw [info.2.2.2.2.1]
      decide
    ∃ finalMachine thread,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent (frames.push root) (ready blocked valid) finalMachine) ∧
      Preserves options remaining span machine finalMachine ∧ finalMachine.threads.activeThread? = some thread := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine source destination n input
  let returned := returnedCopy options limits remaining span frames caller machine source destination n input
  obtain ⟨guardMachine,trace,preserved,thread,active⟩ :=
    CopyRootCurrentGuardBody.from_copy options limits remaining span frames caller machine source destination n input statementFuel mode
  obtain ⟨body,identity,callee,pc,size,dest,cont,va,clocks,borrow⟩ :=
    returned_metadata options limits remaining span frames caller machine source destination n input
  have rows := returned_locals options limits remaining span frames caller machine source destination n input
  have b4 : 4 < returned.locals.size := by rw [size]; decide
  have b5 : 5 < returned.locals.size := by rw [size]; decide
  have at4 : returned.locals[4]? = some ⟨.live (.immediate .uninit),none⟩ := by rw [rows]; rfl
  have at5 : returned.locals[5]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ := by rw [rows]; rfl
  have s4 := (Array.getElem?_eq_some_iff.mp at4).2
  have s5 := (Array.getElem?_eq_some_iff.mp at5).2
  obtain ⟨suffix,unchanged⟩ := CopyCurrentGuardSuffix.from_false options limits remaining span input.debug input.fuel input.validationFuel
    (frames.push root) returned guardMachine body identity callee pc b4 b5
    (by rw [s4]) (by rw [s4]) (by rw [s5]) (by rw [s5]) clocks
    input.tracker (preserved.tracker.trans input.tracked) mode (preserved.ghost.trans input.ghost)
    (preserved.validation.trans input.shallow) (preserved.unchecked.trans input.unchecked)
    (preserved.noGc.trans input.noGc) (preserved.fixed.trans input.fixed)
  let tick := PointerAddCurrentReturn.accountedMachine options remaining span
  let final := tick (tick guardMachine)
  have clock (m : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
      cfg.terminators.getControl (tick m).user = TerminatorClock.advance (cfg.terminators.getControl m.user) :=
    CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  obtain ⟨m1,t1,th1,r1,a1,g1,v1,b1,e1,y1⟩ := CopyRootGuardState.accounted_fields options remaining span guardMachine
  obtain ⟨m2,t2,th2,r2,a2,g2,v2,b2,e2,y2⟩ := CopyRootGuardState.accounted_fields options remaining span (tick guardMachine)
  have props : Preserves options remaining span machine final := {
    memory := m2.trans (m1.trans preserved.memory)
    tracker := t2.trans (t1.trans preserved.tracker)
    race := r2.trans (r1.trans preserved.race)
    addresses := a2.trans (a1.trans preserved.addresses)
    ghost := g2.trans (g1.trans preserved.ghost)
    validation := v2.trans (v1.trans preserved.validation)
    backend := b2.trans (b1.trans preserved.backend)
    extras := e2.trans (e1.trans preserved.extras)
    types := y2.trans (y1.trans preserved.types)
    fixed := preserved.fixed
    unchecked := by change (cfg.terminators.getControl (tick (tick guardMachine)).user).checkedArithmetic = _;rw [clock,clock];exact preserved.unchecked
    noGc := by change (cfg.terminators.getControl (tick (tick guardMachine)).user).gcInterval = _;rw [clock,clock];exact preserved.noGc }
  have first := CopyRootEntry.trace options limits remaining span frames caller machine source destination n input
  exact ⟨final,thread,SuccessfulTrace.append first (SuccessfulTrace.append trace suffix),props,active⟩

end DuplicatePrefix.CopyRootCurrentGuardReach

#print axioms DuplicatePrefix.CopyRootCurrentGuardReach.from_call

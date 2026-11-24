import CanonicalCachedReturn
import CanonicalEntryFacts
import duplicate_prefix.RootLocalBoolReturn
import duplicate_prefix.GeneratedSafetyOfTrace

namespace DuplicatePrefix.CanonicalCallDomain
open Miri Miri.Verification Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.MIR Miri.TreeBorrows
open RootZeroShallowReturn

set_option maxRecDepth 65536
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame

theorem zeroCountEntry {program options remaining headroom span before frame pointer length}
    (loaded : GeneratedBodySafety.loaded = .ok program)
    (admitted : Admitted program options remaining headroom span before frame pointer length 0)
    (compiler : InitialCompilerControl before frame) :
    ZeroEntry frame before.machine := by
  obtain ⟨identity, body, location, size⟩ := admitted.emittedFrame loaded
  have instanceEq := admitted.identity.trans (loadedRootInstance_eq loaded)
  obtain ⟨_, _, _, count⟩ := admitted.initialArgumentSlots
  have result : (frame.locals[0]'(by omega : 0 < frame.locals.size)) =
      ⟨.live (.immediate .uninit), none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans admitted.resultSlot)
  have value : (frame.locals[2]'(by omega : 2 < frame.locals.size)) =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))), some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by omega)).symm.trans count)
  have unused (index : Nat) (bound : index < frame.locals.size) (lo : 3 ≤ index) (hi : index ≤ 5) :
      frame.locals[index] = ⟨.dead, none⟩ := by
    have actual := admitted.initialTemporarySlot loaded compiler index lo (by omega)
    have notImplicit : #[6,13,14].contains index = false := by
      have which : index = 3 ∨ index = 4 ∨ index = 5 := by omega
      rcases which with h | h | h <;> subst index <;> decide +kernel
    rw [notImplicit] at actual
    exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans actual)
  refine {
    body, identity, callee := instanceEq, location, size
    live0 := congrArg LocalState.value result
    uncached0 := congrArg LocalState.layout result
    dead3 := congrArg LocalState.value (unused 3 (by omega) (by decide) (by decide))
    dead4 := congrArg LocalState.value (unused 4 (by omega) (by decide) (by decide))
    dead5 := congrArg LocalState.value (unused 5 (by omega) (by decide) (by decide))
    uncached4 := congrArg LocalState.layout (unused 4 (by omega) (by decide) (by decide))
    uncached5 := congrArg LocalState.layout (unused 5 (by omega) (by decide) (by decide))
    zero := congrArg LocalState.value value
    cached2 := congrArg LocalState.layout value
    noClocks := admitted.stack.calleeClocksOff
    immediate := admitted.immediateLocals
    ghost := admitted.profile.ghostOff
    shallow := admitted.profile.shallow
    fixed := admitted.profile.fixed }

theorem withFrames {before : State} {frames : Array Frame} {frame : Frame}
    (stack : before.stack.frames = frames.push frame) :
    before = Storage.withCurrent frames frame before.machine := by
  cases before with
  | mk actual machine =>
    cases actual with
    | mk data =>
      change data = frames.push frame at stack
      cases stack
      rfl

/-- On any admitted slice, count zero takes the actual true arm and returns
through the caller's cached Boolean local. The release distinguishes live
holders of nonempty slices from dormant protectors on an empty slice. -/
theorem zeroCountCached
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (fuel : Nat) (validation : options.limits.validation = fuel+1)
    (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (length : UInt64)
    (admitted : Admitted program options remaining preparedTagHeadroom span before frame pointer length 0)
    (compiler : InitialCompilerControl before frame) (cached : CachedBoolDestination before frame) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () (remaining+1) span) limits before := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have entry := zeroCountEntry loaded admitted compiler
  have ledger : ∃ owned, frame.extra.borrowTracker = some owned ∧ owned.protectedTags = argumentLedger pointer := by
    cases admitted.destination with
    | physicalRoot root _ _ =>
      obtain ⟨older, caller, _, _, _, _, _, stack, _⟩ := cached.localSlot
      have impossible := congrArg Array.size (root.symm.trans stack)
      simp at impossible
    | cachedCaller _ ledger => exact ledger
  obtain ⟨tracker, tracked, mode⟩ := admitted.profile.mode
  by_cases short : length = 0
  · subst length
    obtain ⟨older, caller, index, target, unwind, original, oldBool, stack, continuation, _,
      saved, _, found, destinationCache, destinationLive, callerClocks⟩ := cached.localSlot
    let frames := older.push caller
    let machine := before.machine
    let first := RootZeroCompleteState.tick options remaining span machine
    let second := RootZeroCompleteState.tick options remaining span first
    have state : before = Storage.withCurrent frames frame machine := withFrames stack
    obtain ⟨present, owned, presentEq, ownedEq, plan⟩ := admitted.emptyCachedRelease ledger
    have trackerEq : present = tracker := Option.some.inj (presentEq.symm.trans tracked)
    subst present
    obtain ⟨result, trace, resultBody, _, _, extra, place, resume, args, _, size, location, slot, immediate⟩ :=
      RootZeroCompletePrefix.reaches_return options limits remaining span compilerSourceComparator
        admitted.profile.debugOff fuel validation frames frame machine
        entry.body entry.identity entry.callee entry.location entry.size entry.live0 entry.uncached0
        entry.dead3 entry.dead4 entry.dead5 entry.uncached4 entry.uncached5 entry.zero entry.cached2
        entry.noClocks entry.immediate tracker tracked mode entry.ghost entry.shallow
        admitted.profile.unchecked admitted.profile.noGc entry.fixed
    have valid : 0 < result.locals.size := by omega
    have bool : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))), some RootCompilerFacts.boolLayout⟩ :=
      Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans slot)
    obtain ⟨indexBound, cachedValue⟩ := Array.getElem?_eq_some_iff.mp found
    obtain ⟨thread, active, _⟩ := admitted.stack.active
    have ghost : second.user.payload.ghost = false :=
      (RootZeroCompleteState.tick_ghost options remaining span first).trans
        ((RootZeroCompleteState.tick_ghost options remaining span machine).trans entry.ghost)
    have shallow : second.user.payload.validation = .Shallow :=
      (RootZeroCompleteState.tick_shallow options remaining span first).trans
        ((RootZeroCompleteState.tick_shallow options remaining span machine).trans entry.shallow)
    have oldFlags := RootZeroCompleteState.tick_flags options remaining span machine
    have currentFlags := RootZeroCompleteState.tick_flags options remaining span first
    have finalStep := RootLocalBoolReturn.step_with_plan options limits remaining span
      admitted.profile.debugOff fuel validation older caller result second true
      (resultBody.trans entry.body) location valid (congrArg LocalState.value bool) (congrArg LocalState.layout bool)
      ((congrArg MachineHooks.FrameExtra.dataRace extra).trans entry.noClocks)
      index indexBound oldBool ((congrArg LocalState.value cachedValue).trans destinationLive)
      ((congrArg LocalState.layout cachedValue).trans destinationCache) callerClocks
      (by rw [place,saved]; rfl) target unwind (resume.trans continuation) immediate
      (args.trans admitted.stack.noVarargs) tracker owned tracked (by rw [extra];exact ownedEq)
      second.memory plan thread active (currentFlags.1.trans (oldFlags.1.trans admitted.profile.unchecked))
      (currentFlags.2.trans (oldFlags.2.trans admitted.profile.noGc)) entry.fixed ghost shallow
    rw [state]
    apply GeneratedSafetyOfTrace.required program loaded config limits _ _ (state ▸ admitted.entered)
      (SuccessfulTrace.append trace (.next finalStep (.refl _)))
    simp [Storage.withCurrent,frames]
  · obtain ⟨older, caller, stack, ⟨ready⟩⟩ := admitted.cachedActiveCaller short cached ledger
    have state := withFrames stack
    have sameTracker : tracker = ready.tracker := Option.some.inj (tracked.symm.trans ready.tracked)
    obtain ⟨done, trace, returned⟩ := executesZeroReturn options limits remaining span compilerSourceComparator
      admitted.profile.debugOff fuel validation older caller frame before.machine entry ready
      (by rw [← sameTracker]; exact mode) admitted.profile.noGc admitted.profile.unchecked
    rw [state]
    exact GeneratedSafetyOfTrace.required program loaded config limits _ done (state ▸ admitted.entered)
      trace returned

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``zeroCountCached) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved canonical zero-count dependency {dependency}"

end DuplicatePrefix.CanonicalCallDomain

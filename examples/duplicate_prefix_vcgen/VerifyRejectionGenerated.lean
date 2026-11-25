import RejectionEntryAfterLength
import Representative
import duplicate_prefix.ArchiveCatalogRoot
import duplicate_prefix.ArchiveTraceToVC

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.Verification

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame

private theorem sameInput : GeneratedBodySafety.input = Program.imported := by rfl

/-- Close the generated root VC by composing the checked root-to-length
prefix with the rejected branch's actual return, for any Unit policy. -/
theorem rejectedGeneratedSafetyOfLengthPrefix
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1)
    (older : Array Frame) (caller initialFrame frame : Frame)
    (initialMachine machine : MachineState)
    (count length : UInt64) (rejected : count > length / 2)
    (body : initialFrame.body = RootBody.reflected.body.body)
    (identity : initialFrame.bodyIdentity = RootBody.reflected.body.identity)
    (position : initialFrame.location = .mir ⟨0,0⟩)
    (leading : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent (older.push caller) initialFrame initialMachine)
      (Storage.withCurrent (older.push caller) frame machine))
    (entry : RejectionEntry frame machine length count)
    (ready : ActiveCaller older caller frame machine)
    (defaultMode : ready.tracker.retagMode = .Default)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (allowed : State → Unit → Prop) :
    GeneratedBodySafety.requiredAt (PreparedContracts.actualConfig options () (remaining+1) span)
      limits allowed (Storage.withCurrent (older.push caller) initialFrame initialMachine) := by
  have imported := RootBody.generated_catalog_root
  rw [← sameInput] at imported
  change GeneratedBodySafety.loaded.map (·.root) = .ok RootBody.reflected.body at imported
  cases loaded : GeneratedBodySafety.loaded with
  | error failure =>
    rw [loaded] at imported
    change Except.error failure = Except.ok RootBody.reflected.body at imported
    cases imported
  | ok program =>
    rw [loaded] at imported
    change Except.ok program.root = Except.ok RootBody.reflected.body at imported
    have root := Except.ok.inj imported
    have aligned : WholeBodyWP.entryMatchesLoaded program.root
        (Storage.withCurrent (older.push caller) initialFrame initialMachine) := by
      rw [root]
      exact ⟨initialFrame, by simp [Storage.withCurrent, Stack.currentFrame?], identity, body, position⟩
    obtain ⟨finalMachine, tail⟩ := executesRejectionReturn options limits remaining span source debugOff fuel fuelEq
      older caller frame machine length count rejected entry ready defaultMode gc unchecked
    let final := Storage.withCurrent older {putBool caller ready.destinationIndex ready.destinationBound false with
      location := FrameLocation.mir ⟨ready.target, 0⟩} finalMachine
    have returned : final.stack.frames.size < (Storage.withCurrent (older.push caller) initialFrame initialMachine).stack.frames.size := by
      simp [final, Storage.withCurrent]
    simpa only [GeneratedBodySafety.requiredAt_eq, loaded] using
      SuccessfulTrace.generated_of_returning_trace _ limits program allowed _ final aligned
        (SuccessfulTrace.append leading tail) returned

#print axioms rejectedGeneratedSafetyOfLengthPrefix
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``rejectedGeneratedSafetyOfLengthPrefix) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved rejection safety dependency {dependency}"
end DuplicatePrefix.RootZeroShallowReturn

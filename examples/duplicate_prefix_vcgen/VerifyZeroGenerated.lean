import RootZeroShallowReturn
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

theorem zeroGeneratedSafety
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1)
    (older : Array Frame) (caller frame : Frame) (machine : MachineState)
    (entry : ZeroEntry frame machine) (ready : ActiveCaller older caller frame machine)
    (defaultMode : ready.tracker.retagMode = .Default)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (allowed : State → Unit → Prop) :
    GeneratedBodySafety.requiredAt (PreparedContracts.actualConfig options () (remaining+1) span)
      limits allowed (Storage.withCurrent (older.push caller) frame machine) := by
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
        (Storage.withCurrent (older.push caller) frame machine) := by
      rw [root]
      exact ⟨frame, by simp [Storage.withCurrent, Stack.currentFrame?], entry.identity, entry.body, entry.location⟩
    obtain ⟨final, execution, returned⟩ := executesZeroReturn options limits remaining span source debugOff fuel fuelEq
      older caller frame machine entry ready defaultMode gc unchecked
    simpa only [GeneratedBodySafety.requiredAt_eq, loaded] using
      SuccessfulTrace.generated_of_returning_trace _ limits program allowed _ final aligned execution returned

#print axioms zeroGeneratedSafety
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``zeroGeneratedSafety) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved zero safety dependency {dependency}"
end DuplicatePrefix.RootZeroShallowReturn

import Representative
import MiriTests.Verification.WholeBodyReplay

namespace DuplicatePrefix.VerifyGenerated

open Miri.Interpreter Miri.Verification
open MiriTests.Verification.WholeBodyReplay

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

/-- On a successful safety check, return a kernel-checked proof of the
emitted VC at this entry state and selected schedule. -/
def certifyRequiredAt (config : Config) (limits : ExecutionMachine.Limits)
    (choose : State → C) (before : State) (budget : Nat) :
    Option (PLift (GeneratedBodySafety.requiredAt config limits (selected choose) before)) :=
  match loaded : GeneratedBodySafety.loaded with
  | .error _ => none
  | .ok program => do
    let certificate ← certify config limits program choose before budget
    if safe : certificate.verdict.acceptsNoUB = true then
      some ⟨by
        rw [GeneratedBodySafety.requiredAt, loaded]
        exact certificate.verdict.exactNoUB.mpr safe⟩
    else none

/-- A singleton typed choice space admits every choice. The initialized
state still contains the runner's concrete environmental inputs. -/
def certifyRequiredForEveryChoiceAt [Subsingleton C] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (before : State) (budget : Nat) :
    Option (PLift (GeneratedBodySafety.requiredForEveryChoiceAt config limits before)) := by
  have allChoices : selected (fun _ : State => choice) = (fun _ _ => True) := by
    funext state selectedChoice
    exact propext ⟨fun _ => trivial, fun _ => Subsingleton.elim selectedChoice choice⟩
  rw [GeneratedBodySafety.requiredForEveryChoiceAt, ← allChoices]
  exact certifyRequiredAt config limits (fun _ => choice) before budget

open Miri.TreeBorrows Miri.TreeBorrows.RetagPolicy in
/-- A function-entry retag for a freeze, unpinned mutable referent such as
`[u8]` requires only a read when implicit writes are disabled. The strong
protector on the new tag does not change the access kind of that retag. -/
theorem mutableSliceEntryAccess (config : PolicyConfig) :
    let writes := config.implicitWrites && !config.rustcNoWritable
    let permission := if writes then Permission.Unique else .ReservedFrz false
    let policy : NewPermission := ⟨permission, permission, .ReservedFrz false,
      some .StrongProtector⟩
    create ⟨true, true, true⟩ .Mutable .FnEntry config = some policy ∧
      initialLocationState policy true = .ok ⟨permission, true, .None⟩ ∧
      permission.associatedAccess = some (if writes then .Write else .Read) := by
  rcases config with ⟨implicitWrites, noWritable⟩
  cases implicitWrites <;> cases noWritable <;> decide

open Miri.TreeBorrows in
/-- Once the destination visitor reaches a foreign Frozen protector, the
write fails and retains the updated disabled permission. -/
theorem writeAgainstFrozenProtector (sifa : IdempotentForeignAccess) :
    (⟨.Frozen, true, sifa⟩ : Tree.LocationState).performAccess .Write .ForeignAccess true =
      .Error ⟨.Disabled, true, sifa⟩ (.ProtectedDisabled .Frozen) := rfl

/-- A rejected replay supplies a kernel-checked refutation at the actual
prepared state and selected schedule. The caller supplies the certificate
from that state. A missing replay certificate supplies no such evidence. -/
theorem refuteFromCertificate (config : Config) (limits : ExecutionMachine.Limits)
    (program : BodyVCGen.LoadedProgram) (choose : State → C) (before : State)
    (loaded : GeneratedBodySafety.loaded = .ok program)
    (certificate : Certificate config limits program choose before)
    (rejected : certificate.verdict.acceptsNoUB = false) :
    ¬ GeneratedBodySafety.requiredAt config limits (selected choose) before := by
  rw [GeneratedBodySafety.requiredAt, loaded]
  intro safe
  have accepted := certificate.verdict.exactNoUB.mp safe
  simp [rejected] at accepted

/-- Run the same certificate check as the native observer. Return a proof of
the emitted VC's negation when the replay reports undefined behavior. -/
def refuteRequiredAt (config : Config) (limits : ExecutionMachine.Limits)
    (choose : State → C) (before : State) (budget : Nat) :
    Option (PLift (¬ GeneratedBodySafety.requiredAt config limits (selected choose) before)) :=
  match loaded : GeneratedBodySafety.loaded with
  | .error _ => none
  | .ok program => do
    let certificate ← certify config limits program choose before budget
    if rejected : certificate.verdict.acceptsNoUB = false then
      some ⟨refuteFromCertificate config limits program choose before loaded certificate rejected⟩
    else none

/-- The native observer's singleton choice space admits the witnessed
schedule among all the typed choices. -/
def refuteRequiredForEveryChoiceAt [Subsingleton C] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (before : State) (budget : Nat) :
    Option (PLift (¬ GeneratedBodySafety.requiredForEveryChoiceAt config limits before)) := by
  have allChoices : selected (fun _ : State => choice) = (fun _ _ => True) := by
    funext state selectedChoice
    exact propext ⟨fun _ => trivial, fun _ => Subsingleton.elim selectedChoice choice⟩
  rw [GeneratedBodySafety.requiredForEveryChoiceAt, ← allChoices]
  exact refuteRequiredAt config limits (fun _ => choice) before budget

end DuplicatePrefix.VerifyGenerated

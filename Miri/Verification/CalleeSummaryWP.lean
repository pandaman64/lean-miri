import Miri.Verification.WholeBodyWP

/-! Canonical call summaries. The call step supplies the actual callee entry
state, and a callee scope exit supplies the actual state for the caller's
continuation. No fuel or termination requirement is imposed on MIR execution. -/

namespace Miri.Verification.CalleeSummaryWP

open Miri.Interpreter Miri.MIR WholeBodyWP

variable {S C : Type}

/-- A finite execution in the enclosing scope either stops or fails within
the inner scope, or reaches an inner scope exit and continues from there. -/
private theorem splitFinishes {step : C → S → StepResult S Bool}
    {stackDepth : S → Nat} {allowed : S → C → Prop} {outer inner : Nat}
    (ordered : outer ≤ inner) {before after : S} {outcome : Except StepError Exit}
    (run : Finishes step stackDepth allowed outer before after outcome) :
    (outcome ≠ .ok .scopeExit ∧ Finishes step stackDepth allowed inner before after outcome) ∨
      ∃ middle, Finishes step stackDepth allowed inner before middle (.ok .scopeExit) ∧
        Finishes step stackDepth allowed outer middle after outcome := by
  induction run with
  | @scopeExit state outside =>
    exact .inr ⟨state, .scopeExit (Nat.lt_of_lt_of_le outside ordered), .scopeExit outside⟩
  | @stopped before after choice live permitted result =>
    by_cases nested : inner ≤ stackDepth before
    · exact .inl ⟨by decide, .stopped nested permitted result⟩
    · exact .inr ⟨before, .scopeExit (Nat.lt_of_not_ge nested), .stopped live permitted result⟩
  | @failed before after choice error live permitted result =>
    by_cases nested : inner ≤ stackDepth before
    · exact .inl ⟨by simp, .failed nested permitted result⟩
    · exact .inr ⟨before, .scopeExit (Nat.lt_of_not_ge nested), .failed live permitted result⟩
  | @next before after final choice outcome live permitted result suffix ih =>
    by_cases nested : inner ≤ stackDepth before
    · rcases ih with ⟨terminal, segment⟩ | ⟨middle, segment, rest⟩
      · exact .inl ⟨terminal, .next nested permitted result segment⟩
      · exact .inr ⟨middle, .next nested permitted result segment, rest⟩
    · exact .inr ⟨before, .scopeExit (Nat.lt_of_not_ge nested), .next live permitted result suffix⟩

/-- An inner execution may be replayed in the enclosing scope, with the
enclosing execution used in place of its inner scope exit. -/
private theorem joinFinishes {step : C → S → StepResult S Bool}
    {stackDepth : S → Nat} {allowed : S → C → Prop} {outer inner : Nat}
    (ordered : outer ≤ inner) {before middle : S} {exit : Except StepError Exit}
    (segment : Finishes step stackDepth allowed inner before middle exit) {after : S}
    {outcome : Except StepError Exit}
    (rest : if exit = .ok .scopeExit then Finishes step stackDepth allowed outer middle after outcome
      else after = middle ∧ outcome = exit) :
    Finishes step stackDepth allowed outer before after outcome := by
  induction segment with
  | scopeExit =>
    simpa using rest
  | stopped live permitted result =>
    simp at rest
    rcases rest with ⟨rfl, rfl⟩
    exact .stopped (Nat.le_trans ordered live) permitted result
  | failed live permitted result =>
    simp at rest
    rcases rest with ⟨rfl, rfl⟩
    exact .failed (Nat.le_trans ordered live) permitted result
  | next live permitted result _ ih =>
    exact .next (Nat.le_trans ordered live) permitted result (ih rest)

variable {K U O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U
local notation "Limits" => ExecutionMachine.Limits
local notation "Errors" => StepError → State → Prop

/-- On a normal return with a target, the caller state can be recognized by
the caller's locals identity and the target's first MIR instruction. The
entire returned state remains available to the postcondition. -/
def resumedAt (caller : LocalsIdentity) (target : BasicBlockId) (after : State) : Prop :=
  ∃ frame, after.stack.currentFrame? = some frame ∧ frame.localsIdentity = caller ∧
    frame.location = .mir ⟨target, 0⟩

/-- Continue from the exact state produced by a callee scope exit. A stopped
driver or an error shares the enclosing contract. -/
def continueWith (config : Config) (limits : Limits) (program : BodyCFG.CompiledProgram)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : Errors) : Exit → State → Prop
  | .scopeExit => catalogControlPre config limits program allowed depth post failure
  | .stopped => post .stopped

/-- Replace an enclosing continuation at any inner entry by a composable
callee summary. The proof splits finite prefixes, so recursive calls and
divergence use the same partial-safety interpretation as the enclosing WP. -/
theorem scopePre_iff (config : Config) (limits : Limits) (program : BodyCFG.CompiledProgram)
    (allowed : State → C → Prop) (outer inner : Nat) (ordered : outer ≤ inner)
    (post : Exit → State → Prop) (failure : Errors) (before : State) :
    catalogControlPre config limits program allowed inner
        (continueWith config limits program allowed outer post failure) failure before ↔
      catalogControlPre config limits program allowed outer post failure before := by
  simp only [catalogControlPre_shared, catalogSharedPre, solve_iff]
  constructor
  · intro checked after outcome run
    rcases splitFinishes ordered run with ⟨terminal, segment⟩ | ⟨middle, segment, suffix⟩
    · have result := checked after outcome segment
      cases outcome with
      | error => exact result
      | ok exit => cases exit
                   · exact (terminal rfl).elim
                   · exact result
    · have ready := checked middle (.ok .scopeExit) segment
      change catalogControlPre config limits program allowed outer post failure middle at ready
      simp only [catalogControlPre_shared, catalogSharedPre, solve_iff] at ready
      exact ready after outcome suffix
  · intro checked middle exit segment
    cases exit with
    | error error => exact checked middle (.error error) (joinFinishes ordered segment (by simp))
    | ok exit => cases exit with
      | stopped => exact checked middle (.ok .stopped) (joinFinishes ordered segment (by simp))
      | scopeExit =>
        change catalogControlPre config limits program allowed outer post failure middle
        simp only [catalogControlPre_shared, catalogSharedPre, solve_iff]
        intro after outcome rest
        exact checked after outcome (joinFinishes ordered segment (by simpa))

/-- The canonical first step evaluates the call and performs frame and
argument setup. Its actual successor is used for the callee WP at the depth
just above the caller. If the step completes without pushing (for instance
an intrinsic), the scope exit is immediate. Normal MIR return in the scope
runs protector release, return copying, cleanup and the caller jump before
the continuation receives the state. -/
def callPre (config : Config) (limits : Limits) (program : BodyCFG.CompiledProgram)
    (allowed : State → C → Prop) (post : Exit → State → Prop)
    (failure : Errors) (before : State) : Prop :=
  ∀ choice, allowed before choice →
    BodyCFG.programTablePre config limits program choice (fun more after =>
      if more then catalogControlPre config limits program allowed (before.stack.frames.size + 1)
        post failure after
      else post .stopped after) failure before

/-- At a selected MIR terminator the summary exposes the symbolic
terminator rule, including its canonical pre-hook and call setup. -/
theorem callPre_at (config : Config) (limits : Limits) (program : BodyCFG.CompiledProgram)
    (allowed : State → C → Prop) (post : Exit → State → Prop) (failure : Errors)
    (before : State) (pc : Location) (term : Terminator)
    (selected : BodyCFG.selected before = some (pc, .terminator term)) :
    callPre config limits program allowed post failure before ↔
      ∀ choice, allowed before choice →
        CanonicalStepWP.terminatorPre config limits choice term (fun more entered =>
          if more then catalogControlPre config limits program allowed
            (before.stack.frames.size + 1) post failure entered
          else post .stopped entered) failure before := by
  unfold callPre
  apply forall_congr'
  intro choice
  apply forall_congr'
  intro _
  let equation : BodyCFG.Equation := ⟨pc, .terminator term, #[]⟩
  let cfg : BodyCFG.Compiled := { blocks := #[] }
  let next := catalogControlPre config limits program allowed (before.stack.frames.size + 1) post failure
  have routeEq : BodyCFG.route cfg (fun _ => next) next = next := by
    funext state
    exact propext (BodyCFG.route_shared cfg next state)
  have exactEquation := equation.pre_iff config limits cfg choice (fun _ => next)
    next (post .stopped) failure before selected
  unfold BodyCFG.Equation.pre BodyCFG.nodePre at exactEquation
  rw [routeEq] at exactEquation
  exact (BodyCFG.programTablePre_iff _ _ _ _ _ _ _).trans exactEquation.symm

/-- Exact operational reading of the summary, including failed call setup
and the failed states reached inside a callee. Use one error predicate for
both portions of the execution. -/
theorem callPre_iff (config : Config) (limits : Limits) (program : BodyCFG.CompiledProgram)
    (allowed : State → C → Prop) (post : Exit → State → Prop)
    (failure : Errors) (before : State) :
    callPre config limits program allowed post failure before ↔
      ∀ choice, allowed before choice →
        InstructionWP.resultPre
          (fun more entered =>
            if more then
              ∀ after outcome, Finishes (ExecutionMachine.step config limits)
                (fun state => state.stack.frames.size) allowed (before.stack.frames.size + 1)
                entered after outcome → InstructionWP.resultPre post failure (after, outcome)
            else post .stopped entered)
          failure (ExecutionMachine.step config limits choice before) := by
  simp only [callPre, BodyCFG.programTablePre_iff, catalogControlPre_shared, catalogSharedPre,
    solve_iff, ExecutionMachine.step]

/-- Compose the summary with the enclosing WP at a live call site. This is
also valid for any first instruction that uses the same depth boundary.
No assumptions are made about the implementation of compiler hooks. -/
theorem callPre_continue_iff (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop)
    (depth : Nat) (post : Exit → State → Prop) (failure : Errors)
    (before : State) (live : depth ≤ before.stack.frames.size) :
    callPre config limits program allowed
        (continueWith config limits program allowed depth post failure) failure before ↔
      catalogControlPre config limits program allowed depth post failure before := by
  rw [catalogControlPre_unfold, ite_eq_left live, callPre]
  apply forall_congr'
  intro choice
  apply forall_congr'
  intro permitted
  rw [BodyCFG.programTablePre_iff, BodyCFG.programTablePre_iff]
  cases Step.step (ExecutionMachine.stepHooks config limits) choice before with
  | mk after outcome =>
    cases outcome with
    | error => rfl
    | ok more =>
      cases more
      · rfl
      · exact scopePre_iff config limits program allowed depth (before.stack.frames.size + 1)
          (Nat.le_succ_of_le live) post failure after

/-- Apply a proved summary with its own return contract at a live caller
site. The only new obligation is the enclosing continuation on states
satisfying that contract. Stopped and failed executions already satisfy the
enclosing postconditions. -/
theorem callerPre_of_summary (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : Errors) (returned : State → Prop)
    (before : State) (live : depth ≤ before.stack.frames.size)
    (summary : callPre config limits program allowed
      (fun exit => match exit with | .scopeExit => returned | .stopped => post .stopped)
      failure before)
    (resume : ∀ after, returned after →
      catalogControlPre config limits program allowed depth post failure after) :
    catalogControlPre config limits program allowed depth post failure before := by
  apply (callPre_continue_iff config limits program allowed depth post failure before live).mp
  rw [callPre_iff] at summary ⊢
  intro choice permitted
  have checked := summary choice permitted
  cases first : ExecutionMachine.step config limits choice before with
  | mk entered outcome =>
    rw [first] at checked
    cases outcome with
    | error => exact checked
    | ok more =>
      cases more
      · exact checked
      · intro after exit run
        have result := checked after exit run
        cases exit with
        | error => exact result
        | ok exit =>
          cases exit with
          | stopped => exact result
          | scopeExit => exact resume after result

end Miri.Verification.CalleeSummaryWP

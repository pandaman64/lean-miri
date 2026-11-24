import Miri.Verification.BodyCFG

/-! Whole-body weakest liberal preconditions. An exact one-step rule supplies
the transfer equation, and the greatest solution checks every finite exit
without bounding loops or requiring termination. -/
namespace Miri.Verification.WholeBodyWP

open Miri.Interpreter Miri.MIR
open Miri.Verification

inductive Exit where
  | scopeExit
  | stopped
  deriving DecidableEq, Repr

variable {S C : Type}

/-- A finite execution stopping at the first scope exit, halted driver step,
or error. Calls increase stack depth and continue under the same rule. -/
inductive Finishes (step : C → S → StepResult S Bool) (stackDepth : S → Nat)
    (allowed : S → C → Prop) (depth : Nat) : S → S → Except StepError Exit → Prop where
  | scopeExit {state} : stackDepth state < depth →
      Finishes step stackDepth allowed depth state state (.ok .scopeExit)
  | stopped {before after choice} : depth ≤ stackDepth before → allowed before choice →
      step choice before = (after, .ok false) →
      Finishes step stackDepth allowed depth before after (.ok .stopped)
  | failed {before after choice error} : depth ≤ stackDepth before → allowed before choice →
      step choice before = (after, .error error) →
      Finishes step stackDepth allowed depth before after (.error error)
  | next {before after final choice outcome} : depth ≤ stackDepth before → allowed before choice →
      step choice before = (after, .ok true) → Finishes step stackDepth allowed depth after final outcome →
      Finishes step stackDepth allowed depth before final outcome

/-- An exact symbolic rule for a single driver choice. -/
structure Rule (step : C → S → StepResult S Bool) where
  pre : C → (Bool → S → Prop) → (StepError → S → Prop) → S → Prop
  exact : ∀ choice post failure before,
    pre choice post failure before ↔ InstructionWP.resultPre post failure (step choice before)

variable {step : C → S → StepResult S Bool}

/-- The shared transfer equation. A continuing step uses the same predicate
at its actual successor, regardless of the selected block or frame. -/
def transfer (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop)
    (again : S → Prop) (before : S) : Prop :=
  if depth ≤ stackDepth before then
    ∀ choice, allowed before choice →
      rule.pre choice (fun more after => if more then again after else post .stopped after) failure before
  else post .scopeExit before

private theorem transfer_mono (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) {post post' : Exit → S → Prop} {failure failure' : StepError → S → Prop}
    {again again' : S → Prop}
    (success : ∀ exit state, post exit state → post' exit state)
    (error : ∀ err state, failure err state → failure' err state)
    (continuation : ∀ state, again state → again' state)
    (before : S) (checked : transfer rule stackDepth allowed depth post failure again before) :
    transfer rule stackDepth allowed depth post' failure' again' before := by
  unfold transfer at checked ⊢
  by_cases inside : depth ≤ stackDepth before
  · simp only [inside, ↓reduceIte] at checked ⊢
    intro choice permitted
    apply (rule.exact choice _ _ _).mpr
    have one := (rule.exact choice _ _ _).mp (checked choice permitted)
    rcases outcome : step choice before with ⟨after, result⟩
    rw [outcome] at one
    cases result with
    | error err => exact error err after one
    | ok more =>
      cases more
      · exact success .stopped after one
      · exact continuation after one
  · simp only [inside, ↓reduceIte] at checked ⊢
    exact success .scopeExit before checked

/-- The greatest predicate preserved by the transfer equation. This definition
requires no invariant argument from callers. -/
def solve (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop) (before : S) : Prop :=
  ∃ candidate : S → Prop, candidate before ∧
    ∀ state, candidate state → transfer rule stackDepth allowed depth post failure candidate state

theorem solve_of_closed (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop)
    (candidate : S → Prop)
    (closed : ∀ state, candidate state → transfer rule stackDepth allowed depth post failure candidate state)
    (before : S) (initial : candidate before) :
    solve rule stackDepth allowed depth post failure before :=
  ⟨candidate, initial, closed⟩

private theorem solve_forward (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop) (before : S)
    (checked : solve rule stackDepth allowed depth post failure before) :
    transfer rule stackDepth allowed depth post failure
      (solve rule stackDepth allowed depth post failure) before := by
  obtain ⟨candidate, initial, closed⟩ := checked
  exact transfer_mono rule stackDepth allowed depth (fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => ⟨candidate, h, closed⟩) before (closed before initial)

/-- Unfold one transfer, sharing the same continuing condition at every
successor. This equation applies equally to forward edges and back edges. -/
theorem solve_unfold (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop) (before : S) :
    solve rule stackDepth allowed depth post failure before ↔
      transfer rule stackDepth allowed depth post failure
        (solve rule stackDepth allowed depth post failure) before := by
  constructor
  · exact solve_forward rule stackDepth allowed depth post failure before
  · intro one
    let valid := solve rule stackDepth allowed depth post failure
    refine ⟨fun state => valid state ∨ state = before, Or.inr rfl, ?_⟩
    intro state h
    apply transfer_mono rule stackDepth allowed depth (again := valid)
      (fun _ _ h => h) (fun _ _ h => h) (fun _ h => Or.inl h)
    rcases h with h | rfl
    · exact solve_forward rule stackDepth allowed depth post failure state h
    · exact one

theorem solve_mono (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) {post post' : Exit → S → Prop} {failure failure' : StepError → S → Prop}
    (success : ∀ exit state, post exit state → post' exit state)
    (error : ∀ err state, failure err state → failure' err state)
    (before : S) (checked : solve rule stackDepth allowed depth post failure before) :
    solve rule stackDepth allowed depth post' failure' before := by
  obtain ⟨candidate, initial, closed⟩ := checked
  exact ⟨candidate, initial, fun state h =>
    transfer_mono rule stackDepth allowed depth success error (fun _ h => h) state (closed state h)⟩

/-- The generated fixed point is equivalent to checking every finite execution.
Infinite executions and states without permitted choices create no new exits. -/
theorem solve_iff (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop) (before : S) :
    solve rule stackDepth allowed depth post failure before ↔
      ∀ after outcome, Finishes step stackDepth allowed depth before after outcome →
        InstructionWP.resultPre post failure (after, outcome) := by
  constructor
  · intro checked after outcome finished
    induction finished with
    | @scopeExit state outside =>
      have one := solve_forward rule stackDepth allowed depth post failure state checked
      simpa only [transfer, Nat.not_le.mpr outside, ↓reduceIte, InstructionWP.resultPre] using one
    | @stopped state after choice inside permitted run =>
      have one := solve_forward rule stackDepth allowed depth post failure state checked
      simp only [transfer, inside, ↓reduceIte] at one
      have result := (rule.exact choice _ _ _).mp (one choice permitted)
      simpa only [run, InstructionWP.resultPre, Bool.false_eq_true, ↓reduceIte] using result
    | @failed state after choice err inside permitted run =>
      have one := solve_forward rule stackDepth allowed depth post failure state checked
      simp only [transfer, inside, ↓reduceIte] at one
      have result := (rule.exact choice _ _ _).mp (one choice permitted)
      simpa only [run, InstructionWP.resultPre] using result
    | @next state after final choice outcome inside permitted run _ ih =>
      have one := solve_forward rule stackDepth allowed depth post failure state checked
      simp only [transfer, inside, ↓reduceIte] at one
      have result := (rule.exact choice _ _ _).mp (one choice permitted)
      exact ih (by simpa only [run, InstructionWP.resultPre, ↓reduceIte] using result)
  · intro checked
    let valid := fun state => ∀ after outcome, Finishes step stackDepth allowed depth state after outcome →
      InstructionWP.resultPre post failure (after, outcome)
    refine ⟨valid, checked, ?_⟩
    intro state known
    unfold transfer
    split
    next inside =>
      intro choice permitted
      apply (rule.exact choice _ _ _).mpr
      rcases run : step choice state with ⟨after, result⟩
      cases result with
      | error err =>
        exact known after (.error err) (.failed inside permitted run)
      | ok more =>
        cases more
        · exact known after (.ok .stopped) (.stopped inside permitted run)
        · intro final outcome finished
          exact known final outcome (.next inside permitted run finished)
    next outside => exact known state (.ok .scopeExit) (.scopeExit (Nat.lt_of_not_ge outside))

/-- Extend a scoped finite prefix with an observed exit. -/
theorem Finishes.prepend {stackDepth : S → Nat} {allowed : S → C → Prop} {depth : Nat}
    {start before after : S} {outcome : Except StepError Exit}
    (reached : FunctionBody.Reachable step stackDepth allowed depth start before)
    (finished : Finishes step stackDepth allowed depth before after outcome) :
    Finishes step stackDepth allowed depth start after outcome := by
  induction reached with
  | initial => exact finished
  | next _ inside permitted run ih => exact ih (.next inside permitted run finished)

/-- Ignoring the separate halted-driver postcondition recovers the existing
scoped error and return predicates. Specialize `failure` to the existing
UB classifier for a bridge to `FunctionBody.UBFree`. -/
theorem solve_iff_functionBody (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : S → Prop) (failure : StepError → S → Prop) (start : S) :
    solve rule stackDepth allowed depth (fun exit state =>
      match exit with | .scopeExit => post state | .stopped => True) failure start ↔
      FunctionBody.OnError step stackDepth allowed depth start failure ∧
      FunctionBody.NormalPost step stackDepth allowed depth start post := by
  rw [solve_iff]
  constructor
  · intro checked
    refine ⟨?_, ?_⟩
    · intro before reachable inside choice permitted after err run
      have finished := Finishes.prepend reachable (.failed inside permitted run)
      exact checked after (.error err) finished
    · intro after reachable outside
      have finished := Finishes.prepend reachable (.scopeExit outside)
      exact checked after (.ok .scopeExit) finished
  · rintro ⟨onError, onReturn⟩ after outcome finished
    have check {before final : S} {result : Except StepError Exit}
        (suffix : Finishes step stackDepth allowed depth before final result)
        (reached : FunctionBody.Reachable step stackDepth allowed depth start before) :
        InstructionWP.resultPre (fun exit state =>
          match exit with | .scopeExit => post state | .stopped => True) failure (final, result) := by
      induction suffix with
      | scopeExit outside => exact onReturn _ reached outside
      | stopped => trivial
      | failed inside permitted run =>
        exact onError _ reached inside _ permitted _ _ run
      | next inside permitted run _ ih =>
        exact ih (.next reached inside permitted run)
    exact check finished .initial

/-- Substitute downstream equations along descending ranks. Non-descending
edges refer to the original shared solution, including loop back edges and
dynamically selected foreign frames. The rank controls substitution only. -/
def eliminate (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop)
    (rank : S → Nat) (before : S) : Prop :=
  transfer rule stackDepth allowed depth post failure
    (fun after => if _h : 0 < rank after ∧ rank after < rank before then
        eliminate rule stackDepth allowed depth post failure rank after
      else solve rule stackDepth allowed depth post failure after) before
termination_by rank before
decreasing_by exact _h.2

/-- Eliminating a descending edge preserves the shared equation at the join.
No assumption on the quality of the rank or on operational successors is
required for exactness. -/
theorem eliminate_iff (rule : Rule step) (stackDepth : S → Nat) (allowed : S → C → Prop)
    (depth : Nat) (post : Exit → S → Prop) (failure : StepError → S → Prop)
    (rank : S → Nat) (before : S) :
    eliminate rule stackDepth allowed depth post failure rank before ↔
      solve rule stackDepth allowed depth post failure before := by
  induction before using (measure rank).wf.induction with
  | h before ih =>
    rw [eliminate, solve_unfold rule stackDepth allowed depth post failure before]
    have sameNext (after : S) :
        (if 0 < rank after ∧ rank after < rank before then
            eliminate rule stackDepth allowed depth post failure rank after
          else solve rule stackDepth allowed depth post failure after) ↔
          solve rule stackDepth allowed depth post failure after := by
      split
      next h => exact ih after h.2
      next => rfl
    exact ⟨transfer_mono rule stackDepth allowed depth (fun _ _ h => h) (fun _ _ h => h)
        (fun state => (sameNext state).mp) before,
      transfer_mono rule stackDepth allowed depth (fun _ _ h => h) (fun _ _ h => h)
        (fun state => (sameNext state).mpr) before⟩

section Machine

variable {K U C O X Host : Type}
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U
local notation "Limits" => ExecutionMachine.Limits

/-- The top frame was prepared with this MIR body and its initial PC. -/
def entryMatches (source : Miri.MIR.Body) (before : State) : Prop :=
  ∃ frame, before.stack.currentFrame? = some frame ∧ frame.body = source ∧
    frame.location = .mir ⟨0, 0⟩

private def machineRule [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled) :
    Rule (ExecutionMachine.step config limits) where
  pre := BodyCFG.tablePre config limits cfg
  exact := BodyCFG.tablePre_iff config limits cfg

/-- The common solution referred to by loop back edges, unknown successors
and states that do not select a compiled equation. -/
def sharedPre [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (before : State) : Prop :=
  solve (machineRule config limits cfg) (fun state => state.stack.frames.size)
    allowed depth post failure before

/-- Zero marks a dynamic state outside the emitted table. A nonzero rank
permits acyclic substitution only when the successor's rank decreases. -/
def liveRank (cfg : BodyCFG.Compiled) (state : State) : Nat :=
  match cfg.equationFor state with
  | none => 0
  | some equation => cfg.rankAt equation.pc + 1

def controlPre [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (before : State) : Prop :=
  eliminate (machineRule config limits cfg) (fun state => state.stack.frames.size)
    allowed depth post failure (liveRank cfg) before

theorem controlPre_shared [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (before : State) :
    controlPre config limits cfg allowed depth post failure before ↔
      sharedPre config limits cfg allowed depth post failure before :=
  eliminate_iff _ _ _ _ _ _ _ _

/-- Substitute a rank-decreasing continuation and leave every other edge as
a reference to the shared solution. The actual transition chooses the edge. -/
theorem controlPre_reduce [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (before : State) :
    controlPre config limits cfg allowed depth post failure before ↔
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          BodyCFG.tablePre config limits cfg choice
            (fun more after =>
              if more then
                if 0 < liveRank cfg after ∧ liveRank cfg after < liveRank cfg before then
                  controlPre config limits cfg allowed depth post failure after
                else sharedPre config limits cfg allowed depth post failure after
              else post .stopped after) failure before
      else post .scopeExit before := by
  unfold controlPre
  rw [eliminate]
  rfl

/-- Every successor uses the same whole-scope solution. This view is useful
when reasoning directly about a loop or a dynamic call. -/
theorem controlPre_unfold [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (before : State) :
    controlPre config limits cfg allowed depth post failure before ↔
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          BodyCFG.tablePre config limits cfg choice
            (fun more after => if more then controlPre config limits cfg allowed depth post failure after
              else post .stopped after) failure before
      else post .scopeExit before := by
  simp only [controlPre_shared]
  exact solve_unfold _ _ _ _ _ _ _

/-- A client can discharge the generated condition by identifying a convenient
closed predicate. This is a proof rule for the VC, not an input to generation. -/
theorem controlPre_of_closed [DecidableEq K] (config : Config) (limits : Limits)
    (cfg : BodyCFG.Compiled) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (candidate : State → Prop)
    (closed : ∀ before, candidate before →
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          BodyCFG.tablePre config limits cfg choice
            (fun more after => if more then candidate after else post .stopped after) failure before
      else post .scopeExit before)
    (before : State) (initial : candidate before) :
    controlPre config limits cfg allowed depth post failure before :=
  (controlPre_shared config limits cfg allowed depth post failure before).mpr
    (solve_of_closed (machineRule config limits cfg) (fun state => state.stack.frames.size)
      allowed depth post failure candidate closed before initial)

theorem controlPre_iff [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (before : State) :
    controlPre config limits cfg allowed depth post failure before ↔
      ∀ after outcome, Finishes (ExecutionMachine.step config limits)
        (fun state => state.stack.frames.size) allowed depth before after outcome →
        InstructionWP.resultPre post failure (after, outcome) :=
  (controlPre_shared config limits cfg allowed depth post failure before).trans
    (solve_iff _ _ _ _ _ _ _)

/-- The symbolic condition emitted for a compiled equation. At a continuing
successor both indexed and fallback routes refer to the same whole-scope
solution, so recursive edges share their continuation. -/
def equationPre [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (equation : BodyCFG.Equation) (before : State) : Prop :=
  if depth ≤ before.stack.frames.size then
    ∀ choice, allowed before choice →
      let next := controlPre config limits cfg allowed depth post failure
      equation.pre config limits cfg choice (fun _ => next) next (post .stopped) failure before
  else post .scopeExit before

/-- The equation selected by the live frame is an exact view of the whole
condition. The theorem keeps the actual successor after calls and unwinding. -/
theorem controlPre_at [DecidableEq K] (config : Config) (limits : Limits) (cfg : BodyCFG.Compiled)
    (allowed : State → C → Prop) (depth : Nat) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (equation : BodyCFG.Equation) (before : State)
    (selected : BodyCFG.selected before = some (equation.pc, equation.node)) :
    controlPre config limits cfg allowed depth post failure before ↔
      equationPre config limits cfg allowed depth post failure equation before := by
  rw [controlPre_unfold, equationPre]
  split
  · apply forall_congr'
    intro choice
    apply forall_congr'
    intro _
    rw [BodyCFG.tablePre_iff, BodyCFG.Equation.pre_iff _ _ _ _ _ _ _ _ _ _ selected]
    simp only [BodyCFG.route_shared]
  · rfl

/-- Generate the exact condition for a prepared body, including nested
executions that remain inside the original frame's scope. -/
def bodyPre [DecidableEq K] (config : Config) (limits : Limits) (source : Miri.MIR.Body)
    (allowed : State → C → Prop) (post : Exit → State → Prop) (failure : StepError → State → Prop)
    (before : State) : Prop :=
  entryMatches source before ∧
    controlPre config limits (BodyCFG.compile source) allowed before.stack.frames.size post failure before

/-- Named equation families can discharge a recursive VC while sharing their
hypotheses at joins. The fallback covers dynamic states outside the table. -/
theorem bodyPre_of_vcs [DecidableEq K] (config : Config) (limits : Limits) (source : Body)
    (allowed : State → C → Prop) (post : Exit → State → Prop)
    (failure : StepError → State → Prop) (before : State)
    (entry : entryMatches source before) (atPC : Location → State → Prop)
    (fallback : State → Prop)
    (initial : BodyCFG.route (BodyCFG.compile source) atPC fallback before)
    (exited : ∀ state, state.stack.frames.size < before.stack.frames.size →
      BodyCFG.route (BodyCFG.compile source) atPC fallback state → post .scopeExit state)
    (equations : (BodyCFG.compile source).equationVCs config limits allowed atPC fallback
      (post .stopped) failure)
    (residual : (BodyCFG.compile source).fallbackVCs config limits allowed atPC fallback
      (post .stopped) failure) :
    bodyPre config limits source allowed post failure before := by
  refine ⟨entry, controlPre_of_closed config limits (BodyCFG.compile source) allowed
    before.stack.frames.size post failure (BodyCFG.route (BodyCFG.compile source) atPC fallback)
    ?_ before initial⟩
  intro state ready
  split
  · intro choice permitted
    exact (BodyCFG.compile source).closed_of_vcs config limits allowed atPC fallback (post .stopped)
      failure equations residual state ready choice permitted
  next outside => exact exited state (Nat.lt_of_not_ge outside) ready

theorem bodyPre_mono [DecidableEq K] (config : Config) (limits : Limits) (source : Miri.MIR.Body)
    (allowed : State → C → Prop) {post post' : Exit → State → Prop}
    {failure failure' : StepError → State → Prop}
    (success : ∀ exit state, post exit state → post' exit state)
    (error : ∀ err state, failure err state → failure' err state)
    (before : State) (checked : bodyPre config limits source allowed post failure before) :
    bodyPre config limits source allowed post' failure' before :=
  ⟨checked.1, (controlPre_shared config limits (BodyCFG.compile source) allowed
    before.stack.frames.size post' failure' before).mpr
    (solve_mono (machineRule config limits (BodyCFG.compile source)) _
      allowed before.stack.frames.size success error before
      ((controlPre_shared config limits (BodyCFG.compile source) allowed
        before.stack.frames.size post failure before).mp checked.2))⟩

theorem bodyPre_iff [DecidableEq K] (config : Config) (limits : Limits) (source : Miri.MIR.Body)
    (allowed : State → C → Prop) (post : Exit → State → Prop) (failure : StepError → State → Prop)
    (before : State) :
    bodyPre config limits source allowed post failure before ↔
      entryMatches source before ∧
        ∀ after outcome, Finishes (ExecutionMachine.step config limits)
          (fun state => state.stack.frames.size) allowed before.stack.frames.size before after outcome →
          InstructionWP.resultPre post failure (after, outcome) :=
  and_congr_right fun _ => controlPre_iff _ _ _ _ _ _ _ _

/-- On an imported root, also check the compiler-local body identity. The
lexical MIR and identity must belong to the same prepared frame. -/
def entryMatchesLoaded (source : LoadedBody) (before : State) : Prop :=
  ∃ frame, before.stack.currentFrame? = some frame ∧ frame.bodyIdentity = source.identity ∧
    frame.body = source.body ∧ frame.location = .mir ⟨0, 0⟩

private def programRule [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) : Rule (ExecutionMachine.step config limits) where
  pre := BodyCFG.programTablePre config limits program
  exact := BodyCFG.programTablePre_iff config limits program

/-- Back references use the program-wide table, including after a call picks
a concrete callee or a return resumes the caller. -/
def catalogSharedPre [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (before : State) : Prop :=
  solve (programRule config limits program) (fun state => state.stack.frames.size)
    allowed depth post failure before

def catalogControlPre [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (before : State) : Prop :=
  eliminate (programRule config limits program) (fun state => state.stack.frames.size)
    allowed depth post failure (BodyCFG.programRank program) before

theorem catalogControlPre_shared [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (before : State) :
    catalogControlPre config limits program allowed depth post failure before ↔
      catalogSharedPre config limits program allowed depth post failure before :=
  eliminate_iff _ _ _ _ _ _ _ _

theorem catalogControlPre_reduce [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (before : State) :
    catalogControlPre config limits program allowed depth post failure before ↔
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          BodyCFG.programTablePre config limits program choice
            (fun more after => if more then
              if 0 < BodyCFG.programRank program after ∧
                  BodyCFG.programRank program after < BodyCFG.programRank program before then
                catalogControlPre config limits program allowed depth post failure after
              else catalogSharedPre config limits program allowed depth post failure after
            else post .stopped after) failure before
      else post .scopeExit before := by
  unfold catalogControlPre
  rw [eliminate]
  rfl

theorem catalogControlPre_unfold [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (before : State) :
    catalogControlPre config limits program allowed depth post failure before ↔
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          BodyCFG.programTablePre config limits program choice
            (fun more after => if more then
              catalogControlPre config limits program allowed depth post failure after
            else post .stopped after) failure before
      else post .scopeExit before := by
  simp only [catalogControlPre_shared]
  exact solve_unfold _ _ _ _ _ _ _

theorem catalogControlPre_of_closed [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (allowed : State → C → Prop) (depth : Nat)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (candidate : State → Prop)
    (closed : ∀ before, candidate before →
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          BodyCFG.programTablePre config limits program choice
            (fun more after => if more then candidate after else post .stopped after) failure before
      else post .scopeExit before)
    (before : State) (initial : candidate before) :
    catalogControlPre config limits program allowed depth post failure before :=
  (catalogControlPre_shared config limits program allowed depth post failure before).mpr
    (solve_of_closed (programRule config limits program) (fun state => state.stack.frames.size)
      allowed depth post failure candidate closed before initial)

/-- An imported body uses compiler-indexed tables for every known live frame.
Calls remain in scope. A return or unwind leaving the initial depth is a
scope exit with its actual caller continuation. A caught unwind that keeps
the frame in scope continues at the location selected by the interpreter. -/
def catalogBodyPre [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (source : LoadedBody) (allowed : State → C → Prop)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (before : State) : Prop :=
  entryMatchesLoaded source before ∧
    catalogControlPre config limits program allowed before.stack.frames.size post failure before

theorem catalogBodyPre_mono [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (source : LoadedBody) (allowed : State → C → Prop)
    {post post' : Exit → State → Prop} {failure failure' : StepError → State → Prop}
    (success : ∀ exit state, post exit state → post' exit state)
    (error : ∀ err state, failure err state → failure' err state)
    (before : State) (checked : catalogBodyPre config limits program source allowed post failure before) :
    catalogBodyPre config limits program source allowed post' failure' before :=
  ⟨checked.1, (catalogControlPre_shared config limits program allowed
    before.stack.frames.size post' failure' before).mpr
    (solve_mono (programRule config limits program) _ allowed before.stack.frames.size success error before
      ((catalogControlPre_shared config limits program allowed
        before.stack.frames.size post failure before).mp checked.2))⟩

theorem catalogBodyPre_iff [DecidableEq K] (config : Config) (limits : Limits)
    (program : BodyCFG.CompiledProgram) (source : LoadedBody) (allowed : State → C → Prop)
    (post : Exit → State → Prop) (failure : StepError → State → Prop) (before : State) :
    catalogBodyPre config limits program source allowed post failure before ↔
      entryMatchesLoaded source before ∧
        ∀ after outcome, Finishes (ExecutionMachine.step config limits)
          (fun state => state.stack.frames.size) allowed before.stack.frames.size before after outcome →
          InstructionWP.resultPre post failure (after, outcome) :=
  and_congr_right fun _ =>
    (catalogControlPre_shared config limits program allowed before.stack.frames.size post failure before).trans
      (solve_iff _ _ _ _ _ _ _)

end Machine
end Miri.Verification.WholeBodyWP

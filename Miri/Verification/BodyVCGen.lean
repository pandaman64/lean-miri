import Miri.Input.CallResolution
import Miri.Verification.ExactWP
import Miri.Verification.WholeBodyWP
import Std.Tactic.Do

/-! Whole-body verification conditions for an imported MIR body. -/
namespace Miri.Verification.BodyVCGen

open Miri.Interpreter Miri.MIR Std.WP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host

private def loadPreparedRoot (prepared : Miri.Input.CallResolution.Prepared) (root : Nat) :
    Except String (CallInstance × LoadedBody) := do
  let definition ← prepared.program.rootDefinitionId root
  let instanceKey ← Miri.Input.CompilerInstance.item prepared.program.input.instances definition #[]
  let body ← Miri.Input.CallResolution.loadedBodyOfInstance prepared instanceKey
  pure (instanceKey, body)

/-- Resolve a non-generic Rust root using the same canonical instance and
body ownership checks as ordinary call dispatch. -/
def loadRoot (input : Miri.Input.ExecutionInput) (root : Nat) : Except String LoadedBody := do
  let lowered ← Miri.Input.lowerProgram input.document
  let prepared ← Miri.Input.CallResolution.prepare lowered
  return (← loadPreparedRoot prepared root).2

/-- The root and bodies available to canonical call resolution. The
interpreter remains responsible for choosing the callee and preparing its
frame when it executes a call. -/
structure LoadedProgram where
  rootInstance : CallInstance
  root : LoadedBody
  bodies : Array LoadedBody

/-- Load the selected root and collect every canonical body that the
interpreter can load from the compiler's instance table. Calls whose bodies
are unavailable use the live interpreter rule. -/
def loadProgram (input : Miri.Input.ExecutionInput) (rootIndex : Nat) : Except String LoadedProgram := do
  let lowered ← Miri.Input.lowerProgram input.document
  let prepared ← Miri.Input.CallResolution.prepare lowered
  let (rootInstance, root) ← loadPreparedRoot prepared rootIndex
  let multiplicities : Std.HashMap CallInstance Nat := prepared.bodies.foldl (fun counts body =>
    counts.insert body.fnInstance (counts[body.fnInstance]?.getD 0 + 1)) {}
  let bodies := prepared.bodies.filterMap fun body =>
    -- Validate ownership through the same loader after checking uniqueness
    -- once for the entire table, avoiding a full rescan for each body.
    if multiplicities[body.fnInstance]? = some 1 then
      (Miri.Input.CallResolution.loadedBodyOfInstance
        { prepared with bodies := #[body] } body.fnInstance).toOption
    else none
  pure ⟨rootInstance, root, bodies⟩

/-- Prepare the imported root on an initialized machine using the production
root-call path. The caller supplies the typed immediate arguments and, for a
non-unit result, a destination allocated by the machine. -/
def prepareRoot (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (choice : C) (arguments : Array (RvalueImmTy Miri.Memory.Provenance))
    (destination : Option (MPlaceTy Miri.Memory.Provenance)) (span : SpanRef) :
    MachineHooks.M K U Unit :=
  let calls := ExecutionMachine.callHooks config limits
  let functions := ExecutionCalls.helpers config.helpers calls
  FunctionCalls.callThreadRootFunction functions choice program.rootInstance calls.rustAbi
    arguments destination span

attribute [spec] prepareRoot FunctionCalls.callThreadRootFunction FunctionCalls.callFunction

/-- Verify the body of the frame at entry, including execution of nested calls
until the callee's initial frame depth is left or the driver stops. -/
inductive Run (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (allowed : State → C → Prop) where
  | body

def run (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (allowed : State → C → Prop) : Run config limits body allowed := .body

/-- A compiled graph, its exact entry VC and the named instruction obligations
available when proving the VC with an invariant. -/
structure Conditions (state : Type) where
  graph : BodyCFG.Compiled
  pre : state → Prop
  equations : (Location → state → Prop) → (state → Prop) → Array Prop
  residual : (Location → state → Prop) → (state → Prop) → Prop

/-- Compile the body once. Both the entry VC and the optional instruction
obligations refer to the same graph. -/
def generate (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (allowed : State → C → Prop) (post : WholeBodyWP.Exit → State → Prop)
    (failure : StepError → State → Prop) : Conditions State :=
  let graph := BodyCFG.compile body
  { graph
    pre := fun before => WholeBodyWP.entryMatches body before ∧
      WholeBodyWP.controlPre config limits graph allowed before.stack.frames.size post failure before
    equations := fun atPC fallback =>
      graph.generatedVCs config limits allowed atPC fallback (post .stopped) failure
    residual := fun atPC fallback =>
      graph.fallbackVCs config limits allowed atPC fallback (post .stopped) failure }

theorem generatedPre_eq (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (allowed : State → C → Prop) (post : WholeBodyWP.Exit → State → Prop)
    (failure : StepError → State → Prop) :
    (generate config limits body allowed post failure).pre =
      WholeBodyWP.bodyPre config limits body allowed post failure := rfl

/-- Discharge the exact VC with facts at named locations and a predicate for
states outside the table. The compiler and runtime supply the successor
addresses, including the state actually entered by a call. -/
theorem proveGenerated {config : Config} {limits : ExecutionMachine.Limits}
    {body : Body} {allowed : State → C → Prop} {post : WholeBodyWP.Exit → State → Prop}
    {failure : StepError → State → Prop} {before : State}
    (atPC : Location → State → Prop) (fallback : State → Prop)
    (entered : WholeBodyWP.entryMatches body before)
    (initial : BodyCFG.route (generate config limits body allowed post failure).graph atPC fallback before)
    (exited : ∀ state, state.stack.frames.size < before.stack.frames.size →
      BodyCFG.route (generate config limits body allowed post failure).graph atPC fallback state →
      post .scopeExit state)
    (equations : ∀ vc ∈ (generate config limits body allowed post failure).equations atPC fallback, vc)
    (residual : (generate config limits body allowed post failure).residual atPC fallback) :
    (generate config limits body allowed post failure).pre before := by
  rw [generatedPre_eq]
  exact WholeBodyWP.bodyPre_of_vcs config limits body allowed post failure before entered atPC
    fallback initial exited ((BodyCFG.Compiled.equationVCs_iff _ _ _ _ _ _ _ _).mpr equations) residual

instance (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (allowed : State → C → Prop) :
    WP (Run config limits body allowed) WholeBodyWP.Exit
      (State → Prop) (StepError → State → Prop) where
  wpTrans _ := ⟨WholeBodyWP.bodyPre config limits body allowed⟩
  wp_trans_monotone := by
    intro _ post post' failure failure' errorMono postMono before checked
    exact WholeBodyWP.bodyPre_mono config limits body allowed postMono errorMono before checked

/-- The generated goal has one compiled graph for the supplied body. The
continuations take the actual exit or the actual failing state. -/
@[spec] theorem spec_run (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop) :
    Triple (run config limits body allowed)
      (generate config limits body allowed post failure).pre post failure :=
  Triple.iff.mpr fun _ checked => checked

/-- Match the runtime diagnostic classification. This explicitly permits
errors outside the runtime's UB class. -/
abbrev noUB (error : StepError) (_ : State) : Prop :=
  RunLoop.reportsUB error = false

/-- Check diagnostic UB exclusion over finite observations. A cutoff or
unsupported operation is an allowed error outcome here. Use an explicit
triple to constrain successful exits or require error-free execution. -/
abbrev NoUB (config : Config) (limits : ExecutionMachine.Limits)
    (body : Body) (allowed : State → C → Prop) (entry : State → Prop) : Prop :=
  Triple (run config limits body allowed) entry (fun _ _ => True) (noUB (K := K) (U := U))

/-- Expose the entry guard and one layer of the generated shared transfer.
Use `vcgen` first. Each continuation keeps the same compiled body in scope,
so this tactic needs no loop fuel or per-block hypotheses. -/
macro "miri_body" : tactic =>
  `(tactic|
    first
    | rw [generatedPre_eq, WholeBodyWP.bodyPre, WholeBodyWP.controlPre_reduce]
    | rw [WholeBodyWP.bodyPre, WholeBodyWP.controlPre_reduce]
    | rw [WholeBodyWP.controlPre_reduce])

/-- Expose the exact transfer using the shared continuation on every edge. -/
macro "miri_body_shared" : tactic =>
  `(tactic|
    first
    | rw [generatedPre_eq, WholeBodyWP.bodyPre, WholeBodyWP.controlPre_unfold]
    | rw [WholeBodyWP.bodyPre, WholeBodyWP.controlPre_unfold]
    | rw [WholeBodyWP.controlPre_unfold])

/-- Reduce a generated goal to entry, exit, named equation, and residual
conditions using the given location and residual predicates. -/
macro "miri_body_with" atPC:term "," fallback:term : tactic =>
  `(tactic| refine proveGenerated $atPC $fallback ?_ ?_ ?_ ?_ ?_)

/-- The imported-program counterpart of `Run`. Known callees share the same
program-wide equation table, keyed by their loaded body identities. -/
inductive RunProgram (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (allowed : State → C → Prop) where
  | root

def runProgram (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (allowed : State → C → Prop) : RunProgram config limits program allowed :=
  .root

/-- The entry VC and generated equation tables of known imported bodies. -/
structure ProgramConditions (state : Type) where
  graph : BodyCFG.CompiledProgram
  pre : state → Prop
  equations : (BodyCFG.ProgramLocation → state → Prop) → (state → Prop) →
    BodyIdentity → Option (Array Prop)
  residual : (BodyCFG.ProgramLocation → state → Prop) → (state → Prop) → Prop

/-- The condition at a named instruction applies when the live driver selects
that exact body and location. Its continuation uses the driver's actual new
state, including the active callee on a successful call. -/
def programEquation (config : Config) (limits : ExecutionMachine.Limits)
    (graph : BodyCFG.CompiledProgram) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop)
    (atPC : BodyCFG.ProgramLocation → State → Prop) (fallback : State → Prop)
    (identity : BodyIdentity) (equation : BodyCFG.Equation) : Prop :=
  let location : BodyCFG.ProgramLocation := ⟨identity, equation.pc⟩
  ∀ before, graph.equationFor before = some (location, equation) → atPC location before →
    ∀ choice, allowed before choice →
      BodyCFG.nodePre config limits choice (fun more after =>
        if more then BodyCFG.programRoute graph atPC fallback after else post .stopped after)
        failure before equation.node

def generateProgram (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop) :
    ProgramConditions State :=
  let graph := BodyCFG.compileProgram program.bodies
  let continued := fun atPC fallback more after =>
    if more then BodyCFG.programRoute graph atPC fallback after else post .stopped after
  { graph
    pre := WholeBodyWP.catalogBodyPre config limits graph program.root allowed post failure
    equations := fun atPC fallback identity => (graph.lookup identity).map fun cfg =>
      cfg.equations.map (programEquation config limits graph allowed post failure atPC fallback identity)
    residual := fun atPC fallback =>
      ∀ before, graph.equationFor before = none → fallback before →
        ∀ choice, allowed before choice →
          BodyCFG.programTablePre config limits graph choice (continued atPC fallback) failure before }

theorem generatedProgramPre_eq (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop) :
    (generateProgram config limits program allowed post failure).pre =
      WholeBodyWP.catalogBodyPre config limits
        (BodyCFG.compileProgram program.bodies) program.root allowed post failure := rfl

/-- Pull a generated body VC back through actual root preparation. A startup
failure is checked immediately, with the state left by the failing effect. -/
def preparedProgramPre (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (choice : C) (arguments : Array (RvalueImmTy Miri.Memory.Provenance))
    (destination : Option (MPlaceTy Miri.Memory.Provenance)) (span : SpanRef)
    (allowed : State → C → Prop) (post : WholeBodyWP.Exit → State → Prop)
    (failure : StepError → State → Prop) : State → Prop :=
  wp (prepareRoot config limits program choice arguments destination span)
    (fun _ => (generateProgram config limits program allowed post failure).pre) failure

private theorem programEquation_selected (config : Config) (limits : ExecutionMachine.Limits)
    (graph : BodyCFG.CompiledProgram) (choice : C) (post : Bool → State → Prop)
    (failure : StepError → State → Prop) (before : State)
    {identity : BodyIdentity} {cfg : BodyCFG.Compiled} {equation : BodyCFG.Equation}
    (active : graph.graphFor before = some (identity, cfg))
    (selected : cfg.equationFor before = some equation) :
    BodyCFG.programTablePre config limits graph choice post failure before ↔
      BodyCFG.nodePre config limits choice post failure before equation.node := by
  simp only [BodyCFG.programTablePre, active, BodyCFG.tablePre, selected, BodyCFG.Equation.pre]
  have same : (fun more after =>
      if more then BodyCFG.route cfg (fun _ => post true) (post true) after
      else post false after) = post := by
    funext more after
    cases more
    · rfl
    · exact propext (BodyCFG.route_shared cfg (post true) after)
  rw [same]

/-- Compose inspection and proof of the compiler-indexed equation tables,
including the residual canonical statement, terminator and unwind cases. -/
theorem proveGeneratedProgram {config : Config} {limits : ExecutionMachine.Limits}
    {program : LoadedProgram} {allowed : State → C → Prop}
    {post : WholeBodyWP.Exit → State → Prop} {failure : StepError → State → Prop} {before : State}
    (atPC : BodyCFG.ProgramLocation → State → Prop) (fallback : State → Prop)
    (entered : WholeBodyWP.entryMatchesLoaded program.root before)
    (initial : BodyCFG.programRoute (generateProgram config limits program allowed post failure).graph
      atPC fallback before)
    (exited : ∀ state, state.stack.frames.size < before.stack.frames.size →
      BodyCFG.programRoute (generateProgram config limits program allowed post failure).graph
        atPC fallback state → post .scopeExit state)
    (equations : ∀ identity vcs,
      (generateProgram config limits program allowed post failure).equations atPC fallback identity = some vcs →
      ∀ vc ∈ vcs, vc)
    (residual : (generateProgram config limits program allowed post failure).residual atPC fallback) :
    (generateProgram config limits program allowed post failure).pre before := by
  let graph := (generateProgram config limits program allowed post failure).graph
  refine ⟨entered, WholeBodyWP.catalogControlPre_of_closed config limits graph allowed
    before.stack.frames.size post failure (BodyCFG.programRoute graph atPC fallback)
    ?_ before initial⟩
  intro state ready
  split
  next inside =>
    intro choice permitted
    cases found : graph.equationFor state with
    | none =>
      exact residual state found (by simpa only [BodyCFG.programRoute, found] using ready) choice permitted
    | some hit =>
      cases active : graph.graphFor state with
      | none => simp [BodyCFG.CompiledProgram.equationFor, active, bind, Bind.bind] at found
      | some pair =>
        obtain ⟨identity, cfg⟩ := pair
        cases selected : cfg.equationFor state with
        | none => simp [BodyCFG.CompiledProgram.equationFor, active, selected, bind, Bind.bind] at found
        | some equation =>
          have same : (⟨identity, equation.pc⟩, equation) = hit := by
            simpa [BodyCFG.CompiledProgram.equationFor, active, selected, bind, Bind.bind] using found
          subst hit
          have loaded : graph.lookup identity = some cfg := by
            unfold BodyCFG.CompiledProgram.graphFor at active
            cases current : state.stack.currentFrame? with
            | none => simp [current, bind, Bind.bind] at active
            | some frame =>
              cases lookup : graph.lookup frame.bodyIdentity with
              | none => simp [current, lookup, bind, Bind.bind] at active
              | some actual =>
                simp [current, lookup, bind, Bind.bind] at active
                rcases active with ⟨rfl, rfl⟩
                exact lookup
          let make := programEquation config limits graph allowed post failure atPC fallback identity
          have emitted : (generateProgram config limits program allowed post failure).equations
              atPC fallback identity = some (cfg.equations.map make) := by
            change (graph.lookup identity).map (fun cfg => cfg.equations.map make) = _
            rw [loaded]
            rfl
          have checked : make equation := equations identity _ emitted _
            (Array.mem_map.mpr ⟨equation, (cfg.equationFor_spec state selected).1, rfl⟩)
          apply (programEquation_selected config limits graph choice _ failure state active selected).mpr
          exact checked state found (by simpa only [BodyCFG.programRoute, found] using ready) choice permitted
  next outside => exact exited state (Nat.lt_of_not_ge outside) ready

instance (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (allowed : State → C → Prop) :
    WP (RunProgram config limits program allowed) WholeBodyWP.Exit
      (State → Prop) (StepError → State → Prop) where
  wpTrans _ := ⟨fun post failure => (generateProgram config limits program allowed post failure).pre⟩
  wp_trans_monotone := by
    intro _ post post' failure failure' errorMono postMono before checked
    exact WholeBodyWP.catalogBodyPre_mono config limits (BodyCFG.compileProgram program.bodies)
      program.root allowed postMono errorMono before checked

@[spec] theorem spec_runProgram (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop) :
    Triple (runProgram config limits program allowed)
      (generateProgram config limits program allowed post failure).pre post failure :=
  Triple.iff.mpr fun _ checked => checked

abbrev ProgramNoUB (config : Config) (limits : ExecutionMachine.Limits)
    (program : LoadedProgram) (allowed : State → C → Prop) (entry : State → Prop) : Prop :=
  Triple (runProgram config limits program allowed) entry (fun _ _ => True) (noUB (K := K) (U := U))

/-- Expose a layer of the generated program VC, retaining rank-decreasing
substitution and the shared continuations on other edges. -/
macro "miri_program" : tactic =>
  `(tactic|
    first
    | rw [generatedProgramPre_eq, WholeBodyWP.catalogBodyPre, WholeBodyWP.catalogControlPre_reduce]
    | rw [WholeBodyWP.catalogControlPre_reduce])

/-- Turn an imported program's generated VC into reusable obligations for
the root and each known callee. -/
macro "miri_program_with" atPC:term "," fallback:term : tactic =>
  `(tactic| refine proveGeneratedProgram $atPC $fallback ?_ ?_ ?_ ?_ ?_)

end Miri.Verification.BodyVCGen

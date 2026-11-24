import Miri.Frontend.ImportMIR
import Miri.Verification.BodyVCGen

namespace BodyVCGenExample

open Miri.Frontend Miri.Interpreter Miri.MIR Miri.Verification Std.WP

set_option maxHeartbeats 10000000
set_option maxRecDepth 65536
set_option experimental.vcgen true

import_mir "examples/body_vcgen/input.json" as input

private def loaded := (BodyVCGen.loadProgram input 0).toOption

private theorem loadedSome : loaded.isSome = true := by cbv

def program : BodyVCGen.LoadedProgram := checkedSome loaded loadedSome

def body : Body := program.root.body

def graph : BodyCFG.Compiled := BodyCFG.compile body

def programGraph : BodyCFG.CompiledProgram := BodyCFG.compileProgram program.bodies

private def targets (pc : Location) : Option (Array Location) :=
  (graph.equationAt pc).map (·.targets)

private def op (pc : Location) : String :=
  match (graph.equationAt pc).map (·.node) with
  | some (BodyCFG.Node.terminator ⟨_, .SwitchInt ..⟩) => "switch"
  | some (BodyCFG.Node.terminator ⟨_, .Call ..⟩) => "call"
  | some (BodyCFG.Node.terminator ⟨_, .Goto ..⟩) => "goto"
  | some (BodyCFG.Node.terminator ⟨_, .Return⟩) => "return"
  | _ => "other"

/-- The branch, loop back edge, direct call, and shared return join come from
the production-loaded body. Call target 3 is the return continuation. -/
theorem importedGraph :
    (op ⟨0, 3⟩, targets ⟨0, 3⟩) = ("switch", some #[⟨5, 0⟩, ⟨1, 0⟩]) ∧
    (op ⟨1, 6⟩, targets ⟨1, 6⟩) = ("switch", some #[⟨4, 0⟩, ⟨2, 0⟩]) ∧
    (op ⟨2, 5⟩, targets ⟨2, 5⟩) = ("call", some #[⟨3, 0⟩]) ∧
    (op ⟨3, 5⟩, targets ⟨3, 5⟩) = ("goto", some #[⟨1, 0⟩]) ∧
    (op ⟨4, 6⟩, targets ⟨4, 6⟩) = ("goto", some #[⟨6, 0⟩]) ∧
    (op ⟨5, 1⟩, targets ⟨5, 1⟩) = ("goto", some #[⟨6, 0⟩]) ∧
    (op ⟨6, 3⟩, targets ⟨6, 3⟩) = ("return", some #[]) := by
  cbv

/-- The direct callee has its own graph, even though its entry PC is also
`bb0.0`. The canonical body identity prevents the two entries from merging. -/
theorem importedCallee :
    program.root.identity.index = 0 ∧
    ((programGraph.lookup (.ofCanonicalIndex 1)).map (·.blocks.size)) = some 2 := by
  cbv

theorem calleeEquationCount :
    ((programGraph.lookup (.ofCanonicalIndex 1)).map (·.equations.size)) = some 5 := by
  cbv

section Proof

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U

/-- Substitute any success and error postconditions. The displayed continuation
is shared by all control-flow edges, and the call uses the actual successor state. -/
theorem generated
    (config : ExecutionMachine.Config K U C O X H) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (entry : State)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop)
    (entered : WholeBodyWP.entryMatches body entry)
    (one : ∀ choice, allowed entry choice →
      BodyCFG.tablePre config limits graph choice
        (fun more after => if more then
          WholeBodyWP.controlPre config limits graph allowed entry.stack.frames.size post failure after
          else post .stopped after) failure entry) :
    Triple (BodyVCGen.run config limits body allowed) (· = entry) post failure := by
  vcgen
  rename_i state same
  subst state
  miri_body_shared
  exact ⟨entered, by simpa only [graph, Nat.le_refl, ↓reduceIte] using one⟩

/-- An optional proof using predicates at the locations means proving the
generated equation family and the condition for states outside this table. -/
theorem fromEquations
    (config : ExecutionMachine.Config K U C O X H) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (entry : State)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop)
    (atPC : Location → State → Prop) (fallback : State → Prop)
    (entered : WholeBodyWP.entryMatches body entry)
    (initial : BodyCFG.route graph atPC fallback entry)
    (returned : ∀ state, state.stack.frames.size < entry.stack.frames.size →
      BodyCFG.route graph atPC fallback state → post .scopeExit state)
    (equations : ∀ vc ∈ (BodyVCGen.generate config limits body allowed post failure).equations
      atPC fallback, vc)
    (residual : (BodyVCGen.generate config limits body allowed post failure).residual atPC fallback) :
    Triple (BodyVCGen.run config limits body allowed) (· = entry) post failure := by
  vcgen
  rename_i state same
  subst state
  miri_body_with atPC, fallback
  · exact entered
  · exact initial
  · exact returned
  · exact equations
  · exact residual

/-- A program-level VC selects the graph for the actual frame at every step.
The same success and error continuations apply across the imported call. -/
theorem generatedProgram
    (config : ExecutionMachine.Config K U C O X H) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (entry : State)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop)
    (entered : WholeBodyWP.entryMatchesLoaded program.root entry)
    (one : ∀ choice, allowed entry choice →
      BodyCFG.programTablePre config limits programGraph choice
        (fun more after => if more then
          if 0 < BodyCFG.programRank programGraph after ∧
              BodyCFG.programRank programGraph after < BodyCFG.programRank programGraph entry then
            WholeBodyWP.catalogControlPre config limits programGraph allowed
              entry.stack.frames.size post failure after
          else WholeBodyWP.catalogSharedPre config limits programGraph allowed
            entry.stack.frames.size post failure after
        else post .stopped after) failure entry) :
    Triple (BodyVCGen.runProgram config limits program allowed) (· = entry) post failure := by
  vcgen
  rename_i state same
  subst state
  miri_program
  refine ⟨entered, ?_⟩
  simp only [Nat.le_refl, ↓reduceIte]
  intro choice permitted
  exact one choice permitted

/-- Discharge the generated program VC with local conditions for known
bodies, including the direct callee, and a condition for other states. -/
theorem fromProgramEquations
    (config : ExecutionMachine.Config K U C O X H) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (entry : State)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop)
    (atPC : BodyCFG.ProgramLocation → State → Prop) (fallback : State → Prop)
    (entered : WholeBodyWP.entryMatchesLoaded program.root entry)
    (initial : BodyCFG.programRoute programGraph atPC fallback entry)
    (returned : ∀ state, state.stack.frames.size < entry.stack.frames.size →
      BodyCFG.programRoute programGraph atPC fallback state → post .scopeExit state)
    (equations : ∀ identity vcs,
      (BodyVCGen.generateProgram config limits program allowed post failure).equations
        atPC fallback identity = some vcs → ∀ vc ∈ vcs, vc)
    (residual : (BodyVCGen.generateProgram config limits program allowed post failure).residual atPC fallback) :
    Triple (BodyVCGen.runProgram config limits program allowed) (· = entry) post failure := by
  vcgen
  rename_i state same
  subst state
  miri_program_with atPC, fallback
  · exact entered
  · exact initial
  · exact returned
  · exact equations
  · exact residual

/-- The generated callee obligations retain the requested postconditions.
There is one obligation per compiled instruction, including its terminator. -/
theorem generatedCalleeEquationCount
    (config : ExecutionMachine.Config K U C O X H) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : StepError → State → Prop)
    (atPC : BodyCFG.ProgramLocation → State → Prop) (fallback : State → Prop) :
    (((BodyVCGen.generateProgram config limits program allowed post failure).equations
      atPC fallback (.ofCanonicalIndex 1)).map Array.size) = some 5 := by
  simp only [BodyVCGen.generateProgram, Option.map_map]
  rw [← calleeEquationCount]
  apply congrArg (fun f => (programGraph.lookup (.ofCanonicalIndex 1)).map f)
  funext cfg
  apply Array.size_map

end Proof

#print axioms importedGraph
#print axioms importedCallee
#print axioms generatedProgram
#print axioms fromProgramEquations
#print axioms generatedCalleeEquationCount

end BodyVCGenExample

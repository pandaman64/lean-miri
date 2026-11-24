import Miri.Verification.CanonicalStepWP

/-! Compile MIR locations to named equations. Edges are locations rather than
inlined continuations, so a join shares one equation and a loop has a finite
representation. Runtime routing always follows the state left by the driver. -/
namespace Miri.Verification.BodyCFG

open Miri.MIR Miri.Interpreter

/-- The payload of one equation. Preserve terminator source information because
the interpreter can consult it during call and panic handling. -/
inductive Node where
  | statement (kind : StatementKind)
  | terminator (term : Terminator)
  deriving Repr, DecidableEq

structure Block where
  statements : Array StatementKind
  terminator : Terminator
  targets : Array Location := #[]
  deriving Repr

structure Compiled where
  blocks : Array Block
  /-- Reverse ranks of strongly connected components. -/
  blockRanks : Array Nat := #[]
  /-- Width reserved for the statement offsets of each component. -/
  rankWidth : Nat := 1
  deriving Repr

private def cleanupTarget : UnwindAction → Array BasicBlockId
  | .Cleanup target => #[target]
  | _ => #[]

/-- MIR branch labels. A dynamic call, return, unwind, or machine effect can
reach additional destinations. The equation checker uses the actual successor
rather than imposing these syntactic labels as a state invariant. -/
def terminatorTargets : TerminatorKind → Array BasicBlockId
  | .Goto target _ => #[target]
  | .SwitchInt _ targets =>
    (targets.cases.map fun | .Case _ target => target).push targets.otherwise
  | .Drop _ target unwind _ asyncDrop => #[target] ++ cleanupTarget unwind ++ asyncDrop.toArray
  | .Call _ _ _ target unwind .. => target.toArray ++ cleanupTarget unwind
  | .Assert _ _ _ target unwind => #[target] ++ cleanupTarget unwind
  | .Yield _ resume _ drop => #[resume] ++ drop.toArray
  | .FalseEdge real imaginary => #[real, imaginary]
  | .FalseUnwind real unwind => #[real] ++ cleanupTarget unwind
  | .InlineAsm asm => asm.targets ++ cleanupTarget asm.unwind
  | .Return | .UnwindResume | .UnwindTerminate _ | .Unreachable
  | .TailCall .. | .CoroutineDrop => #[]

private def finishOrder (edges : Array (Array BasicBlockId)) : Array BasicBlockId := Id.run do
  let budget := edges.foldl (fun n targets => n + targets.size) (2 * edges.size + 1)
  let mut seen := Array.replicate edges.size false
  let mut finished := #[]
  for root in [:edges.size] do
    if seen[root]? == some false then
      let mut pending := #[(root, false)]
      for _ in [:budget] do
        let some (node, closing) := pending.back? | break
        pending := pending.pop
        if closing then
          finished := finished.push node
        else if seen[node]? == some false then
          seen := seen.setIfInBounds node true
          pending := pending.push (node, true)
          for target in (edges[node]?.getD #[]) do
            if seen[target]? == some false then pending := pending.push (target, false)
  return finished

/-- Kosaraju's two iterative passes. Entries in the same component share a
rank. A strict edge in the component graph points from a higher rank to a
lower one. The proof backend checks this ordering at every actual edge
before it substitutes a successor formula. -/
private def componentRanks (edges : Array (Array BasicBlockId)) : Array Nat := Id.run do
  let order := finishOrder edges
  let mut reverse := Array.replicate edges.size #[]
  for source in [:edges.size] do
    for target in (edges[source]?.getD #[]) do
      if let some predecessors := reverse[target]? then
        reverse := reverse.setIfInBounds target (predecessors.push source)
  let mut ranks := Array.replicate edges.size 0
  let mut rank := edges.size
  for root in order.reverse do
    if ranks[root]? == some 0 then
      let mut pending := #[root]
      ranks := ranks.setIfInBounds root rank
      for _ in [:edges.size] do
        let some node := pending.back? | break
        pending := pending.pop
        for predecessor in (reverse[node]?.getD #[]) do
          if ranks[predecessor]? == some 0 then
            ranks := ranks.setIfInBounds predecessor rank
            pending := pending.push predecessor
      rank := rank - 1
  return ranks

def compile (body : Body) : Compiled :=
  let blocks := body.basicBlocks.map fun block => ({
    statements := block.statements.map Statement.kind
    terminator := block.terminator
    targets := (terminatorTargets block.terminator.kind).map fun target => ⟨target, 0⟩ } : Block)
  let edges := blocks.map fun block =>
    (block.targets.map (·.block)).filter (· < blocks.size)
  let rankWidth := blocks.foldl (fun width block => max width (block.statements.size + 1)) 1
  ⟨blocks, componentRanks edges, rankWidth⟩

/-- Priority for backward substitution. Later statements decrease the rank
within a block. A jump inside a component may require the recursive rule. -/
def Compiled.rankAt (cfg : Compiled) (pc : Location) : Nat :=
  let blockRank := cfg.blockRanks[pc.block]?.getD 0
  let suffix := (cfg.blocks[pc.block]?.map (·.statements.size)).getD 0 - pc.statementIndex
  blockRank * cfg.rankWidth + suffix

/-- Match the driver's terminator selection even when a statement index is
beyond the end of its block. Every such index uses the shared terminator. -/
def Compiled.lookup (cfg : Compiled) (pc : Location) : Option Node := do
  let block ← cfg.blocks[pc.block]?
  return match block.statements[pc.statementIndex]? with
    | some kind => .statement kind
    | none => .terminator block.terminator

theorem lookup_compile (body : Body) (pc : Location) :
    (compile body).lookup pc =
      (body.basicBlocks[pc.block]?).map fun block =>
        match block.statements[pc.statementIndex]? with
        | some stmt => .statement stmt.kind
        | none => .terminator block.terminator := by
  unfold Compiled.lookup compile
  simp only [Array.getElem?_map]
  cases body.basicBlocks[pc.block]? with
  | none => rfl
  | some block =>
    simp only [Option.map_some, bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp only [Array.getElem?_map]
    cases block.statements[pc.statementIndex]? <;> rfl

structure Equation where
  pc : Location
  node : Node
  targets : Array Location
  deriving Repr

private def terminatorEquation (id : BasicBlockId) (block : Block) : Equation :=
  ⟨⟨id, block.statements.size⟩, .terminator block.terminator, block.targets⟩

private def statementEquation (id : BasicBlockId) (index : Nat) (kind : StatementKind) : Equation :=
  let pc : Location := ⟨id, index⟩
  ⟨pc, .statement kind, #[pc.successorWithinBlock]⟩

private def blockEquations (id : BasicBlockId) (block : Block) : Array Equation :=
  (block.statements.mapIdx (statementEquation id)).push (terminatorEquation id block)

/-- Materialize the finite equation table. Every statement has one nominal
fallthrough edge. The terminator occupies the last location of its block. -/
def Compiled.equations (cfg : Compiled) : Array Equation :=
  (cfg.blocks.mapIdx blockEquations).flatten

/-- Index the nominal equations without rebuilding the flat equation table.
A noncanonical statement index is outside the table even though the live
driver still routes that index to the block's terminator. -/
def Compiled.equationAt (cfg : Compiled) (pc : Location) : Option Equation := do
  let block ← cfg.blocks[pc.block]?
  if pc.statementIndex = block.statements.size then
    some (terminatorEquation pc.block block)
  else
    (block.statements[pc.statementIndex]?).map (statementEquation pc.block pc.statementIndex)

private theorem equationAt_eq (cfg : Compiled) (pc : Location) :
    cfg.equationAt pc =
      (cfg.blocks[pc.block]?).bind fun block => (blockEquations pc.block block)[pc.statementIndex]? := by
  unfold Compiled.equationAt
  cases cfg.blocks[pc.block]? with
  | none => rfl
  | some block =>
    simp [blockEquations, Array.getElem?_push, Array.getElem?_mapIdx]

theorem Compiled.equationAt_mem (cfg : Compiled) (pc : Location) {equation : Equation}
    (found : cfg.equationAt pc = some equation) : equation ∈ cfg.equations := by
  rw [equationAt_eq] at found
  cases blockAt : cfg.blocks[pc.block]? with
  | none => simp [blockAt] at found
  | some block =>
    simp only [blockAt, Option.bind_some] at found
    apply Array.mem_flatten_of_mem _ (Array.mem_of_getElem? found)
    exact Array.mem_of_getElem? (i := pc.block) (by simp [Array.getElem?_mapIdx, blockAt])

theorem Compiled.equationAt_pc (cfg : Compiled) (pc : Location) {equation : Equation}
    (found : cfg.equationAt pc = some equation) : equation.pc = pc := by
  obtain ⟨id, index⟩ := pc
  unfold Compiled.equationAt at found
  cases blockAt : cfg.blocks[id]? with
  | none => simp [blockAt, bind, Bind.bind, Option.bind] at found
  | some block =>
    simp only [blockAt, bind, Bind.bind, Option.bind] at found
    split at found
    · rename_i atEnd
      cases found
      simp [terminatorEquation, atEnd]
    · cases slot : block.statements[index]? with
      | none => simp [slot] at found
      | some kind =>
        simp only [slot, Option.map_some, Option.some.injEq] at found
        cases found
        rfl

/-- Equation count is linear in the MIR payload. A block with no statements
has exactly one equation, and shared labels and back edges add none. -/
theorem Compiled.equations_size (cfg : Compiled) :
    cfg.equations.size = (cfg.blocks.map fun block => block.statements.size + 1).sum := by
  rw [Compiled.equations, Array.size_flatten]
  congr 1
  apply Array.ext
  · simp
  · intro index left right
    simp [blockEquations]

/-- All available compiled MIR bodies, indexed by the loader's canonical
identity. A program counter is meaningful only within its body. -/
structure CompiledProgram where
  graphs : Std.HashMap Nat Compiled

def compileProgram (bodies : Array LoadedBody) : CompiledProgram :=
  ⟨bodies.foldl (fun graphs source => graphs.insert source.identity.index (compile source.body)) {}⟩

def CompiledProgram.lookup (program : CompiledProgram) (identity : BodyIdentity) : Option Compiled :=
  program.graphs[identity.index]?

/-- A stable key for any generated equation within a compiled program. -/
structure ProgramLocation where
  body : BodyIdentity
  pc : Location
  deriving DecidableEq, Repr

section Execution

variable {K U C O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U
local notation "Success" => Bool → State → Prop
local notation "Errors" => StepError → State → Prop

def nodePre (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (post : Success) (failure : Errors) (before : State) : Node → Prop
  | .statement kind => CanonicalStepWP.statementPre config limits choice kind post failure before
  | .terminator term => CanonicalStepWP.terminatorPre config limits choice term post failure before

/-- Observe a MIR instruction before dispatch without examining future states. -/
def selected (state : State) : Option (Location × Node) := do
  let frame ← state.stack.currentFrame?
  let .mir pc := frame.location | none
  let block ← frame.body.basicBlocks[pc.block]?
  let node := match block.statements[pc.statementIndex]? with
    | some stmt => Node.statement stmt.kind
    | none => Node.terminator block.terminator
  return (pc, node)

/-- A matching named equation is selected before interpreting its formula. -/
def Compiled.equationFor (cfg : Compiled) (before : State) : Option Equation := do
  let (pc, node) ← selected before
  let eq ← cfg.equationAt pc
  if eq.node = node then some eq else none

omit [DecidableEq K] in
theorem Compiled.equationFor_spec (cfg : Compiled) (before : State) {equation : Equation}
    (found : cfg.equationFor before = some equation) :
    equation ∈ cfg.equations ∧ selected before = some (equation.pc, equation.node) := by
  unfold Compiled.equationFor at found
  cases here : selected before with
  | none => simp [here, bind, Bind.bind, Option.bind] at found
  | some selectedNode =>
    obtain ⟨pc, node⟩ := selectedNode
    cases nodeAt : cfg.equationAt pc with
    | none => simp [here, nodeAt, bind, Bind.bind, Option.bind] at found
    | some compiled =>
      by_cases same : compiled.node = node
      · simp [here, nodeAt, same, bind, Bind.bind, Option.bind] at found
        subst equation
        exact ⟨cfg.equationAt_mem pc nodeAt, by rw [cfg.equationAt_pc pc nodeAt, same]⟩
      · simp [here, nodeAt, same, bind, Bind.bind, Option.bind] at found

/-- Route a concrete successor to a shared equation when the compiled
instruction matches the live instruction at that successor. A missing or
mismatched equation uses the supplied fallback. -/
def route (cfg : Compiled) (atPC : Location → State → Prop)
    (fallback : State → Prop) (state : State) : Prop :=
  match cfg.equationFor state with
  | none => fallback state
  | some equation => atPC equation.pc state

/-- Emit the equation's one-step VC. Its continuation dispatches to another
location by reference, independently of how many edges enter that location. -/
def Equation.pre (equation : Equation) (config : Config) (limits : ExecutionMachine.Limits)
    (cfg : Compiled) (choice : C) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors) (before : State) : Prop :=
  nodePre config limits choice (fun more after =>
    if more then route cfg atPC fallback after else stopped after) failure before equation.node

/-- VC for one named MIR location. Symbolic effects precede the shared
successor predicate and retain their actual failed states. -/
def Equation.vc (equation : Equation) (cfg : Compiled) (config : Config)
    (limits : ExecutionMachine.Limits) (allowed : State → C → Prop)
    (atPC : Location → State → Prop) (fallback : State → Prop)
    (stopped : State → Prop) (failure : Errors) : Prop :=
  ∀ before, selected before = some (equation.pc, equation.node) → atPC equation.pc before →
    ∀ choice, allowed before choice →
      equation.pre config limits cfg choice atPC fallback stopped failure before

/-- The actual generated formulas in the order of the shared equation table. -/
def Compiled.generatedVCs (cfg : Compiled) (config : Config) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors) : Array Prop :=
  cfg.equations.map fun eq => eq.vc cfg config limits allowed atPC fallback stopped failure

theorem Compiled.generatedVCs_size (cfg : Compiled) (config : Config) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors) :
    (cfg.generatedVCs config limits allowed atPC fallback stopped failure).size = cfg.equations.size :=
  Array.size_map

/-- Preservation VCs for the emitted table. States outside the table use the
same fallback predicate supplied to every equation. -/
def Compiled.equationVCs (cfg : Compiled) (config : Config) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors) : Prop :=
  ∀ eq ∈ cfg.equations, eq.vc cfg config limits allowed atPC fallback stopped failure

theorem Compiled.equationVCs_iff (cfg : Compiled) (config : Config) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors) :
    cfg.equationVCs config limits allowed atPC fallback stopped failure ↔
      ∀ vc ∈ cfg.generatedVCs config limits allowed atPC fallback stopped failure, vc := by
  unfold Compiled.equationVCs Compiled.generatedVCs
  constructor
  · intro hold vc included
    obtain ⟨eq, present, rfl⟩ := Array.mem_map.mp included
    exact hold eq present
  · intro hold eq present
    exact hold _ (Array.mem_map.mpr ⟨eq, present, rfl⟩)

/-- The emitted equation applies whenever the live driver selects its
payload. This theorem also covers states whose frame was prepared by a call. -/
theorem Equation.pre_iff (equation : Equation) (config : Config) (limits : ExecutionMachine.Limits)
    (cfg : Compiled) (choice : C) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors) (before : State)
    (here : selected before = some (equation.pc, equation.node)) :
    equation.pre config limits cfg choice atPC fallback stopped failure before ↔
      InstructionWP.resultPre
        (fun more after => if more then route cfg atPC fallback after else stopped after) failure
        (Step.step (ExecutionMachine.stepHooks config limits) choice before) := by
  rw [← StepWP.driverChoicePre_iff, ← CanonicalStepWP.choicePre_iff]
  cases current : before.stack.currentFrame? with
  | none => simp [selected, current] at here
  | some frame =>
    cases location : frame.location with
    | unwinding span => simp [selected, current, location] at here
    | mir pc =>
      cases blockAt : frame.body.basicBlocks[pc.block]? with
      | none => simp [selected, current, location, blockAt] at here
      | some block =>
        cases slot : block.statements[pc.statementIndex]? with
        | none =>
          simp only [selected, current, location, blockAt, slot, bind, Bind.bind, Option.bind,
            pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at here
          simp [Equation.pre, CanonicalStepWP.choicePre, StepWP.driverChoicePreWith,
            current, location, blockAt, slot, ← here.2, nodePre]
        | some stmt =>
          simp only [selected, current, location, blockAt, slot, bind, Bind.bind, Option.bind,
            pure, Pure.pure, Option.some.injEq, Prod.mk.injEq] at here
          simp [Equation.pre, CanonicalStepWP.choicePre, StepWP.driverChoicePreWith,
            current, location, blockAt, slot, ← here.2, nodePre]

omit [DecidableEq K] in
theorem route_shared (cfg : Compiled) (again : State → Prop) (before : State) :
    route cfg (fun _ => again) again before ↔ again before := by
  cases found : cfg.equationFor before <;> simp [route, found]

/-- Invoke the emitted equation's formula when applicable. Outside the
compiled table the canonical rule handles the actual state, including callee
frames and unusual program counters. -/
def tablePre (config : Config) (limits : ExecutionMachine.Limits) (cfg : Compiled)
    (choice : C) (post : Success) (failure : Errors) (before : State) : Prop :=
  match cfg.equationFor before with
  | some eq => eq.pre config limits cfg choice (fun _ => post true) (post true)
      (post false) failure before
  | none => CanonicalStepWP.choicePre config limits choice post failure before

theorem tablePre_iff (config : Config) (limits : ExecutionMachine.Limits) (cfg : Compiled)
    (choice : C) (post : Success) (failure : Errors) (before : State) :
    tablePre config limits cfg choice post failure before ↔
      InstructionWP.resultPre post failure
        (Step.step (ExecutionMachine.stepHooks config limits) choice before) := by
  unfold tablePre
  cases found : cfg.equationFor before with
  | none =>
    exact (CanonicalStepWP.choicePre_iff _ _ _ _ _ _).trans
      (StepWP.driverChoicePre_iff _ _ _ _ _)
  | some eq =>
    change eq.pre _ _ _ _ _ _ _ _ _ ↔ _
    rw [eq.pre_iff _ _ _ _ _ _ _ _ _ (cfg.equationFor_spec before found).2]
    rcases Step.step (ExecutionMachine.stepHooks config limits) choice before with ⟨after, outcome⟩
    cases outcome with
    | error => rfl
    | ok more =>
      cases more
      · rfl
      · exact route_shared cfg (post true) after

/-- The residual obligation for states outside the equation table. -/
def Compiled.fallbackVCs (cfg : Compiled) (config : Config) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors) : Prop :=
  ∀ before, cfg.equationFor before = none → fallback before →
    ∀ choice, allowed before choice →
      CanonicalStepWP.choicePre config limits choice
        (fun more after => if more then route cfg atPC fallback after else stopped after)
        failure before

/-- Emitted equations and the residual proof give preservation for the
automatically routed predicate. -/
theorem Compiled.closed_of_vcs (cfg : Compiled) (config : Config) (limits : ExecutionMachine.Limits)
    (allowed : State → C → Prop) (atPC : Location → State → Prop)
    (fallback : State → Prop) (stopped : State → Prop) (failure : Errors)
    (equations : cfg.equationVCs config limits allowed atPC fallback stopped failure)
    (residual : cfg.fallbackVCs config limits allowed atPC fallback stopped failure)
    (before : State) (initial : route cfg atPC fallback before) (choice : C)
    (permitted : allowed before choice) :
    tablePre config limits cfg choice
      (fun more after => if more then route cfg atPC fallback after else stopped after)
      failure before := by
  cases found : cfg.equationFor before with
  | none =>
    have initial' : fallback before := by simpa only [route, found] using initial
    simpa only [tablePre, found] using residual before found initial' choice permitted
  | some eq =>
    have initial' : atPC eq.pc before := by simpa only [route, found] using initial
    obtain ⟨inTable, here⟩ := cfg.equationFor_spec before found
    have checked := equations eq inTable before here initial' choice permitted
    apply (tablePre_iff _ _ _ _ _ _ _).mpr
    exact (eq.pre_iff _ _ _ _ _ _ _ _ _ here).mp checked

/-- Select the known callee or root graph using the active frame's identity. -/
def CompiledProgram.graphFor (program : CompiledProgram) (before : State) :
    Option (BodyIdentity × Compiled) := do
  let frame ← before.stack.currentFrame?
  let cfg ← program.lookup frame.bodyIdentity
  return (frame.bodyIdentity, cfg)

/-- A catalogue match checks the real loaded payload within the chosen body
before entering the equation. A missing or mismatched entry uses the fallback. -/
def CompiledProgram.equationFor (program : CompiledProgram) (before : State) :
    Option (ProgramLocation × Equation) := do
  let (identity, cfg) ← program.graphFor before
  let equation ← cfg.equationFor before
  return (⟨identity, equation.pc⟩, equation)

def programRoute (program : CompiledProgram) (atPC : ProgramLocation → State → Prop)
    (fallback : State → Prop) (before : State) : Prop :=
  match program.equationFor before with
  | none => fallback before
  | some (location, _) => atPC location before

def programRank (program : CompiledProgram) (before : State) : Nat :=
  match program.graphFor before with
  | none => 0
  | some (_, cfg) =>
    match cfg.equationFor before with
    | none => 0
    | some equation => cfg.rankAt equation.pc + 1

/-- Check one driver choice using the equation table for the actual active
body, including a known callee pushed by the previous step. -/
def programTablePre (config : Config) (limits : ExecutionMachine.Limits) (program : CompiledProgram)
    (choice : C) (post : Success) (failure : Errors) (before : State) : Prop :=
  match program.graphFor before with
  | none => CanonicalStepWP.choicePre config limits choice post failure before
  | some (_, cfg) => tablePre config limits cfg choice post failure before

theorem programTablePre_iff (config : Config) (limits : ExecutionMachine.Limits) (program : CompiledProgram)
    (choice : C) (post : Success) (failure : Errors) (before : State) :
    programTablePre config limits program choice post failure before ↔
      InstructionWP.resultPre post failure
        (Step.step (ExecutionMachine.stepHooks config limits) choice before) := by
  unfold programTablePre
  cases detached : program.graphFor before with
  | none =>
    exact (CanonicalStepWP.choicePre_iff _ _ _ _ _ _).trans
      (StepWP.driverChoicePre_iff _ _ _ _ _)
  | some entry =>
    obtain ⟨_, cfg⟩ := entry
    exact tablePre_iff _ _ cfg _ _ _ _

end Execution
end Miri.Verification.BodyCFG

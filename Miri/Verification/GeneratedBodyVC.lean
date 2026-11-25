import Miri.Verification.BodyVCGen
import Miri.Verification.InitialWPAttr
import Miri.Verification.CalleeSummaryWP
import Miri.Verification.CopyInitialWP

namespace Miri.Verification.GeneratedBodyVC

open Miri.Interpreter Miri.MIR Std.WP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Limits" => ExecutionMachine.Limits
local notation "Success" => Bool → State → Prop
local notation "Failure" => StepError → State → Prop

/-- A specialized transfer with a proof against the fixed instruction rule.
The successor predicates are parameters, so transitions can share equations. -/
structure ReducedNode (config : Config) (limits : Limits) where
  node : BodyCFG.Node
  pre : C → Success → Failure → State → Prop
  exact : ∀ choice post failure before,
    pre choice post failure before ↔ BodyCFG.nodePre config limits choice post failure before node

abbrev Table (config : Config) (limits : Limits) :=
  Std.HashMap (Nat × Nat × Nat) (ReducedNode config limits)

private def rowPre (config : Config) (limits : Limits) (table : Table config limits)
    (identity : BodyIdentity) (eq : BodyCFG.Equation) (choice : C) (post : Success)
    (failure : Failure) (before : State) : Prop :=
  match table[(identity.index, eq.pc.block, eq.pc.statementIndex)]? with
  | some reduced =>
    if reduced.node = eq.node then reduced.pre choice post failure before
    else BodyCFG.nodePre config limits choice post failure before eq.node
  | none => BodyCFG.nodePre config limits choice post failure before eq.node

private theorem rowPre_eq (config : Config) (limits : Limits) (table : Table config limits)
    (identity : BodyIdentity) (eq : BodyCFG.Equation) (choice : C) (post : Success)
    (failure : Failure) (before : State) :
    rowPre config limits table identity eq choice post failure before =
      BodyCFG.nodePre config limits choice post failure before eq.node := by
  unfold rowPre
  split
  next reduced atIndex =>
    split
    next same => rw [propext (reduced.exact choice post failure before), same]
    · rfl
  · rfl

private def tablePre (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (choice : C) (post : Success) (failure : Failure)
    (before : State) : Prop :=
  match graph.graphFor before with
  | none => CanonicalStepWP.choicePre config limits choice post failure before
  | some (identity, cfg) =>
    match cfg.equationFor before with
    | none => CanonicalStepWP.choicePre config limits choice post failure before
    | some eq => rowPre config limits table identity eq choice post failure before

private theorem tablePre_iff (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (choice : C) (post : Success) (failure : Failure)
    (before : State) :
    tablePre config limits graph table choice post failure before ↔
      BodyCFG.programTablePre config limits graph choice post failure before := by
  have postEq : ∀ cfg : BodyCFG.Compiled,
      (fun more after => if more then BodyCFG.route cfg (fun _ => post true) (post true) after
        else post false after) = post := by
    intro cfg
    funext more after
    cases more
    · rfl
    · exact propext (BodyCFG.route_shared cfg (post true) after)
  cases active : graph.graphFor before with
  | none => simp only [tablePre, BodyCFG.programTablePre, active]
  | some found =>
    obtain ⟨identity, cfg⟩ := found
    cases selected : cfg.equationFor before with
    | none => simp only [tablePre, BodyCFG.programTablePre, BodyCFG.tablePre, active, selected]
    | some eq =>
      simp only [tablePre, BodyCFG.programTablePre, BodyCFG.tablePre, active, selected,
        BodyCFG.Equation.pre, postEq cfg, rowPre_eq]

/-- Dispatch using the actual active frame, MIR location and instruction.
Rows with missing or different MIR use the canonical exact precondition. -/
def rule (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) : WholeBodyWP.Rule (ExecutionMachine.step config limits) where
  pre := tablePre config limits graph table
  exact choice post failure before :=
    (tablePre_iff config limits graph table choice post failure before).trans
      (BodyCFG.programTablePre_iff config limits graph choice post failure before)

/-- A known row applies when it matches the active frame and MIR instruction. -/
theorem rule_pre_of_row (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (choice : C) (post : Success) (failure : Failure) (before : State)
    {identity : BodyIdentity} {cfg : BodyCFG.Compiled} {eq : BodyCFG.Equation}
    {reduced : ReducedNode config limits}
    (active : graph.graphFor before = some (identity, cfg))
    (selected : cfg.equationFor before = some eq)
    (found : table[(identity.index, eq.pc.block, eq.pc.statementIndex)]? = some reduced)
    (same : reduced.node = eq.node) :
    (rule config limits graph table).pre choice post failure before =
      reduced.pre choice post failure before := by
  simp only [rule, tablePre, active, selected, rowPre, found, same, ↓reduceIte]

/-- Joins and back edges reuse the same exact solution for the active state. -/
def sharedPre (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) : State → Prop :=
  WholeBodyWP.solve (rule config limits graph table) (fun state => state.stack.frames.size)
    allowed depth post failure

/-- The same control graph and rank with the reduced transfer table. -/
def controlPre (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) : State → Prop :=
  WholeBodyWP.eliminate (rule config limits graph table) (fun state => state.stack.frames.size)
    allowed depth post failure (BodyCFG.programRank graph)

theorem controlPre_reduce (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) (before : State) :
    controlPre config limits graph table allowed depth post failure before ↔
      if depth ≤ before.stack.frames.size then
        ∀ choice, allowed before choice →
          (rule config limits graph table).pre choice (fun more after => if more then
            if 0 < BodyCFG.programRank graph after ∧
                BodyCFG.programRank graph after < BodyCFG.programRank graph before then
              controlPre config limits graph table allowed depth post failure after
            else sharedPre config limits graph table allowed depth post failure after
          else post .stopped after) failure before
      else post .scopeExit before := by
  unfold controlPre
  rw [WholeBodyWP.eliminate]
  rfl

theorem controlPre_eq (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) :
    controlPre config limits graph table allowed depth post failure =
      WholeBodyWP.catalogControlPre config limits graph allowed depth post failure := by
  funext before
  apply propext
  simp only [controlPre, WholeBodyWP.catalogControlPre_shared, WholeBodyWP.catalogSharedPre,
    WholeBodyWP.eliminate_iff, WholeBodyWP.solve_iff]

/-- At a live call site, open the actual callee scope and resume the
generated continuation on the state left by return. -/
theorem sharedPre_iff_call (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) (before : State)
    (live : depth ≤ before.stack.frames.size) :
    sharedPre config limits graph table allowed depth post failure before ↔
      CalleeSummaryWP.callPre config limits graph allowed
        (CalleeSummaryWP.continueWith config limits graph allowed depth post failure)
        failure before := by
  have same := congrFun (controlPre_eq config limits graph table allowed depth post failure) before
  have shared := WholeBodyWP.eliminate_iff (rule config limits graph table)
    (fun state => state.stack.frames.size) allowed depth post failure (BodyCFG.programRank graph) before
  change controlPre config limits graph table allowed depth post failure before ↔
    sharedPre config limits graph table allowed depth post failure before at shared
  rw [← shared, same]
  exact (CalleeSummaryWP.callPre_continue_iff config limits graph allowed depth post failure before live).symm

/-- A statically selected instruction and its reduced transfer. The live
frame and instruction are checked before the transfer can be used. -/
structure WindowRow (config : Config) (limits : Limits) where
  location : BodyCFG.ProgramLocation
  reduced : ReducedNode config limits
  summarizeCall : Bool := false

/-- Compose a list of straight-line transfers. Each continuing transfer
passes its actual successor state to the next row. A selected call
summarizes the actual entered scope. Other edges leaving the window use
the shared whole-body equation. -/
def windowPre (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) :
    List (WindowRow config limits) → State → Prop
  | [], before => sharedPre config limits graph table allowed depth post failure before
  | row :: rest, before =>
    if depth ≤ before.stack.frames.size then
      match graph.equationFor before with
      | some (location, equation) =>
        if location = row.location ∧ equation.node = row.reduced.node then
          if row.summarizeCall then
            CalleeSummaryWP.callPre config limits graph allowed
              (CalleeSummaryWP.continueWith config limits graph allowed depth post failure)
              failure before
          else
            ∀ choice, allowed before choice →
              row.reduced.pre choice
                (fun more after => if more then windowPre config limits graph table allowed depth
                  post failure rest after else post .stopped after) failure before
        else sharedPre config limits graph table allowed depth post failure before
      | none => sharedPre config limits graph table allowed depth post failure before
    else post .scopeExit before

/-- Select the first transfer of a window when the live state is at its row. -/
theorem windowPre_at (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure)
    (row : WindowRow config limits) (rest : List (WindowRow config limits)) (before : State)
    {equation : BodyCFG.Equation} (inside : depth ≤ before.stack.frames.size)
    (selected : graph.equationFor before = some (row.location, equation))
    (same : equation.node = row.reduced.node) (ordinary : row.summarizeCall = false) :
    windowPre config limits graph table allowed depth post failure (row :: rest) before ↔
      ∀ choice, allowed before choice →
        row.reduced.pre choice (fun more after => if more then
          windowPre config limits graph table allowed depth post failure rest after
          else post .stopped after) failure before := by
  simp only [windowPre, inside, ↓reduceIte, selected, same, and_self, ordinary, Bool.false_eq_true]

/-- Select the scope summary when the live state selects the emitted call. -/
theorem windowPre_call (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure)
    (row : WindowRow config limits) (rest : List (WindowRow config limits)) (before : State)
    {equation : BodyCFG.Equation} (inside : depth ≤ before.stack.frames.size)
    (selected : graph.equationFor before = some (row.location, equation))
    (same : equation.node = row.reduced.node) (isCall : row.summarizeCall = true) :
    windowPre config limits graph table allowed depth post failure (row :: rest) before ↔
      CalleeSummaryWP.callPre config limits graph allowed
        (CalleeSummaryWP.continueWith config limits graph allowed depth post failure) failure before := by
  simp only [windowPre, inside, ↓reduceIte, selected, same, and_self, isCall]

theorem windowPre_iff (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure)
    (rows : List (WindowRow config limits)) (before : State) :
    windowPre config limits graph table allowed depth post failure rows before ↔
      sharedPre config limits graph table allowed depth post failure before := by
  induction rows generalizing before with
  | nil => rfl
  | cons row rest ih =>
    have sharedStep := WholeBodyWP.solve_unfold (rule config limits graph table)
      (fun state : State => state.stack.frames.size) allowed depth post failure before
    by_cases inside : depth ≤ before.stack.frames.size
    · cases active : graph.graphFor before with
      | none =>
        simp only [windowPre, inside, ↓reduceIte, BodyCFG.CompiledProgram.equationFor,
          active, bind, Bind.bind, Option.bind]
      | some found =>
        obtain ⟨identity, cfg⟩ := found
        cases selected : cfg.equationFor before with
        | none =>
          simp only [windowPre, inside, ↓reduceIte, BodyCFG.CompiledProgram.equationFor,
            active, selected, bind, Bind.bind, Option.bind]
        | some equation =>
          by_cases sameRow : (⟨identity, equation.pc⟩ : BodyCFG.ProgramLocation) = row.location ∧
              equation.node = row.reduced.node
          · cases isCall : row.summarizeCall
            · rw [show sharedPre config limits graph table allowed depth post failure before ↔ _ from sharedStep]
              simp only [windowPre, inside, ↓reduceIte, BodyCFG.CompiledProgram.equationFor, active,
                selected, bind, Bind.bind, Option.bind, pure, Pure.pure, sameRow, isCall, Bool.false_eq_true,
                WholeBodyWP.transfer, rule, tablePre, ih, rowPre_eq]
              exact forall_congr' fun choice => imp_congr_right fun _ => row.reduced.exact choice _ _ _
            · simpa only [windowPre, inside, ↓reduceIte, BodyCFG.CompiledProgram.equationFor, active,
                selected, bind, Bind.bind, Option.bind, pure, Pure.pure, sameRow, and_self, isCall] using
                (sharedPre_iff_call config limits graph table allowed depth post failure before inside).symm
          · simp only [windowPre, inside, ↓reduceIte, BodyCFG.CompiledProgram.equationFor, active,
              selected, bind, Bind.bind, Option.bind, pure, Pure.pure, sameRow]
    · have same := sharedStep.symm
      simpa only [windowPre, inside, ↓reduceIte, WholeBodyWP.transfer, sharedPre] using same

/-- Expose a generated straight-line window at the current state through the
normal program VC. The final continuation remains shared. -/
theorem controlPre_iff_window (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (allowed : State → C → Prop) (depth : Nat)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure)
    (rows : List (WindowRow config limits)) (before : State) :
    controlPre config limits graph table allowed depth post failure before ↔
      windowPre config limits graph table allowed depth post failure rows before :=
  (WholeBodyWP.eliminate_iff _ _ _ _ _ _ _ _).trans
    (windowPre_iff config limits graph table allowed depth post failure rows before).symm

/-- Use the existing graph rank and shared fixed point with the reduced
transfer equations. -/
def pre (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) (before : State) : Prop :=
  let graph := BodyCFG.compileProgram program.bodies
  WholeBodyWP.entryMatchesLoaded program.root before ∧
    controlPre config limits graph table allowed before.stack.frames.size post failure before

theorem pre_iff (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) (before : State) :
    pre config limits program table allowed post failure before ↔
      (BodyVCGen.generateProgram config limits program allowed post failure).pre before := by
  simp only [pre, controlPre_eq, BodyVCGen.generatedProgramPre_eq, WholeBodyWP.catalogBodyPre]

/-- Emit the entry, selected-location and residual obligations with the same
reduced table. Successors use caller-supplied shared predicates. -/
def generateProgram (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) : BodyVCGen.ProgramConditions State :=
  let graph := BodyCFG.compileProgram program.bodies
  let continued := fun atPC fallback more after =>
    if more then BodyCFG.programRoute graph atPC fallback after else post .stopped after
  { graph
    pre := pre config limits program table allowed post failure
    equations := fun atPC fallback identity => (graph.lookup identity).map fun cfg =>
      cfg.equations.map fun equation =>
        let location : BodyCFG.ProgramLocation := ⟨identity, equation.pc⟩
        ∀ before, graph.equationFor before = some (location, equation) → atPC location before →
          ∀ choice, allowed before choice →
            rowPre config limits table identity equation choice (continued atPC fallback) failure before
    residual := fun atPC fallback =>
      ∀ before, graph.equationFor before = none → fallback before →
        ∀ choice, allowed before choice →
          tablePre config limits graph table choice (continued atPC fallback) failure before }

theorem generateProgram_eq (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) :
    generateProgram config limits program table allowed post failure =
      BodyVCGen.generateProgram config limits program allowed post failure := by
  have samePre : pre config limits program table allowed post failure =
      (BodyVCGen.generateProgram config limits program allowed post failure).pre :=
    funext fun before => propext (pre_iff config limits program table allowed post failure before)
  have sameTable : tablePre config limits (BodyCFG.compileProgram program.bodies) table =
      BodyCFG.programTablePre config limits (BodyCFG.compileProgram program.bodies) := by
    funext choice next onError before
    exact propext (tablePre_iff config limits (BodyCFG.compileProgram program.bodies) table
      choice next onError before)
  simp only [generateProgram, samePre, sameTable, rowPre_eq, BodyVCGen.generateProgram]
  rfl

/-- Use the canonical program operation with the specialized transfer table
as the proof interface. -/
def run (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (_table : Table config limits) (allowed : State → C → Prop) :
    BodyVCGen.RunProgram config limits program allowed :=
  BodyVCGen.runProgram config limits program allowed

@[spec] theorem spec_run (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) :
    Triple (run config limits program table allowed) (pre config limits program table allowed post failure)
      post failure :=
  Triple.iff.mpr fun before checked => (pre_iff config limits program table allowed post failure before).mp checked

/-- A direct VC for the compiler-selected window at the prepared entry. -/
theorem spec_run_window (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure)
    (rows : List (WindowRow config limits)) :
    Triple (run config limits program table allowed)
      (fun before => WholeBodyWP.entryMatchesLoaded program.root before ∧
        windowPre config limits (BodyCFG.compileProgram program.bodies) table allowed
          before.stack.frames.size post failure rows before) post failure :=
  Triple.iff.mpr fun before checked => (pre_iff config limits program table allowed post failure before).mp
    ⟨checked.1, (controlPre_iff_window config limits (BodyCFG.compileProgram program.bodies)
      table allowed before.stack.frames.size post failure rows before).mpr checked.2⟩

/-- Open one layer of the reduced program without expanding its successors. -/
macro "miri_generated_program" : tactic =>
  `(tactic| first
    | rw [pre, controlPre_reduce]
    | rw [controlPre_reduce])

/-- Open the straight-line window emitted for an imported location. -/
macro "miri_generated_window" rows:term : tactic =>
  `(tactic| first
    | rw [pre, controlPre_iff_window (rows := $rows)]
    | rw [controlPre_iff_window (rows := $rows)]
    | rw [← windowPre_iff (rows := $rows)])

/-- Normalize the concrete instruction, leaving configured effects and shared
success and failure continuations symbolic. -/
macro "miri_reduce_node" node:ident : tactic =>
  `(tactic| (
    conv =>
      lhs
      simp only [$node:ident, BodyCFG.nodePre]
      simp only [DiscriminantWP.statementPre_setDiscriminant, StorageLiveWP.statement_storageLive,
        PlaceMentionWP.canonical_statementPre, NondivergingIntrinsicWP.statementPre_intrinsic,
        CanonicalStepWP.terminatorPre, DropWP.selectedDrop_eq, AssertPanicWP.selectedAssert_eq,
        AssertPanicWP.selectedUnwindTerminate_eq]
      simp only [CanonicalStepWP.statementPre, CanonicalStepWP.selectedTerminatorPre,
        InstructionWP.terminatorPreWithReturn,
        BranchControlWP.switchPre, BranchControlWP.readOperand,
        CanonicalStepWP.canonical_assertConditionPre, BranchControlWP.assertConditionPre,
        RvalueWP.evalPre, RvalueWP.actionPre_bind_fun,
        EffectSpecs.canonical_rvalue_operand, EffectSpecs.canonical_rvalue_place,
        EffectSpecs.canonical_rvalue_placeToOp,
        PlaceMentionWP.evalPre, PlaceMentionWP.projectionsPre, PlaceMentionWP.projectPre,
        NondivergingIntrinsicWP.wp_eval, NondivergingIntrinsicWP.evalPre, NondivergingIntrinsicWP.copyPre,
        CopyTreeWP.intrinsicCopyPre_eq, CopyTreeWP.copyActionPre_eq, StorageLiveWP.wp_storageLiveDyn,
        Array.empty_beq_eq, Array.beq_empty_eq, Array.push_beq_push, Array.isEmpty_empty,
        Array.isEmpty_push, List.toList_toArray, Array.toList_empty, Array.toList_push,
        Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.false_eq_true,
        BinOp.leftHomogeneous, BinOp.rightHomogeneous, ↓reduceIte,
        miri_initial_wp]
    try rfl))

end Miri.Verification.GeneratedBodyVC

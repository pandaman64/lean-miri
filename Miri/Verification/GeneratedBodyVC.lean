import Miri.Verification.BodyVCGen
import Miri.Verification.InitialWPAttr

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

private def tablePre (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) (choice : C) (post : Success) (failure : Failure)
    (before : State) : Prop :=
  match graph.graphFor before with
  | none => CanonicalStepWP.choicePre config limits choice post failure before
  | some (identity, cfg) =>
    match cfg.equationFor before with
    | none => CanonicalStepWP.choicePre config limits choice post failure before
    | some eq =>
      match table[(identity.index, eq.pc.block, eq.pc.statementIndex)]? with
      | some reduced =>
        if reduced.node = eq.node then reduced.pre choice post failure before
        else BodyCFG.nodePre config limits choice post failure before eq.node
      | none => BodyCFG.nodePre config limits choice post failure before eq.node

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
        BodyCFG.Equation.pre, postEq cfg]
      split
      next reduced atIndex =>
        split
        next same => rw [reduced.exact, same]
        · rfl
      · rfl

/-- Dispatch using the actual active frame, MIR location and instruction.
Rows with missing or different MIR use the canonical exact precondition. -/
def rule (config : Config) (limits : Limits) (graph : BodyCFG.CompiledProgram)
    (table : Table config limits) : WholeBodyWP.Rule (ExecutionMachine.step config limits) where
  pre := tablePre config limits graph table
  exact choice post failure before :=
    (tablePre_iff config limits graph table choice post failure before).trans
      (BodyCFG.programTablePre_iff config limits graph choice post failure before)

/-- Use the existing graph rank and shared fixed point with the reduced
transfer equations. -/
def pre (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) (before : State) : Prop :=
  let graph := BodyCFG.compileProgram program.bodies
  WholeBodyWP.entryMatchesLoaded program.root before ∧
    WholeBodyWP.eliminate (rule config limits graph table) (fun state => state.stack.frames.size)
      allowed before.stack.frames.size post failure (BodyCFG.programRank graph) before

theorem pre_iff (config : Config) (limits : Limits) (program : BodyVCGen.LoadedProgram)
    (table : Table config limits) (allowed : State → C → Prop)
    (post : WholeBodyWP.Exit → State → Prop) (failure : Failure) (before : State) :
    pre config limits program table allowed post failure before ↔
      (BodyVCGen.generateProgram config limits program allowed post failure).pre before := by
  rw [BodyVCGen.generatedProgramPre_eq, WholeBodyWP.catalogBodyPre_iff]
  simp only [pre, WholeBodyWP.eliminate_iff, WholeBodyWP.solve_iff]

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

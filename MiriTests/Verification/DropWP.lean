import Miri.Verification.ExactWP

namespace MiriTests.Verification.DropWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification Std.WP
open Miri.Verification.DropWP Miri.Verification.RvalueWP Miri.Verification.StepWP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Limits" => ExecutionMachine.Limits
local notation "State" => MachineHooks.State K U
local notation "Errors" => StepError → State → Prop

/-- Empty glue jumps directly at the state left by the glue queries. -/
example (config : Config) (limits : Limits) (choice : C) (info : SourceInfo)
    (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
    (post : State → Prop) (onError : Errors) (before evaluated resolved ready : State)
    (dest : RuntimePlace Provenance) (callee : CallInstance) (definition : DefId)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (eval : PlaceDynamic.evalPlace
        (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
        choice place false before = .ok dest evaluated)
    (resolve : config.virtual.compiler.resolveDropGlue dest.layout.ty evaluated = .ok callee resolved)
    (kind : (ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits).instanceKind callee resolved = .ok (.Shim (.DropGlue definition none)) ready)
    (current : ready.stack.currentFrame? = some frame) :
    CanonicalStepWP.selectedTerminatorPre config limits choice
      ⟨info, .Drop place target unwind true none⟩ post onError before =
      post { ready with stack := ⟨ready.stack.frames.pop.push { frame with location := .mir ⟨target, 0⟩ }⟩ } := by
  miri_drop_wp
  simp only [actionPre_ok eval, actionPre_ok resolve, actionPre_ok kind,
    InstructionWP.locationPre, current]

/-- The debug consistency failure receives the post-query state. -/
example {P S E FnABI ArgABI : Type} (hooks : CallHooks P S C E O X FnABI ArgABI)
    (choice : C) (budget : Nat) (place : RuntimeStackPlace P) (original resolved : CallInstance)
    (allocated : MPlaceTy P) (target : BasicBlockId) (unwind : UnwindAction)
    (post : S → Prop) (onError : StepError → S → Prop) (before allocation classified ready : S)
    (force : hooks.forceAllocation choice place before = .ok allocated allocation)
    (classify : hooks.isDynamic allocated.layout.ty allocation = .ok false classified)
    (debug : hooks.debugAssertions = true)
    (resolve : hooks.resolveDropGlue choice allocated.layout.ty classified = .ok resolved ready)
    (mismatch : (original == resolved) = false) :
    actionPre (Call.initDropInPlaceCall hooks choice budget place original target unwind)
      (fun _ => post) onError before =
      onError (.invalidProgram "drop glue instance mismatch") ready := by
  miri_drop_wp
  simp only [actionPre_ok force, actionPre_ok classify, actionPre_ok resolve,
    debug, mismatch, Bool.false_eq_true, ↓reduceIte]

/-- The call gets the resolved ABI, one copied mutable reference, the fake
unit destination, and both original edges. -/
example {P S E FnABI ArgABI : Type} (hooks : CallHooks P S C E O X FnABI ArgABI)
    (choice : C) (budget : Nat) (place : RuntimeStackPlace P) (original concrete : CallInstance)
    (allocated receiver : MPlaceTy P) (target : BasicBlockId) (unwind : UnwindAction)
    (post : S → Prop) (onError : StepError → S → Prop)
    (before allocation classified unpacked resolved typed referenced ready : S)
    (abi : FnABI) (arg : OpTy P) (ret : RuntimeStackPlace P)
    (force : hooks.forceAllocation choice place before = .ok allocated allocation)
    (classify : hooks.isDynamic allocated.layout.ty allocation = .ok true classified)
    (unpack : hooks.unpackDynForDrop choice allocated classified = .ok receiver unpacked)
    (resolve : hooks.resolveDropGlue choice receiver.layout.ty unpacked = .ok concrete resolved)
    (callABI : hooks.fnAbiOfInstance choice concrete #[] resolved = .ok abi typed)
    (reference : hooks.mplaceToMutRef choice receiver typed = .ok arg referenced)
    (unitReturn : hooks.fakeUnitReturn choice referenced = .ok ret ready) :
    actionPre (Call.initDropInPlaceCall hooks choice budget place original target unwind)
      (fun _ => post) onError before =
      CallWP.dispatchPre hooks choice post onError budget
        ⟨.Instance concrete, hooks.rustAbi, some abi, #[.Copy arg], false, ret, some target, unwind⟩ ready := by
  miri_drop_wp
  simp only [actionPre_ok force, actionPre_ok classify, ↓reduceIte, actionPre_ok unpack,
    actionPre_ok resolve, actionPre_ok callABI, actionPre_ok reference, actionPre_ok unitReturn]

/-- Missing dynamic metadata fails at the state left by type classification. -/
example {S F A : Type} (hooks : VTableHooks Provenance S C F A) (choice : C)
    (place : MPlaceTy Provenance) (predicates : PredicateList) (before checked : S)
    (post : OpTy Provenance → S → Prop) (onError : StepError → S → Prop)
    (classify : hooks.isDynamic choice place.layout.ty before = .ok true checked)
    (metadata : place.mplace.metadata = .none) :
    actionPre (VTable.unpackDynTrait hooks choice ⟨.indirect place.mplace, place.layout⟩ predicates)
      post onError before = onError (.invalidProgram "dynamic place has no metadata") checked := by
  rw [actionPre_unpackVTable, actionPre_ok classify]
  simp only [metadata, MemPlaceMeta.unwrapMeta, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

set_option experimental.vcgen true in
/-- The generated step VC rejects an async drop at the state produced by the
terminator pre-hook, for every permitted choice. -/
example (config : Config) (limits : Limits) (allowed : State → C → Prop) (before : State)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (location : Location)
    (block : BasicBlock) (info : SourceInfo) (place : Place) (target asyncTarget : BasicBlockId)
    (unwind : UnwindAction) (replace : Bool) (post : Bool → State → Prop) (onError : Errors)
    (current : before.stack.currentFrame? = some frame) (pc : frame.location = .mir location)
    (selected : frame.body.basicBlocks[location.block]? = some block)
    (slot : block.statements[location.statementIndex]? = none)
    (drop : block.terminator = ⟨info, .Drop place target unwind replace (some asyncTarget)⟩)
    (preHook : ∀ choice, allowed before choice → ∃ ready,
      TerminatorMachine.beforeTerminatorWithChoice (ExecutionMachine.withValidation config limits).terminators
        ((ExecutionMachine.withValidation config limits).preemptionChoice choice) before = .ok () ready ∧
      onError (.invalidProgram "Async Drop must be expanded or reset to sync") ready) :
    Triple (OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits) (allowed := allowed))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  intro choice permitted
  obtain ⟨ready, ran, rejected⟩ := preHook choice permitted
  simp only [CanonicalStepWP.choicePre, StepWP.driverChoicePreWith, current, pc, selected, slot,
    drop, CanonicalStepWP.terminatorPre, ← actionPre_eq_wp, actionPre_ok ran]
  miri_instruction_wp
  exact rejected

end MiriTests.Verification.DropWP

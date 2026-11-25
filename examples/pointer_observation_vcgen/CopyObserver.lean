import CopyTail
import CopyReturnValidation
import Miri.Verification.CopyInitialWP

namespace PointerObservation.Copy

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Verification Fixture

set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private theorem rowSource (source : UInt8) (stale : Bool) (layout4 : LocalLayout)
    (post : OpTy Provenance → State → Prop) (failure : StepError → State → Prop) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let ptr := pointer (if stale then child else BorTag.one) 1
        let op : OpTy Provenance := ⟨.indirect ⟨ptr.withOptionalProvenance, .none, none⟩, layout⟩
        match (entry.stack.currentFrame?.bind (fun frame => frame.locals[3]?) : Option (LocalState Provenance LocalLayout)) with
        | some ⟨.live (.immediate imm), some pointerLayout⟩ =>
          RvalueWP.actionPre (hooks.dereference () ⟨.immediate imm, pointerLayout⟩)
            (fun place => post ⟨.indirect place.mplace, place.layout⟩) failure entry =
            post op entry
        | _ => False := by
  cases stale <;> cbv

private theorem rowLocalOperand (source : UInt8) (stale : Bool) (layout4 : LocalLayout)
    (post : OpTy Provenance → State → Prop) (failure : StepError → State → Prop) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
      match (entry.stack.currentFrame?.bind (fun frame => frame.locals[3]?) : Option (LocalState Provenance LocalLayout)) with
      | some ⟨.live (.immediate imm), some pointerLayout⟩ =>
        OperandPlaceWP.localOperandPre hooks () 3 none post failure entry =
          post ⟨.immediate imm, pointerLayout⟩ entry
      | _ => False := by
  cases stale <;> cbv

private theorem rowTypeHook (source : UInt8) (stale : Bool) (layout4 : LocalLayout)
    (post : OpTy Provenance → State → Prop) (failure : StepError → State → Prop) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let ptr := pointer (if stale then child else BorTag.one) 1
        let op : OpTy Provenance := ⟨.indirect ⟨ptr.withOptionalProvenance, .none, none⟩, layout⟩
        RvalueWP.actionPre (hooks.checkPlaceType () ⟨3, #[.Deref]⟩ op)
          (fun _ => post op) failure entry = post op entry := by
  cases stale <;> cbv

private theorem postCopyLoad_operand (source : UInt8) (stale : Bool) (layout4 : LocalLayout)
    (post : OpTy Provenance → State → Prop) (failure : StepError → State → Prop) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
        let ptr := pointer (if stale then child else BorTag.one) 1
        let op : OpTy Provenance := ⟨.indirect ⟨ptr.withOptionalProvenance, .none, none⟩, layout⟩
        RvalueWP.actionPre (OperandMachine.evalOperand hooks () (.Copy ⟨3, #[.Deref]⟩) (some layout))
          post failure entry = post op entry := by
  cases launched : postCopyLoadEntry source stale layout4 with
  | none => simpa only [launched] using rowSource source stale layout4 post failure
  | some pair =>
    obtain ⟨config, entry⟩ := pair
    have deref := rowSource source stale layout4 post failure
    have typed := rowTypeHook source stale layout4 post failure
    simp only [launched] at deref typed ⊢
    cases output : (entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout)) with
    | none => simp only [output] at typed
    | some layout =>
      simp only [output] at deref typed ⊢
      let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
      let typedPost := fun result : OpTy Provenance =>
        RvalueWP.actionPre (hooks.checkPlaceType () ⟨3, #[.Deref]⟩ result) (fun _ => post result) failure
      have derefTyped := rowSource source stale layout4 typedPost failure
      have localRead := rowLocalOperand source stale layout4 (fun base =>
        RvalueWP.actionPre (hooks.dereference () base) (fun place =>
          typedPost ⟨.indirect place.mplace, place.layout⟩) failure) failure
      simp only [launched, output] at derefTyped localRead
      cases saved : (entry.stack.currentFrame?.bind (fun frame => frame.locals[3]?) :
          Option (LocalState Provenance LocalLayout)) with
      | none => simp only [saved] at deref
      | some savedLocal =>
        obtain ⟨value, cached⟩ := savedLocal
        cases value with
        | dead => simp only [saved] at deref
        | live operand =>
          cases operand with
          | indirect => simp only [saved] at deref
          | immediate imm =>
            cases cached with
            | none => simp only [saved] at deref
            | some pointerLayout =>
              simp only [saved] at localRead derefTyped
              simp only [OperandPlaceWP.actionPre_evalOperand, OperandPlaceWP.actionPre_evalPlaceToOpDeref]
              rw [localRead, derefTyped]
              exact typed

private theorem loadDestination (source : UInt8) (stale : Bool) (layout4 : LocalLayout)
    (post : RuntimePlace Provenance → State → Prop) (failure : StepError → State → Prop) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      let hooks := ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        RvalueWP.actionPre (hooks.evalPlace () ⟨0, #[]⟩ true) post failure entry =
          post ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 1), layout⟩ entry := by
  cbv

private theorem postCopyLoad_row (source : UInt8) (stale : Bool) (layout4 : LocalLayout)
    (post : Bool → State → Prop) (failure : StepError → State → Prop) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let checked := ExecutionMachine.withValidation config limits
        let hooks := ExecutionMachine.rvalueHooks checked limits
        let ptr := pointer (if stale then child else BorTag.one) 1
        let op : OpTy Provenance := ⟨.indirect ⟨ptr.withOptionalProvenance, .none, none⟩, layout⟩
        let dest : RuntimePlace Provenance := ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 1), layout⟩
        BodyCFG.nodePre config limits () post failure entry mir_0_bb0_10 =
          RvalueWP.actionPre (MachineHooks.withRetagMode .Default (hooks.copyOp () op dest))
            (fun _ => InstructionWP.finishStatementResultPre (entry.stack.frames.size - 1) post failure)
            failure entry := by
  cases entered : postCopyLoadEntry source stale layout4 with
  | none => simpa only [entered] using loadDestination source stale layout4 (fun _ _ => True) failure
  | some pair =>
    obtain ⟨config, entry⟩ := pair
    let hooks := ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits
    let copyOperand := fun dest op =>
      RvalueWP.actionPre (MachineHooks.withRetagMode .Default (hooks.copyOp () op dest))
        (fun _ => InstructionWP.finishStatementResultPre (entry.stack.frames.size - 1) post failure)
        failure
    let evaluate := fun dest : RuntimePlace Provenance =>
      RvalueWP.actionPre (hooks.evalOperand () (.Copy ⟨3, #[.Deref]⟩) (some dest.layout))
        (copyOperand dest) failure
    have dest := loadDestination source stale layout4 evaluate failure
    simp only [entered] at dest
    cases output : (entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout)) with
    | none => simp only [output] at dest
    | some layout =>
      let target : RuntimePlace Provenance := ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 1), layout⟩
      have operand := postCopyLoad_operand source stale layout4 (copyOperand target) failure
      simp only [entered, output] at dest operand ⊢
      change RvalueWP.actionPre (hooks.evalPlace () ⟨0, #[]⟩ true) evaluate failure entry = _
      rw [dest]
      exact operand

private theorem postCopyLoad_selected (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
    (postCopyLoadEntry source stale layout4).bind (fun after => BodyCFG.selected after.2) =
      some (⟨0, 10⟩, mir_0_bb0_10) := by
  cbv

section

variable {K U : Type}
local notation "State" => MachineHooks.State K U

/-- A default-mode scope can pass through a result whose tracker still uses
that mode, on success or failure. -/
private theorem actionPre_defaultRetag (action : RvalueM State A)
    (post : A → State → Prop) (failure : StepError → State → Prop) (before : State)
    (mode : before.machine.borrowTracker.map (·.retagMode) = some .Default)
    (plain : RvalueWP.actionPre action
      (fun value after => after.machine.borrowTracker.map (·.retagMode) = some .Default ∧ post value after)
      (fun error after => after.machine.borrowTracker.map (·.retagMode) = some .Default ∧ failure error after) before) :
    RvalueWP.actionPre (MachineHooks.withRetagMode .Default action) post failure before := by
  have same (state : State) (tracker : MachineHooks.BorrowState)
      (found : state.machine.borrowTracker = some tracker) (mode : tracker.retagMode = .Default) :
      {state with machine.borrowTracker := some {tracker with retagMode := .Default}} = state := by
    have keep : {tracker with retagMode := .Default} = tracker := by
      rw [← mode]
    simp only [keep]
    rw [← found]
  cases tracking : before.machine.borrowTracker with
  | none => simp only [tracking, Option.map_none, reduceCtorEq] at mode
  | some tracker =>
    simp only [tracking, Option.map_some, Option.some.injEq] at mode
    simp only [RvalueWP.actionPre, MachineHooks.withRetagMode, tracking, same _ _ tracking mode] at plain ⊢
    cases acted : action before with
    | ok value after =>
      simp only [acted] at plain ⊢
      obtain ⟨kept, postcondition⟩ := plain
      cases found : after.machine.borrowTracker with
      | none => simp only [found, Option.map_none, reduceCtorEq] at kept
      | some next =>
        simp only [found, Option.map_some, Option.some.injEq] at kept
        simpa only [found, mode, same _ _ found kept] using postcondition
    | error error after =>
      simp only [acted] at plain ⊢
      obtain ⟨kept, postcondition⟩ := plain
      cases found : after.machine.borrowTracker with
      | none => simp only [found, Option.map_none, reduceCtorEq] at kept
      | some next =>
        simp only [found, Option.map_some, Option.some.injEq] at kept
        simpa only [found, mode, same _ _ found kept] using postcondition

end

section

attribute [local cbv_opaque] Allocation.readScalar MemoryObservationWP.scalarFromImage
  Scalar.toUInt8 Scalar.fromScalarInt ScalarInt.ofUInt8
private theorem scalarFromImage_one (layout : TargetDataLayout) (start : UInt64)
    (byte : UInt8) (provenance : ProvenanceMap Provenance) :
    MemoryObservationWP.scalarFromImage layout ⟨⟨start⟩, ⟨1⟩⟩ false
      (.ok #[byte]) (.ok (.ok ())) provenance = .ok (Scalar.fromScalarInt (ScalarInt.ofUInt8 byte)) :=
  CopyInitialWP.scalarFromImage_byte layout ⟨start⟩ byte provenance

attribute [local cbv_eval] MemoryObservationWP.readScalar_eq_image
  scalarFromImage_one CopyInitialWP.toUInt8_byte

/-- The typed observer reads the copied byte with the root tag. A stale child
reports the precise load failure and retains the copied byte. -/
private theorem postCopyLoad_readRawMode (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let ptr := pointer (if stale then child else BorTag.one) 1
        let op : OpTy Provenance := ⟨.indirect ⟨ptr.withOptionalProvenance, .none, none⟩, layout⟩
        RvalueWP.actionPre (PlaceMachine.readRaw config.access op)
          (fun value after => stale = false ∧
            after = {entry with machine := {entry.machine with memory := after.machine.memory}} ∧
            match value with
            | .immediate immediate => immediate.value = .scalar (Scalar.fromScalarInt (ScalarInt.ofUInt8 source))
            | .place _ => False)
          (fun error after => stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source]) ∧
            after.machine.borrowTracker.map (·.retagMode) = some .Default) entry := by
  cases stale <;>
    cbv


private theorem postCopyLoad_copyPlanMode (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let checked := ExecutionMachine.withValidation config limits
        entry.machine.borrowTracker.map (·.retagMode) = some .Default ∧
        checked.copy.compatible layout layout = .ok true ∧
        checked.copy.hasPadding layout = .ok false ∧
        layout.layout.isSized = true := by
  cbv

private theorem postCopyLoad_finish (source : UInt8) (layout4 : LocalLayout)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) :
    match postCopyLoadEntry source false layout4 with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout) with
      | none => False
      | some layout =>
        let checked := ExecutionMachine.withValidation config limits
        let dest : RuntimePlace Provenance := ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 1), layout⟩
        let value : Immediate Provenance := .scalar (.fromScalarInt (ScalarInt.ofUInt8 source))
        let entry := {entry with machine := {entry.machine with memory}}
        PlaceReadWriteWP.writeNoValidatePre (ExecutionMachine.projectionHooks checked).place
          () value dest (fun _ after =>
            after.machine.borrowTracker.map (·.retagMode) = some .Default ∧
            InstructionWP.finishStatementResultPre (entry.stack.frames.size - 1)
              (fun more final => more = true ∧ scalarAt final 0 = some source)
              (fun _ _ => False) after) (fun _ _ => False) entry := by
  cbv

end

/-- Execute the emitted observer, using the exact state at its location. -/
theorem postCopyLoad_observation (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
    match postCopyLoadEntry source stale layout4 with
    | none => False
    | some (config, entry) =>
      prefixPre config (fun final => stale = false ∧ scalarAt final 0 = some source)
        (fun error final => stale = true ∧ error = disabledLoad ∧ bytesAt 1 final = some (.ok #[source]))
        10 [mir_0_bb0_10] entry := by
  have selected := postCopyLoad_selected source stale layout4
  have plan := postCopyLoad_copyPlanMode source stale layout4
  have read := postCopyLoad_readRawMode source stale layout4
  cases entered : postCopyLoadEntry source stale layout4 with
  | none => simp only [entered, Option.bind_none] at selected; cases selected
  | some pair =>
    obtain ⟨config, entry⟩ := pair
    let post := fun more final => more = true ∧ stale = false ∧ scalarAt final 0 = some source
    let failure := fun error final => stale = true ∧ error = disabledLoad ∧ bytesAt 1 final = some (.ok #[source])
    have row := postCopyLoad_row source stale layout4 post failure
    simp only [entered, Option.bind_some] at selected plan read row
    change BodyCFG.selected entry = some (⟨0, 10⟩, mir_0_bb0_10) ∧
        BodyCFG.nodePre config limits () post failure entry mir_0_bb0_10
    refine ⟨selected, ?_⟩
    cases output : (entry.stack.currentFrame?.bind (fun frame => frame.locals[0]?) |>.bind (·.layout)) with
    | none => simp only [output] at row
    | some layout =>
      simp only [output] at plan read row
      rw [row]
      refine actionPre_defaultRetag _ _ _ _ plan.1 ?_
      let checked := ExecutionMachine.withValidation config limits
      let ptr := pointer (if stale then child else BorTag.one) 1
      let op : OpTy Provenance := ⟨.indirect ⟨ptr.withOptionalProvenance, .none, none⟩, layout⟩
      let dest : RuntimePlace Provenance := ⟨.local 0 0 none (LocalsIdentity.ofAllocationToken 1), layout⟩
      let copy := (ExecutionMachine.withValidation checked limits).copy
      let hooks := (ExecutionMachine.projectionHooks checked).place
      have compatible : copy.compatible layout layout = .ok true := plan.2.1
      have padding : copy.hasPadding layout = .ok false := plan.2.2.1
      have sized := plan.2.2.2
      rw [RvalueWP.canonical_copyOp, PlaceReadWriteWP.actionPre_copyRuntimePlace]
      change PlaceReadWriteWP.copyPre hooks copy () op dest false _ _ entry
      unfold PlaceReadWriteWP.copyPre PlaceReadWriteWP.copyNoValidatePre
      simp only [op, dest, compatible, padding, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
      change RvalueWP.actionPre (PlaceMachine.readRaw config.access op) _ _ entry
      cases ran : PlaceMachine.readRaw config.access op entry with
      | error error after =>
        dsimp only [op, ptr] at ran
        simp only [RvalueWP.actionPre, op, ptr, ran] at read ⊢
        exact ⟨read.2.2.2, read.1, read.2.1, read.2.2.1⟩
      | ok value after =>
        dsimp only [op, ptr] at ran
        simp only [RvalueWP.actionPre, op, ptr, ran] at read ⊢
        obtain ⟨success, retained, observed⟩ := read
        cases value with
        | place _ => exact observed.elim
        | immediate loaded =>
          subst stale
          have finished := postCopyLoad_finish source layout4 after.machine.memory
          let observe : State → Prop := fun final =>
            final.machine.borrowTracker.map (·.retagMode) = some .Default ∧
            InstructionWP.finishStatementResultPre (entry.stack.frames.size - 1)
              (fun more result => more = true ∧ scalarAt result 0 = some source)
              (fun _ _ => False) final
          have validated := postCopyLoad_validate source layout4 after.machine.memory observe (fun _ _ => False)
          simp only [postCopyReturnWritePre, entered, output, ↓reduceIte] at validated
          simp only [entered, output] at finished
          simp only [sized, Bool.not_true, Bool.false_or, Bool.false_eq_true, bne_self_eq_false,
            ↓reduceIte, observed, false_and, and_false, true_and, post, failure]
          rw [retained]
          exact Eq.mpr validated finished

open Lean Elab Command in
run_cmd liftTermElabM do
  for dependency in (← collectAxioms ``postCopyLoad_observation) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "postCopyLoad_observation depends on unapproved axiom {dependency}"

#print axioms postCopyLoad_observation

end PointerObservation.Copy

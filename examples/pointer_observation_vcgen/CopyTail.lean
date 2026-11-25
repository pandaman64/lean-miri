import Copy
import GeneratedCopyRows
import Miri.Verification.CopyInitialWP

namespace PointerObservation.Copy

open Miri.ABI Miri.Input Miri.TreeBorrows Miri.Interpreter Miri.Verification Miri.Memory Miri.MIR Fixture

/-- Expected post-copy state for this one-allocation fixture. -/
def postCopyTree (source : UInt8) (stale : Bool) : Option (Config × State) := do
  let (config, before) ← (scenario source source stale).toOption
  let entry ← (before.machine.memory.live.get? allocId).map ULift.up
  let entry := entry.down
  let tags ← (before.machine.borrowTracker.map fun t => ULift.up t.global.protectedTags)
  let tree := entry.allocation.extra
  let read := tree.performBorrowAccessRange (.concrete BorTag.one) (Size.ofBytes 0)
    (Size.ofBytes 1) .Read tags.down .VisitChildrenOfAccessed
  let written := read.tree.performBorrowAccessRange (.concrete BorTag.one) (Size.ofBytes 1)
    (Size.ofBytes 1) .Write tags.down .VisitChildrenOfAccessed
  let original := before.machine.memory
  let live := original.live.insert allocId {entry with allocation := entry.allocation.setExtra written.tree}
  let memory := {original with live}
  let state := {before with machine := {before.machine with memory}}
  return (config, (Step.finishStatement 0 (state, .ok ())).1)

/-- Frame at the observer load, after caching the unit layout and ending
storage for the intrinsic's three temporaries. -/
def postCopyLoadEntry (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
    Option (Config × State) := do
  let (config, entry) ← postCopyTree source stale
  let frame ← entry.stack.currentFrame?.map ULift.up
  let cached ← (frame.down.getOrCacheLocalLayout 4 layout4).toOption.map ULift.up
  let frame ← (cached.down.1.replaceLocalValue 6 .dead).toOption.map ULift.up
  let frame ← (frame.down.replaceLocalValue 5 .dead).toOption.map ULift.up
  let frame ← (frame.down.replaceLocalValue 4 .dead).toOption.map ULift.up
  let frame := {frame.down with location := .mir ⟨0, 10⟩}
  return (config, {entry with stack := ⟨#[frame]⟩})

set_option maxHeartbeats 300000
set_option maxRecDepth 65536
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

theorem postCopyTree_bytes (source : UInt8) (stale : Bool) :
    (postCopyTree source stale).bind (fun after => bytesAt 1 after.2) =
      some (.ok #[source]) := by
  cbv

theorem postCopyTree_selected (source : UInt8) (stale : Bool) :
    (postCopyTree source stale).bind (fun after => BodyCFG.selected after.2) =
      some (⟨0, 6⟩, mir_0_bb0_6) := by
  cbv

/-- The post-copy program counter and statement agree with the first
row of the emitted suffix. -/
theorem postCopyTree_selected_generated (source : UInt8) (stale : Bool) :
    (postCopyTree source stale).bind (fun after => BodyCFG.selected after.2) =
      (postCopyTree source stale).bind (fun (config, _) =>
        ((GeneratedBodySafety.window_0_bb0_5 config limits).drop 1).head?.map
          (fun row => (row.location.pc, row.reduced.node))) := by
  have generated (config : Config) :
      ((GeneratedBodySafety.window_0_bb0_5 config limits).drop 1).head?.map
        (fun row => (row.location.pc, row.reduced.node)) =
        some (⟨0, 6⟩, mir_0_bb0_6) := rfl
  have selected := postCopyTree_selected source stale
  cases next : postCopyTree source stale with
  | none => simp [next] at selected
  | some pair =>
    obtain ⟨config, entry⟩ := pair
    simpa only [next, Option.bind_some, generated] using selected

section

set_option maxHeartbeats 3000000
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
theorem postCopyLoad_readRaw (source : UInt8) (stale : Bool) (layout4 : LocalLayout) :
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
          (fun error after => stale = true ∧ error = disabledLoad ∧ bytesAt 1 after = some (.ok #[source])) entry := by
  cases stale <;>
    cbv

/-- The immediate write to the return local preserves the symbolic byte. -/
theorem postCopyLoad_write (source : UInt8) (layout4 : LocalLayout)
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
          () value dest (fun _ after => scalarAt after 0 = some source) (fun _ _ => False) entry := by
  cbv

end

section

set_option maxHeartbeats 1000000

/-- Layout of the unit temporary assigned immediately after the copy. -/
def row6Layout : Option LocalLayout :=
  match configure input 0 with
  | .error _ => none
  | .ok (_, prepared, program) =>
    match layoutOfLocal prepared.down program.down 4 with
    | .error _ => none
    | .ok layout => some layout.down

private theorem row6Destination (source : UInt8) (stale : Bool)
    (post : RuntimePlace Provenance → State → Prop) (failure : StepError → State → Prop) :
    match postCopyTree source stale with
    | none => False
    | some (config, entry) =>
      let hooks := ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits
      match entry.stack.currentFrame?, row6Layout with
      | some frame, some layout =>
        match frame.getOrCacheLocalLayout 4 layout with
        | .ok (frame, _) =>
          RvalueWP.actionPre (hooks.evalPlace () ⟨4, #[]⟩ true) post failure entry =
            post ⟨.local 0 4 none (LocalsIdentity.ofAllocationToken 1), layout⟩ {entry with stack := ⟨#[frame]⟩}
        | .error _ => False
      | _, _ => False := by
  cbv

section
attribute [local cbv_opaque] ValidityVisitor.validatePlace
private theorem row6Effect (source : UInt8) (stale : Bool)
    (post : Unit → State → Prop) (failure : StepError → State → Prop) :
    match postCopyTree source stale with
    | none => False
    | some (config, entry) =>
      let hooks := ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits
      match entry.stack.currentFrame?, row6Layout with
      | some frame, some layout =>
        match frame.getOrCacheLocalLayout 4 layout with
        | .ok (frame, _) =>
          let state := {entry with stack := ⟨#[frame]⟩}
          let dest : RuntimePlace Provenance := ⟨.local 0 4 none (LocalsIdentity.ofAllocationToken 1), layout⟩
          RvalueWP.actionPre (hooks.evalOperand () (.Constant ⟨⟨6⟩, none, .Val .ZeroSized 3⟩) (some layout))
            (fun op => RvalueWP.actionPre (hooks.withRetagMode () .Default (hooks.copyOp () op dest)) post failure)
            failure state = post () state
        | .error _ => False
      | _, _ => False := by
  -- Expose the shallow branch before reducing the validity visitor.
  cbv <;> simp only [ValidityVisitor.validatePlace, Bool.false_eq_true, ↓reduceIte]
end

private theorem postCopyTreeRow6 (source : UInt8) (stale : Bool)
    (post : Bool → State → Prop) (failure : StepError → State → Prop) :
    match postCopyTree source stale with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?, row6Layout with
      | some frame, some layout =>
        match frame.getOrCacheLocalLayout 4 layout with
        | .ok (frame, _) =>
          let state := {entry with stack := ⟨#[frame]⟩}
          BodyCFG.nodePre config limits () post failure entry mir_0_bb0_6 =
            InstructionWP.finishStatementResultPre (entry.stack.frames.size - 1) post failure state
        | .error _ => False
      | _, _ => False := by
  cases actual : postCopyTree source stale with
  | none => simpa only [actual] using row6Destination source stale (fun _ _ => True) failure
  | some pair =>
    obtain ⟨config, entry⟩ := pair
    let finish := InstructionWP.finishStatementResultPre (entry.stack.frames.size - 1) post failure
    let hooks := ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits
    let rest (dest : RuntimePlace Provenance) :=
      RvalueWP.actionPre (hooks.evalOperand () (.Constant ⟨⟨6⟩, none, .Val .ZeroSized 3⟩) (some dest.layout))
        (fun op => RvalueWP.actionPre (hooks.withRetagMode () .Default (hooks.copyOp () op dest))
          (fun _ => finish) failure) failure
    have dest := row6Destination source stale rest failure
    have assigned := row6Effect source stale (fun _ => finish) failure
    simp only [actual] at dest assigned
    cases cachedFrame : entry.stack.currentFrame? with
    | none => simp only [cachedFrame] at dest
    | some frame =>
      cases unitLayout : row6Layout with
      | none => simp only [cachedFrame, unitLayout] at dest
      | some layout =>
        cases cached : frame.getOrCacheLocalLayout 4 layout with
        | error reason => simp only [cachedFrame, unitLayout, cached] at dest
        | ok pair =>
          obtain ⟨frame, _⟩ := pair
          simp only [cachedFrame, unitLayout, cached] at dest assigned ⊢
          change RvalueWP.actionPre (hooks.evalPlace () ⟨4, #[]⟩ true) rest failure entry = _
          rw [dest]
          exact assigned

private theorem storageAfterUnit (source : UInt8) (stale : Bool)
    (post : Config → State → Prop) (failure : StepError → State → Prop) :
    match postCopyTree source stale with
    | none => False
    | some (config, entry) =>
      match entry.stack.currentFrame?, row6Layout with
      | some frame, some layout =>
        match frame.getOrCacheLocalLayout 4 layout with
        | .ok (frame, _) =>
          let state := {entry with stack := ⟨#[frame]⟩}
          InstructionWP.finishStatementResultPre (entry.stack.frames.size - 1)
            (fun more after => more = true ∧
              prefixPre config (post config) failure 7 [mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9] after)
            failure state ↔
          (match postCopyLoadEntry source stale layout with
            | some (config, after) => post config after
            | none => False)
        | .error _ => False
      | _, _ => False := by
  simp only [prefixPre, mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9,
    BodyCFG.nodePre, CanonicalStepWP.statementPre]
  cbv
  simp only [eq_self, true_and] <;> rfl

/-- Execute the emitted unit assignment and the three storage-dead rows.
Their exact continuation receives the frame at the observer load. -/
theorem postCopyTreePrefix (source : UInt8) (stale : Bool)
    (post : Config → State → Prop) (failure : StepError → State → Prop) :
    (match postCopyTree source stale with
      | none => False
      | some (config, entry) => prefixPre config (post config) failure 6
          [mir_0_bb0_6, mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9] entry) ↔
    (match row6Layout.bind (postCopyLoadEntry source stale) with
      | none => False
      | some (config, next) => post config next) := by
  have selected := postCopyTree_selected source stale
  cases actual : postCopyTree source stale with
  | none => simp only [actual, Option.bind_none, reduceCtorEq] at selected
  | some pair =>
    obtain ⟨config, entry⟩ := pair
    let next (more : Bool) (after : State) := more = true ∧
      prefixPre config (post config) failure 7 [mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9] after
    have assigned := postCopyTreeRow6 source stale next failure
    have ended := storageAfterUnit source stale post failure
    simp only [actual, Option.bind_some] at assigned ended selected
    cases cachedFrame : entry.stack.currentFrame? with
    | none => simp only [cachedFrame] at assigned
    | some frame =>
      cases unitLayout : row6Layout with
      | none => simp only [cachedFrame, unitLayout] at assigned
      | some layout =>
        cases cached : frame.getOrCacheLocalLayout 4 layout with
        | error reason => simp only [cachedFrame, unitLayout, cached] at assigned
        | ok result =>
          obtain ⟨frame, _⟩ := result
          simp only [cachedFrame, unitLayout, cached] at assigned ended
          change prefixPre config (post config) failure 6
            [mir_0_bb0_6, mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9] entry ↔ _
          rw [prefixPre]
          simp only [selected, eq_self, true_and, Option.bind_some]
          change BodyCFG.nodePre config limits () next failure entry mir_0_bb0_6 ↔ _
          rw [assigned]
          refine ended.trans ?_
          cases postCopyLoadEntry source stale layout <;> rfl

private theorem prefixPre_append (config : Config) (post : State → Prop) (failure : StepError → State → Prop)
    (pc : Nat) (front back : List BodyCFG.Node) (before : State) :
    prefixPre config post failure pc (front ++ back) before ↔
      prefixPre config (prefixPre config post failure (pc + front.length) back) failure pc front before := by
  induction front generalizing pc before with
  | nil => rfl
  | cons first rest ih =>
    have nextPc : pc + (first :: rest).length = pc + 1 + rest.length := by simp; omega
    simp only [List.cons_append, prefixPre, nextPc]
    have continued :
        (fun more after => more = true ∧ prefixPre config post failure (pc + 1) (rest ++ back) after) =
          (fun more after => more = true ∧ prefixPre config
            (prefixPre config post failure (pc + 1 + rest.length) back) failure (pc + 1) rest after) := by
      funext more after
      exact propext (and_congr_right fun _ => ih (pc + 1) after)
    rw [continued]

/-- The imported compiler query supplies the layout of the unit temporary. -/
theorem row6LayoutReady : row6Layout.isSome = true := by
  cbv

/-- The five-row suffix reduces to the observer load after all four
intermediate instructions execute. -/
theorem postCopyTreeSuffix (source : UInt8) (stale : Bool)
    (post : State → Prop) (failure : StepError → State → Prop) :
    (match postCopyTree source stale with
      | none => False
      | some (config, entry) => prefixPre config post failure 6 rows.tail entry) ↔
    (match row6Layout.bind (postCopyLoadEntry source stale) with
      | none => False
      | some (config, next) => prefixPre config post failure 10 [mir_0_bb0_10] next) := by
  have intermediate := postCopyTreePrefix source stale
    (fun config => prefixPre config post failure 10 [mir_0_bb0_10]) failure
  cases entered : postCopyTree source stale with
  | none => simpa only [entered] using intermediate
  | some pair =>
    obtain ⟨config, before⟩ := pair
    change prefixPre config post failure 6
      ([mir_0_bb0_6, mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9] ++ [mir_0_bb0_10]) before ↔ _
    have loadPc : 6 + [mir_0_bb0_6, mir_0_bb0_7, mir_0_bb0_8, mir_0_bb0_9].length = 10 := rfl
    rw [prefixPre_append, loadPc]
    simpa only [entered] using intermediate

end

open Lean Elab Command in
run_cmd liftTermElabM do
  for name in [``postCopyTree_bytes, ``postCopyTree_selected, ``postCopyTree_selected_generated,
      ``postCopyLoad_readRaw, ``postCopyLoad_write, ``postCopyTreeRow6, ``storageAfterUnit,
      ``postCopyTreePrefix, ``row6LayoutReady, ``postCopyTreeSuffix] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms postCopyTree_bytes
#print axioms postCopyTree_selected
#print axioms postCopyTree_selected_generated
#print axioms postCopyLoad_readRaw
#print axioms postCopyLoad_write
#print axioms postCopyTreePrefix
#print axioms postCopyTreeSuffix

end PointerObservation.Copy

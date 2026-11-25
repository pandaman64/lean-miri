import Miri.Verification.CanonicalStepWP
import Miri.Verification.FieldProjectionWP

/-! Exact preconditions for evaluating the place in a MIR `PlaceMention`. -/

namespace Miri.Verification.PlaceMentionWP

open Miri.Interpreter Miri.MIR Miri.Memory RvalueWP Std.WP

variable {P S C E : Type}

/-- Expose the ordered index-local read and the validity flag used by deref.
Field projections continue through the canonical dynamic layout rules. -/
def projectPre [PointerProvenance P] (hooks : PlaceProjectionHooks P S C E)
    (choice : C) (base : RuntimePlace P) (element : ProjectionElem)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  match element with
  | .Deref => actionPre (hooks.place.deref choice base false) post onError
  | .Field field _ => actionPre (PlaceDynamic.field hooks choice base field) post onError
  | .Index localId =>
    actionPre (hooks.localIndex choice localId)
      (fun index => actionPre (PlaceDynamic.index hooks choice base index) post onError) onError
  | .OpaqueCast _ => onError (.invalidProgram "OpaqueCast after borrowck")
  | .PhantomDeref => onError (.invalidProgram "PhantomDeref after borrowck")
  | .Downcast _ variant => actionPre (PlaceDynamic.downcast hooks choice base variant) post onError
  | .ConstantIndex offset minimum fromEnd =>
    if offset >= 2^64 || minimum >= 2^64 then onError (.invalidProgram "MIR index exceeds u64")
    else actionPre (PlaceDynamic.constantIndex hooks choice base (UInt64.ofNat offset)
      (UInt64.ofNat minimum) fromEnd) post onError
  | .Subslice start stop fromEnd =>
    if start >= 2^64 || stop >= 2^64 then onError (.invalidProgram "MIR subslice exceeds u64")
    else actionPre (PlaceDynamic.subslice hooks choice base (UInt64.ofNat start)
      (UInt64.ofNat stop) fromEnd) post onError
  | .UnwrapUnsafeBinder ty =>
    actionPre (hooks.layoutOf choice ty) (fun layout =>
      if !base.layout.layout.isSized || !layout.layout.isSized ||
          base.layout.layout.size != layout.layout.size then
        onError (.invalidProgram "transmute requires equally sized layouts")
      else actionPre (PlaceDynamic.offsetWithMeta hooks choice base .ZERO .wrapping .none layout)
        post onError) onError

theorem actionPre_project [PointerProvenance P]
    (hooks : PlaceProjectionHooks P S C E) (choice : C) (base : RuntimePlace P)
    (element : ProjectionElem) (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.project hooks choice base element) post onError =
      projectPre hooks choice base element post onError := by
  cases element <;> try rfl
  case Index => exact actionPre_bind_fun _ _ _ _
  case UnwrapUnsafeBinder =>
    simp only [PlaceDynamic.project, projectPre, actionPre_bind_fun]
    congr 1
    funext layout
    split <;> rfl
  all_goals
    simp only [PlaceDynamic.project, projectPre]
    split <;> rfl

/-- Process the projection path from left to right, using the exact state
returned by each hook. An empty path proceeds directly to its finish check. -/
def projectionsPre [PointerProvenance P] (hooks : PlaceProjectionHooks P S C E)
    (choice : C) (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    List ProjectionElem → RuntimePlace P → S → Prop
  | [], base => post base
  | element :: rest, base =>
    projectPre hooks choice base element (projectionsPre hooks choice post onError rest) onError

private theorem actionPre_projections [PointerProvenance P] (hooks : PlaceProjectionHooks P S C E)
    (choice : C) (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop)
    (elements : List ProjectionElem) (base : RuntimePlace P) :
    actionPre (forIn elements base fun element place =>
      ForInStep.yield <$> PlaceDynamic.project hooks choice place element) post onError =
      projectionsPre hooks choice post onError elements base := by
  induction elements generalizing base with
  | nil => rfl
  | cons element rest ih =>
    simp only [List.forIn_cons, projectionsPre, ← actionPre_project, map_eq_pure_bind,
      bind_assoc, pure_bind, actionPre_bind_fun]
    congr 1
    funext next
    exact ih next

/-- A cached local layout is available from the current frame. Otherwise the
layout query runs first and the result is cached in the frame it leaves. -/
def localLayoutPre (hooks : PlaceHooks P S C E) (choice : C) (id : LocalId)
    (post : LocalLayout → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  actionPre hooks.getFrame (fun frame =>
    scalarCheckPre ((frame.getLocal id).mapError StepError.stack) (fun slot =>
      match slot.layout with
      | some layout => post layout
      | none => actionPre (hooks.resolveLayout choice id) (fun layout =>
        actionPre hooks.getFrame (fun current =>
          scalarCheckPre ((current.getOrCacheLocalLayout id layout).mapError StepError.stack)
            (fun (updated, cached) => actionPre (hooks.setFrame updated) (fun _ => post cached) onError)
            onError) onError) onError) onError) onError

theorem actionPre_placeLayoutOfLocal (hooks : PlaceHooks P S C E) (choice : C) (id : LocalId)
    (post : LocalLayout → S → Prop) (onError : StepError → S → Prop) :
    actionPre (placeLayoutOfLocal hooks choice id) post onError =
      localLayoutPre hooks choice id post onError := by
  simp only [placeLayoutOfLocal, localLayoutPre, actionPre_bind_fun]
  congr 1
  funext frame state
  cases frame.getLocal id with
  | error error => rfl
  | ok slot =>
    simp only [stackLift_ok, Except.mapError, scalarCheckPre, actionPre_pure]
    cases slot.layout with
    | some layout => rfl
    | none =>
      simp only [actionPre_bind_fun]
      congr 1
      funext layout
      congr 1
      funext current atState
      cases current.getOrCacheLocalLayout id layout with
      | error error => rfl
      | ok update =>
        rcases update with ⟨updated, cachedLayout⟩
        simp only [stackLift_ok, scalarCheckPre]
        rfl

/-- Sized locals yield a local reference without reading their operand. An
unsized local must have a live indirect operand with its metadata. -/
def localPre (hooks : PlaceHooks P S C E) (choice : C) (id : LocalId)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  localLayoutPre hooks choice id (fun layout =>
    if layout.layout.isSized then
      actionPre hooks.frameIndex (fun frame =>
        actionPre hooks.getFrame
          (fun current => post ⟨.local frame id none current.localsIdentity, layout⟩) onError) onError
    else
      actionPre hooks.getFrame (fun current =>
        scalarCheckPre ((current.getLocalOperand id).mapError StepError.stack) (fun
          | .indirect place => post ⟨.memory place, layout⟩
          | .immediate _ => onError (.invalidProgram "unsized local is immediate")) onError) onError)
    onError

theorem actionPre_localToPlace (hooks : PlaceHooks P S C E)
    (choice : C) (id : LocalId) (post : RuntimePlace P → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (localToPlace hooks choice id) post onError = localPre hooks choice id post onError := by
  simp only [localToPlace, localPre, ← actionPre_placeLayoutOfLocal, actionPre_bind_fun]
  congr 1
  funext layout
  split
  · simp only [actionPre_bind_fun] <;> rfl
  · simp only [actionPre_bind_fun]
    congr 1
    funext current state
    cases operand : current.getLocalOperand id with
    | error => rfl
    | ok value => cases value <;> rfl

/-- Resolve the local first, project without the simple-deref validity bypass,
and run the final place-type check before passing the result to the client. -/
def evalPre [PointerProvenance P] (hooks : PlaceProjectionHooks P S C E)
    (choice : C) (place : Place) (post : RuntimePlace P → S → Prop)
    (onError : StepError → S → Prop) : S → Prop :=
  localPre hooks.place choice place.localId
    (projectionsPre hooks choice
      (fun result => actionPre (hooks.place.checkPlaceType choice place result)
        (fun _ => post result) onError)
      onError place.projection.toList) onError

theorem actionPre_evalPlace [PointerProvenance P]
    (hooks : PlaceProjectionHooks P S C E) (choice : C) (place : Place)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.evalPlace hooks choice place false) post onError =
      evalPre hooks choice place post onError := by
  simp only [PlaceDynamic.evalPlace, evalPre, ← actionPre_localToPlace, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    ← Array.forIn_toList, actionPre_bind_fun]
  congr 1
  funext base
  change actionPre (forIn place.projection.toList base (fun element value => do
      return .yield (← PlaceDynamic.project hooks choice value element))) _ _ = _
  have step : (fun element (value : RuntimePlace P) => do
      return ForInStep.yield (← PlaceDynamic.project hooks choice value element)) =
      (fun element value => ForInStep.yield <$> PlaceDynamic.project hooks choice value element) := by
    funext element value
    exact (map_eq_pure_bind _ _).symm
  rw [step, actionPre_projections]
  congr 2

variable {K U O X Host : Type} [DecidableEq K]

/-- The selected canonical statement retains the driver check and advances
the statement index only after local resolution, projection and type check. -/
theorem canonical_statementPre
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (place : Place) (post : Bool → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) :
    CanonicalStepWP.statementPre config limits choice (.PlaceMention place) post onError before =
      evalPre (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
        choice place
        (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError)
        onError before := by
  simp only [CanonicalStepWP.statementPre, ← actionPre_eq_wp, actionPre_evalPlace]

/-- Reduce the selected place evaluation and its ordered projections. -/
macro "miri_place_mention_wp" : tactic =>
  `(tactic| simp only [canonical_statementPre, actionPre_evalPlace, actionPre_localToPlace,
    actionPre_placeLayoutOfLocal, actionPre_project, evalPre, localPre, localLayoutPre,
    projectionsPre, projectPre, FieldProjectionWP.actionPre_field, FieldProjectionWP.fieldPre,
    FieldProjectionWP.actionPre_offsetWithMeta, FieldProjectionWP.offsetPre])

end Miri.Verification.PlaceMentionWP

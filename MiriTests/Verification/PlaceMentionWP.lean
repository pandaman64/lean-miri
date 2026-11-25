import Miri.Verification.PlaceMentionWP

namespace MiriTests.Verification.PlaceMentionWP

open Miri.Interpreter Miri.MIR Miri.Memory Miri.Verification
open Miri.Verification.PlaceMentionWP Miri.Verification.RvalueWP

variable {K U C O X Host : Type} [DecidableEq K]

/-- A canonical empty projection still resolves the local and checks the
place type before the statement driver advances. -/
example (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (id : LocalId) (post : Bool → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) :
    let hooks := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
    let place : Place := ⟨id, #[]⟩
    Miri.Verification.CanonicalStepWP.statementPre config limits choice (.PlaceMention place)
      post onError before =
      localPre hooks.place choice id (fun result =>
        actionPre (hooks.place.checkPlaceType choice place result)
          (fun _ => InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError)
          onError) onError before := by
  simp only [canonical_statementPre, Miri.Verification.PlaceMentionWP.evalPre] <;> rfl

/-- A generated field projection uses the parent layout's static offset
before requesting the projected layout or performing the final type check. -/
example (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (id : LocalId) (ty : TyId) (parentLayout : LocalLayout)
    (post : Bool → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U)
    (offsetError : Miri.ABI.LayoutError) (sized : parentLayout.layout.isSized = true)
    (invalidOffset : parentLayout.layout.fields.offset 1 = .error offsetError)
    (frameIndex : Nat) (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (frameIndexFound : (ExecutionMachine.projectionHooks
      (ExecutionMachine.withValidation config limits)).place.frameIndex before = .ok frameIndex before)
    (frameFound : (ExecutionMachine.projectionHooks
      (ExecutionMachine.withValidation config limits)).place.getFrame before = .ok current before)
    (resolved : ∀ (cont : LocalLayout → MachineHooks.State K U → Prop),
      localLayoutPre (ExecutionMachine.projectionHooks
        (ExecutionMachine.withValidation config limits)).place choice id cont onError before =
        cont parentLayout before) :
    CanonicalStepWP.statementPre config limits choice (.PlaceMention ⟨id, #[.Field 1 ty]⟩)
      post onError before = onError (.invalidProgram s!"place layout: {repr offsetError}") before := by
  simp only [canonical_statementPre, Miri.Verification.PlaceMentionWP.evalPre, localPre, resolved,
    sized, ↓reduceIte]
  miri_place_mention_wp
  simp only [invalidOffset, Except.mapError, actionPre, frameIndexFound, frameFound, scalarCheckPre]

variable {P S E : Type} [PointerProvenance P]

/-- A missing local stops before any layout query, projection or finish check. -/
example (hooks : PlaceProjectionHooks P S C E) (choice : C) (place : Place)
    (frame : Frame P LocalLayout E) (before after : S) (error : StackError)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop)
    (current : hooks.place.getFrame before = .ok frame after)
    (missing : frame.getLocal place.localId = .error error) :
    actionPre (PlaceDynamic.evalPlace hooks choice place false) post onError before =
      onError (.stack error) after := by
  rw [actionPre_evalPlace]
  simp only [Miri.Verification.PlaceMentionWP.evalPre, localPre, localLayoutPre, actionPre, current, missing,
    Except.mapError, scalarCheckPre]

/-- A field and normal dereference run before the index-local read. Its
typed failure retains all prior state changes and stops the remaining path. -/
example (hooks : PlaceProjectionHooks P S C E) (choice : C) (base field pointee : RuntimePlace P)
    (ty : TyId) (index : LocalId) (before afterField afterDeref failed : S)
    (error : StepError) (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop)
    (fieldOK : PlaceDynamic.field hooks choice base 1 before = .ok field afterField)
    (derefOK : hooks.place.deref choice field false afterField = .ok pointee afterDeref)
    (indexFailed : hooks.localIndex choice index afterDeref = .error error failed) :
    projectionsPre hooks choice post onError [.Field 1 ty, .Deref, .Index index, .Deref]
      base before = onError error failed := by
  simp only [projectionsPre, projectPre, actionPre, fieldOK, derefOK, indexFailed]

/-- The index's typed bounds error follows a successful local index read. -/
example (hooks : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (id : LocalId) (before after : S)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop)
    (read : hooks.localIndex choice id before = .ok 4 after)
    (array : base.layout.layout.fields = .Array Miri.ABI.Size.ZERO 3)
    (sized : base.layout.layout.isSized = true) :
    projectPre hooks choice base (.Index id) post onError before =
      onError (.undefinedBehavior "place index 4 out of bounds for 3") after := by
  simp only [projectPre, actionPre, read, PlaceDynamic.index, PlaceDynamic.length, array, sized,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, Bind.bind, EStateM.bind, pure,
    Pure.pure, EStateM.pure] <;> rfl

/-- Oversized constant indices fail before the array or slice is inspected. -/
example (hooks : PlaceProjectionHooks P S C E) (choice : C) (base : RuntimePlace P)
    (before : S) (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.project hooks choice base (.ConstantIndex (2^64) 0 false))
      post onError before = onError (.invalidProgram "MIR index exceeds u64") before := by
  miri_place_mention_wp <;> rfl

/-- A local projection that exceeds its parent reports the error in the
state returned by the field layout query. -/
example (hooks : PlaceProjectionHooks P S C E) (choice : C)
    (frame localId : Nat) (identity : LocalsIdentity) (ty : TyId)
    (parent field : LocalLayout) (before queried : S)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop)
    (offset : Miri.ABI.Size) (offsetFound : parent.layout.fields.offset 1 = .ok offset)
    (fieldFound : hooks.field choice parent 1 before = .ok field queried)
    (sized : field.layout.isSized = true)
    (bound : Miri.ABI.Size) (boundAdded : offset.add field.layout.size = .ok bound)
    (outside : bound.bytes > parent.layout.size.bytes) :
    actionPre (PlaceDynamic.project hooks choice
      ⟨.local frame localId none identity, parent⟩ (.Field 1 ty)) post onError before =
      onError (.invalidProgram "local projection exceeds enclosing place") queried := by
  miri_place_mention_wp
  simp only [offsetFound, actionPre, Except.mapError, scalarCheckPre, fieldFound, sized,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, MemPlaceMeta.hasMeta, Bool.false_or,
    boundAdded, outside]

end MiriTests.Verification.PlaceMentionWP

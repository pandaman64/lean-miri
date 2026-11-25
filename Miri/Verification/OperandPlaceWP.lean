import Miri.Verification.InitialWPAttr
import Miri.Verification.PlaceMentionWP
import Miri.Verification.StorageLiveWP
import Miri.Input.CompilerScalarLeaves
import Miri.Interpreter.ConstantMachine

/-! Exact continuation rules for canonical operand reads and place projections. -/

namespace Miri.Verification.OperandPlaceWP

open Miri.ABI Miri.Interpreter Miri.Memory RvalueWP

variable {K U C P S E A : Type}
local notation "State" => MachineHooks.State K U
local notation "Errors" => StepError → State → Prop
local notation "Op" => OpTy Provenance

private theorem purePre (value : A) (post : A → S → Prop) (onError : StepError → S → Prop) :
    actionPre (pure value) post onError = post value := rfl

private theorem throwPre (error : StepError) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (throw error) post onError = onError error := rfl

private def checked (result : Except StepError A) : RvalueM S A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

private theorem checkedPre (result : Except StepError A) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (checked result) post onError = scalarCheckPre result post onError := by
  cases result <;> rfl

/-- A cache hit wins over any layout hint. On a miss, debug checking runs before
publishing the layout in the frame current after the compiler effects. An
immediate read signals the local race hook only outside validation. -/
def localOperandPre (h : OperandMachine.Hooks K U C) (choice : C)
    (id : MIR.LocalId) (known : Option LocalLayout) (post : Op → State → Prop)
    (onError : Errors) : State → Prop :=
  let read := fun layout =>
    StorageLiveWP.currentFramePre (fun frame =>
      scalarCheckPre ((frame.getLocalOperand id).mapError StepError.stack) (fun op =>
        match op with
        | .indirect _ => post ⟨op, layout⟩
        | .immediate _ =>
          if layout.layout.backendRepr.isUnsized then onError (.invalidProgram "unsized immediate local")
          else actionPre h.compiler.validationInProgress (fun validating =>
            if validating then post ⟨op, layout⟩
            else actionPre (MachineHooks.afterLocalRead id) (fun _ => post ⟨op, layout⟩) onError)
            onError) onError) onError
  let cache := fun layout =>
    StorageLiveWP.currentFramePre (fun frame =>
      scalarCheckPre ((frame.getOrCacheLocalLayout id layout).mapError StepError.stack)
        (fun pair => StorageLiveWP.setCurrentFramePre pair.1 (fun _ => read pair.2) onError)
        onError) onError
  StorageLiveWP.currentFramePre (fun frame =>
    scalarCheckPre ((frame.getLocal id).mapError StepError.stack) (fun slot =>
      match slot.layout with
      | some layout => read layout
      | none =>
        match known with
        | none => actionPre (h.compiler.layout choice id) cache onError
        | some hint =>
          if h.compiler.debugAssertions then
            actionPre (h.compiler.layout choice id) (fun computed =>
              scalarCheckPre (h.layoutCompatible computed hint) (fun compatible =>
                if compatible then cache hint
                else onError (.invalidProgram "known local layout differs from compiler layout")) onError)
              onError
          else cache hint) onError) onError

@[miri_initial_wp] theorem actionPre_localToOp (h : OperandMachine.Hooks K U C) (choice : C)
    (id : MIR.LocalId) (known : Option LocalLayout) (post : Op → State → Prop)
    (onError : Errors) :
    actionPre (OperandMachine.localToOp h choice id known) post onError =
      localOperandPre h choice id known post onError := by
  let read := fun (layout : LocalLayout) => do
    let frame ← (MachineHooks.currentFrame : MachineHooks.M K U _)
    let op ← checked ((frame.getLocalOperand id).mapError StepError.stack)
    if let .immediate _ := op then
      if layout.layout.backendRepr.isUnsized then throw (StepError.invalidProgram "unsized immediate local")
      unless ← h.compiler.validationInProgress do MachineHooks.afterLocalRead id
    return (⟨op, layout⟩ : Op)
  have readPre (layout : LocalLayout) : actionPre (read layout) post onError =
      StorageLiveWP.currentFramePre (fun frame =>
        scalarCheckPre ((frame.getLocalOperand id).mapError StepError.stack) (fun op =>
          match op with
          | .indirect _ => post ⟨op, layout⟩
          | .immediate _ =>
            if layout.layout.backendRepr.isUnsized then onError (.invalidProgram "unsized immediate local")
            else actionPre h.compiler.validationInProgress (fun validating =>
              if validating then post ⟨op, layout⟩
              else actionPre (MachineHooks.afterLocalRead id) (fun _ => post ⟨op, layout⟩) onError)
              onError) onError) onError := by
    simp only [read, actionPre_bind_fun, StorageLiveWP.actionPre_currentFrame, checkedPre]
    congr 1
    funext frame state
    cases frame.getLocalOperand id with
    | error => rfl
    | ok op =>
      cases op with
      | indirect => rfl
      | immediate =>
        simp only [Except.mapError, scalarCheckPre, actionPre_ite, actionPre_bind_fun]
        split
        · rfl
        · congr 1
  let cache := fun layout => do
    let frame ← (MachineHooks.currentFrame : MachineHooks.M K U _)
    let (frame, layout) ← checked ((frame.getOrCacheLocalLayout id layout).mapError StepError.stack)
    MachineHooks.setCurrentFrame frame
    read layout
  have cachePre (layout : LocalLayout) : actionPre (cache layout) post onError =
      StorageLiveWP.currentFramePre (fun frame =>
        scalarCheckPre ((frame.getOrCacheLocalLayout id layout).mapError StepError.stack)
          (fun pair => StorageLiveWP.setCurrentFramePre pair.1
            (fun _ => actionPre (read pair.2) post onError) onError) onError) onError := by
    simp only [cache, actionPre_bind_fun, StorageLiveWP.actionPre_currentFrame, checkedPre]
    congr 1
    funext frame state
    cases frame.getOrCacheLocalLayout id layout with
    | error => rfl
    | ok update =>
      rcases update with ⟨updated, cached⟩
      simp only [Except.mapError, scalarCheckPre, StorageLiveWP.actionPre_setCurrentFrame]
  unfold OperandMachine.localToOp localOperandPre
  simp only [actionPre_bind_fun, StorageLiveWP.actionPre_currentFrame]
  congr 1
  funext frame state
  cases frame.getLocal id with
  | error => rfl
  | ok slot =>
    change actionPre (pure slot) _ onError state = _
    simp only [purePre, Except.mapError, scalarCheckPre]
    cases slotLayout : slot.layout with
    | some layout =>
      change actionPre ((pure layout : MachineHooks.M K U LocalLayout) >>= read) post onError state = _
      simp only [pure_bind, readPre] <;> rfl
    | none =>
      cases known with
      | none =>
        change actionPre (h.compiler.layout choice id >>= cache) post onError state = _
        simp only [actionPre_bind_fun, cachePre, readPre] <;> rfl
      | some hint =>
        cases h.compiler.debugAssertions
        · change actionPre _ post onError state = _
          simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
          change actionPre (cache hint) post onError state = _
          simp only [cachePre, readPre] <;> rfl
        · simp only [↓reduceIte, pure_bind, actionPre_bind_fun]
          congr 1
          funext computed after
          cases compatible : h.layoutCompatible computed hint with
          | error => rfl
          | ok accepted =>
            cases accepted
            · rfl
            · change actionPre (cache hint) post onError after = _
              simp only [cachePre, readPre]
              rfl

/-- Preserve the interpreter's precise error classification for immediate
projections after the compiler has supplied the projection context. -/
private def mapProjectionError (result : Except ProjectionError A) : Except StepError A :=
  result.mapError fun error => match error with
    | .machineError error => error
    | .bounds length index => .undefinedBehavior s!"index out of bounds: {index} >= {length}"
    | .pointerArithOverflow => .undefinedBehavior "pointer arithmetic overflow"
    | .scalar error => ScalarOps.scalarError error
    | .immediate error => ScalarOps.immediateError error
    | .obligation message => .unsupported message
    | other => .invalidProgram s!"operand projection: {reprStr other}"

def projectionCheckPre (result : Except ProjectionError A) (post : A → S → Prop)
    (onError : StepError → S → Prop) : S → Prop :=
  scalarCheckPre (mapProjectionError result) post onError

@[miri_initial_wp] theorem actionPre_operandField (h : OperandMachine.Hooks K U C) (choice : C)
    (base : Op) (index : Nat) (post : Op → State → Prop) (onError : Errors) :
    actionPre (OperandMachine.field h choice base index) post onError =
      match base.op with
      | .immediate _ => actionPre (h.compiler.projection choice)
        (fun context => projectionCheckPre (projectField context base index) post onError) onError
      | .indirect memory => FieldProjectionWP.fieldPre h.projection choice ⟨.memory memory, base.layout⟩ index
        (fun projected => match projected.ref with
          | .memory memory => post ⟨.indirect memory, projected.layout⟩
          | .local .. => onError (.invalidProgram "indirect field projection became local")) onError := by
  unfold OperandMachine.field
  cases base.op with
  | immediate value =>
    rw [actionPre_bind_fun]
    congr 1
    funext context
    cases projectField context base index <;> rfl
  | indirect memory =>
    rw [actionPre_bind_fun, FieldProjectionWP.actionPre_field]
    congr 1
    funext projected
    cases projected.ref <;> rfl

def operandProjectionPre (h : OperandMachine.Hooks K U C) (choice : C)
    (base : Op) (elem : MIR.ProjectionElem) (post : Op → State → Prop) (onError : Errors) :
    State → Prop :=
  match elem with
  | .Field index _ => actionPre (OperandMachine.field h choice base index) post onError
  | .Deref => actionPre (h.dereference choice base) (fun place =>
      post ⟨.indirect place.mplace, place.layout⟩) onError
  | elem =>
    match base.op with
    | .indirect memory =>
      PlaceMentionWP.projectPre h.projection choice ⟨.memory memory, base.layout⟩ elem
        (fun next => match next.ref with
          | .memory memory => post ⟨.indirect memory, next.layout⟩
          | .local .. => onError (.invalidProgram "indirect projection became local")) onError
    | .immediate _ =>
      actionPre (h.compiler.projection choice) (fun context =>
        match elem with
        | .Subslice start stop fromEnd =>
          if start >= 2^64 || stop >= 2^64 then onError (.invalidProgram "MIR subslice exceeds u64")
          else projectionCheckPre
            (prepareSubslice context base (UInt64.ofNat start) (UInt64.ofNat stop) fromEnd)
            (fun range => actionPre (h.projection.subsliceLayout choice base.layout range.2)
              (fun layout => projectionCheckPre
                (base.offsetWithMeta context range.1 .inbounds layout.2 layout.1) post onError) onError)
            onError
        | .Index id => actionPre (h.projection.localIndex choice id)
          (fun index => projectionCheckPre (projectIndex context base index) post onError) onError
        | _ => projectionCheckPre (Miri.Interpreter.project context base elem) post onError)
        onError

@[miri_initial_wp] theorem actionPre_operandProject (h : OperandMachine.Hooks K U C) (choice : C)
    (base : Op) (elem : MIR.ProjectionElem) (post : Op → State → Prop) (onError : Errors) :
    actionPre (OperandMachine.project h choice base elem) post onError =
      operandProjectionPre h choice base elem post onError := by
  unfold OperandMachine.project operandProjectionPre
  cases elem
  case Deref => exact actionPre_bind_fun _ _ _ _
  case Field => rfl
  all_goals
    dsimp only
    simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte]
    cases base.op with
    | indirect memory =>
      rw [actionPre_bind_fun, PlaceMentionWP.actionPre_project]
      congr 1
      funext next
      cases next.ref <;> rfl
    | immediate value =>
      rw [actionPre_bind_fun]
      congr 1 <;> funext context
      all_goals first
      | apply checkedPre
      | rw [actionPre_bind_fun]
        congr 1
        funext index
        apply checkedPre
      | rename_i start stop fromEnd
        rw [actionPre_ite]
        split
        · rfl
        · generalize prepareSubslice context base (UInt64.ofNat start) (UInt64.ofNat stop) fromEnd = result
          cases result with
          | error => rfl
          | ok range =>
            rcases range with ⟨offset, amount⟩
            simp only [projectionCheckPre, mapProjectionError, Except.mapError, actionPre_bind_fun]
            change actionPre (pure (offset, amount) : MachineHooks.M K U _) _ _ = _
            rw [purePre]
            congr 1
            funext layout
            rcases layout with ⟨layout, metadata⟩
            apply checkedPre

/-- Iterate operand projections in MIR order and check the assembled type.
Copy and move use this same rule without modifying the source local. -/
def operandProjectionsPre (h : OperandMachine.Hooks K U C) (choice : C)
    (post : Op → State → Prop) (onError : Errors) :
    List MIR.ProjectionElem → Op → State → Prop
  | [], base => post base
  | element :: rest, base =>
    operandProjectionPre h choice base element
      (operandProjectionsPre h choice post onError rest) onError

private theorem actionPre_operandProjections (h : OperandMachine.Hooks K U C) (choice : C)
    (elements : List MIR.ProjectionElem) (base : Op) (post : Op → State → Prop) (onError : Errors) :
    actionPre (forIn elements base fun element current =>
      ForInStep.yield <$> OperandMachine.project h choice current element) post onError =
      operandProjectionsPre h choice post onError elements base := by
  induction elements generalizing base with
  | nil => rfl
  | cons element rest ih =>
    simp only [List.forIn_cons, operandProjectionsPre, ← actionPre_operandProject, map_eq_pure_bind, bind_assoc,
      pure_bind, actionPre_bind_fun]
    congr 1
    funext next
    exact ih next

@[miri_initial_wp] theorem actionPre_evalPlaceToOp (h : OperandMachine.Hooks K U C) (choice : C)
    (place : MIR.Place) (known : Option LocalLayout) (post : Op → State → Prop) (onError : Errors) :
    actionPre (OperandMachine.evalPlaceToOp h choice place known) post onError =
      localOperandPre h choice place.localId (if place.projection.isEmpty then known else none)
        (operandProjectionsPre h choice (fun result =>
          actionPre (h.checkPlaceType choice place result) (fun _ => post result) onError)
          onError place.projection.toList) onError := by
  simp only [OperandMachine.evalPlaceToOp, ← Array.forIn_toList, actionPre_bind_fun, actionPre_localToOp]
  congr 1
  funext base
  change actionPre (forIn place.projection.toList base
    (fun element current => do return .yield (← OperandMachine.project h choice current element))) _ _ = _
  have step : (fun element current => do
      return ForInStep.yield (← OperandMachine.project h choice current element)) =
      (fun element current => ForInStep.yield <$> OperandMachine.project h choice current element) := by
    funext element current
    exact (map_eq_pure_bind _ _).symm
  rw [step, actionPre_operandProjections]
  congr 2

@[miri_initial_wp] theorem actionPre_evalOperand (h : OperandMachine.Hooks K U C) (choice : C)
    (operand : MIR.Operand) (known : Option LocalLayout) (post : Op → State → Prop) (onError : Errors) :
    actionPre (OperandMachine.evalOperand h choice operand known) post onError =
      match operand with
      | .Copy place | .Move place => actionPre (OperandMachine.evalPlaceToOp h choice place known) post onError
      | .Constant value => actionPre (h.constant choice value known) post onError
      | .RuntimeChecks checks => actionPre (h.runtimeChecks choice checks) (fun value =>
        actionPre (h.boolLayout choice) (fun layout =>
          post ⟨.immediate (.scalar (.fromBool value)), layout⟩) onError) onError := by
  cases operand <;> simp only [OperandMachine.evalOperand, actionPre_bind_fun, purePre]

/-- Bare destination places use the same ordered projections as place mentions.
A sole dereference can bypass the final type check on the source's explicit
skip-validity path. -/
@[miri_initial_wp] theorem actionPre_evalPlace [PointerProvenance P] (h : PlaceProjectionHooks P S C E)
    (choice : C) (place : MIR.Place) (skipValidity : Bool) (post : RuntimePlace P → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.evalPlace h choice place skipValidity) post onError =
      if skipValidity && place.projection == #[.Deref] then
        PlaceMentionWP.localPre h.place choice place.localId
          (fun base => actionPre (h.place.deref choice base true) post onError) onError
      else PlaceMentionWP.evalPre h choice place post onError := by
  by_cases bypass : (skipValidity && place.projection == #[.Deref]) = true
  · simp only [PlaceDynamic.evalPlace, bypass, ↓reduceIte, actionPre_bind_fun,
      PlaceMentionWP.actionPre_localToPlace]
  · rw [← PlaceMentionWP.actionPre_evalPlace]
    simp only [PlaceDynamic.evalPlace, bypass, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- A source immediate with race tracking checks for a global clock, then
commits both clocks before classifying the race outcome. -/
@[miri_initial_wp] theorem actionPre_afterLocalRead (id : MIR.LocalId) (post : Unit → State → Prop) (onError : Errors) :
    actionPre (MachineHooks.afterLocalRead id) post onError =
      StorageLiveWP.currentFramePre (fun frame before =>
        match frame.extra.dataRace with
        | none => post () before
        | some clocks =>
          match before.machine.dataRace with
          | none => onError (.invalidProgram "frame has vector clocks but machine does not") before
          | some global =>
            let result := Miri.Concurrency.LocalRace.localRead clocks global before.machine.threads id
            let state := { before with machine.dataRace := some result.global }
            StorageLiveWP.setCurrentFramePre
              { frame with extra.dataRace := some result.frame }
              (fun _ => match result.outcome with
                | .ok () => post ()
                | .error error => onError (.callback s!"after_local_read: {reprStr error}"))
              onError state) onError := by
  funext before
  rw [MachineHooks.afterLocalRead, actionPre_bind_fun, StorageLiveWP.actionPre_currentFrame]
  unfold StorageLiveWP.currentFramePre
  cases before.stack.currentFrame? with
  | none => rfl
  | some frame =>
    dsimp only
    cases frame.extra.dataRace with
    | none => rfl
    | some clocks =>
      simp only [actionPre_bind_fun]
      let require : MachineHooks.M K U _ :=
        match before.machine.dataRace with
        | none => throw (.invalidProgram "frame has vector clocks but machine does not")
        | some global => pure global
      change actionPre require _ onError before = _
      cases globalClocks : before.machine.dataRace with
      | none => simp only [require, globalClocks, throwPre]
      | some global =>
        simp only [require, globalClocks, purePre]
        let result := Miri.Concurrency.LocalRace.localRead clocks global before.machine.threads id
        let updated := {before with machine.dataRace := some result.global}
        change actionPre (MachineHooks.setCurrentFrame _) _ onError updated = _
        rw [StorageLiveWP.actionPre_setCurrentFrame]
        congr 2
        funext _
        cases result.outcome with
        | ok unitValue => cases unitValue; rfl
        | error => rfl

@[miri_initial_wp] theorem actionPre_placeLength [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (post : UInt64 → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.length h choice base) post onError =
      if !base.layout.layout.isSized then
        actionPre (h.isSliceOrStr choice base.layout.ty) (fun slice =>
          if slice then
            let metadata : MemPlaceMeta P := match base.ref with
              | .local .. => .none
              | .memory memory => memory.metadata
            scalarCheckPre (metadata.unwrapMeta.mapError fun error => .invalidProgram (reprStr error))
              (fun scalar => scalarCheckPre
                ((scalar.toTargetUsize (Size.fromBits h.target.pointerWidth.bits)).mapError ScalarOps.scalarError)
                post onError) onError
          else onError (.invalidProgram "length of unsized non-slice")) onError
      else match base.layout.layout.fields with
        | .Array _ count => post count
        | _ => onError (.invalidProgram "length of non-array") := by
  rw [PlaceDynamic.length, actionPre_ite]
  split
  · simp only [actionPre_bind_fun]
    congr 1
    funext slice
    cases slice
    · rfl
    · let metadata : MemPlaceMeta P := match base.ref with
              | .local .. => .none
              | .memory memory => memory.metadata
      change actionPre (checked (metadata.unwrapMeta.mapError fun error => .invalidProgram (reprStr error)) >>= _) _ _ = _
      rw [actionPre_bind_fun, checkedPre]
      congr 1
      funext scalar
      apply checkedPre
  · cases base.layout.layout.fields <;> rfl

@[miri_initial_wp] theorem actionPre_placeDowncast (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (variant : Nat) (post : RuntimePlace P → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.downcast h choice base variant) post onError =
      let metadata : MemPlaceMeta P := match base.ref with
              | .local .. => .none
              | .memory memory => memory.metadata
      if metadata.hasMeta then onError (.invalidProgram "downcast requires thin place")
      else actionPre (h.variant choice base.layout variant) (fun layout =>
        if !layout.layout.isSized then onError (.invalidProgram "sized offset requires sized output")
        else FieldProjectionWP.offsetPre h choice base .ZERO .inbounds .none layout post onError) onError := by
  let metadata : MemPlaceMeta P := match base.ref with
    | .local .. => .none
    | .memory memory => memory.metadata
  rw [PlaceDynamic.downcast, actionPre_ite]
  change (if metadata.hasMeta then _ else _) = (if metadata.hasMeta then _ else _)
  split
  · rfl
  · rw [actionPre_bind_fun]
    congr 1
    funext layout
    change actionPre (if !layout.layout.isSized then throw (.invalidProgram "sized offset requires sized output")
      else PlaceDynamic.offsetWithMeta h choice base .ZERO .inbounds .none layout) post onError = _
    rw [actionPre_ite]
    split
    · rfl
    · exact FieldProjectionWP.actionPre_offsetWithMeta _ _ _ _ _ _ _ _ _

@[miri_initial_wp] theorem actionPre_placeIndex [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (index : UInt64) (post : RuntimePlace P → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.index h choice base index) post onError =
      match base.layout.layout.fields with
      | .Array stride _ =>
        actionPre (PlaceDynamic.length h choice base) (fun length =>
          if index >= length then onError (.undefinedBehavior s!"place index {index} out of bounds for {length}")
          else match IntegerOps.computeSizeInBytes stride index h.maxSizeOfVal with
            | none => onError (.undefinedBehavior "PointerArithOverflow")
            | some offset => actionPre (h.field choice base.layout 0) (fun layout =>
              if !layout.layout.isSized then onError (.invalidProgram "sized offset requires sized output")
              else FieldProjectionWP.offsetPre h choice base offset .inbounds .none layout post onError) onError)
          onError
      | _ => onError (.invalidProgram "index on non-array") := by
  rw [PlaceDynamic.index]
  cases base.layout.layout.fields <;> try rfl
  rename_i stride _
  simp only [actionPre_bind_fun]
  congr 1
  funext length
  rw [actionPre_ite]
  split
  · rfl
  · cases IntegerOps.computeSizeInBytes stride index h.maxSizeOfVal with
    | none => rfl
    | some offset =>
      rw [actionPre_bind_fun]
      congr 1
      funext layout
      change actionPre (if !layout.layout.isSized then throw (.invalidProgram "sized offset requires sized output")
        else PlaceDynamic.offsetWithMeta h choice base offset .inbounds .none layout) post onError = _
      rw [actionPre_ite]
      split
      · rfl
      · exact FieldProjectionWP.actionPre_offsetWithMeta _ _ _ _ _ _ _ _ _

@[miri_initial_wp] theorem actionPre_placeConstantIndex [PointerProvenance P] (h : PlaceProjectionHooks P S C E)
    (choice : C) (base : RuntimePlace P) (offset minimum : UInt64) (fromEnd : Bool)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.constantIndex h choice base offset minimum fromEnd) post onError =
      actionPre (PlaceDynamic.length h choice base) (fun length =>
        if length < minimum then onError (.undefinedBehavior "constant index minimum length")
        else if fromEnd then
          if offset == 0 || offset > minimum then onError (.invalidProgram "invalid from-end constant index")
          else actionPre (PlaceDynamic.index h choice base (length - offset)) post onError
        else if offset >= minimum then onError (.invalidProgram "invalid constant index")
        else actionPre (PlaceDynamic.index h choice base offset) post onError) onError := by
  rw [PlaceDynamic.constantIndex, actionPre_bind_fun]
  congr 1
  funext length
  rw [actionPre_ite]
  split
  · rfl
  · cases fromEnd <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_ite]
    all_goals split <;> rfl

@[miri_initial_wp] theorem actionPre_placeSubslice [PointerProvenance P] (h : PlaceProjectionHooks P S C E)
    (choice : C) (base : RuntimePlace P) (start stop : UInt64) (fromEnd : Bool)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.subslice h choice base start stop fromEnd) post onError =
      actionPre (PlaceDynamic.length h choice base) (fun length =>
        let finish := fun actualStop => match base.layout.layout.fields with
          | .Array stride _ => scalarCheckPre ((stride.mul start).mapError
              fun error => .invalidProgram s!"place size: {repr error}") (fun offset =>
              if actualStop < start then onError (.invalidProgram "subslice length underflow")
              else actionPre (h.subsliceLayout choice base.layout (actualStop - start)) (fun layout =>
                FieldProjectionWP.offsetPre h choice base offset .inbounds layout.2 layout.1 post onError) onError)
              onError
          | _ => onError (.invalidProgram "subslice on non-array")
        if fromEnd then
          if start.toNat + stop.toNat >= 2^64 || start.toNat + stop.toNat > length.toNat then
            onError (.undefinedBehavior "subslice bounds")
          else finish (length - stop)
        else finish stop) onError := by
  rw [PlaceDynamic.subslice, actionPre_bind_fun]
  congr 1
  funext length
  have finish (actualStop : UInt64) :
      actionPre (do
        let offset ← match base.layout.layout.fields with
          | .Array stride _ => checked ((stride.mul start).mapError
              fun error => .invalidProgram s!"place size: {repr error}")
          | _ => throw (.invalidProgram "subslice on non-array")
        if actualStop < start then throw (.invalidProgram "subslice length underflow")
        let (layout, metadata) ← h.subsliceLayout choice base.layout (actualStop - start)
        PlaceDynamic.offsetWithMeta h choice base offset .inbounds metadata layout) post onError =
      (match base.layout.layout.fields with
      | .Array stride _ => scalarCheckPre ((stride.mul start).mapError
          fun error => .invalidProgram s!"place size: {repr error}") (fun offset =>
          if actualStop < start then onError (.invalidProgram "subslice length underflow")
          else actionPre (h.subsliceLayout choice base.layout (actualStop - start)) (fun layout =>
            FieldProjectionWP.offsetPre h choice base offset .inbounds layout.2 layout.1 post onError) onError)
          onError
      | _ => onError (.invalidProgram "subslice on non-array")) := by
    cases base.layout.layout.fields <;> try rfl
    rw [actionPre_bind_fun, checkedPre]
    congr 1
    funext offset
    rw [actionPre_ite]
    split
    · rfl
    · rw [actionPre_bind_fun]
      congr 1
      funext layout
      exact FieldProjectionWP.actionPre_offsetWithMeta _ _ _ _ _ _ _ _ _
  cases fromEnd <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, actionPre_ite]
  · exact finish stop
  · split
    · rfl
    · exact finish (length - stop)

attribute [miri_initial_wp] localOperandPre operandProjectionPre operandProjectionsPre
  projectionCheckPre PlaceMentionWP.evalPre PlaceMentionWP.localPre PlaceMentionWP.localLayoutPre
  PlaceMentionWP.actionPre_project PlaceMentionWP.projectPre PlaceMentionWP.projectionsPre
  FieldProjectionWP.actionPre_field FieldProjectionWP.actionPre_offsetWithMeta
  FieldProjectionWP.fieldPre FieldProjectionWP.offsetPre
  StorageLiveWP.actionPre_currentFrame StorageLiveWP.actionPre_setCurrentFrame
  StorageLiveWP.currentFramePre StorageLiveWP.setCurrentFramePre
  EffectSpecs.canonical_rvalue_place EffectSpecs.canonical_rvalue_operand
  EffectSpecs.canonical_rvalue_placeToOp

variable {O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host

@[miri_initial_wp] theorem canonical_aggregateOperand (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (operand : MIR.Operand) (known : Option LocalLayout) :
    (ExecutionMachine.aggregateHooks config limits).evalOperand choice operand known =
      OperandMachine.evalOperand
        (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
        choice operand known := rfl

@[miri_initial_wp] theorem actionPre_canonicalOperandType (config : Config)
    (choice : C) (place : MIR.Place) (op : Op) (post : Unit → State → Prop) (onError : Errors) :
    actionPre ((ExecutionMachine.operandHooks config).checkPlaceType choice place op) post onError =
      if config.compiler.debugAssertions then
        actionPre (config.operands.checkPlaceType choice place op) post onError
      else post () := by
  change actionPre (if config.compiler.debugAssertions then _ else _) post onError = _
  rw [actionPre_ite]
  split <;> rfl

@[miri_initial_wp] theorem actionPre_compilerRuntimeChecks (prepared : Input.CompilerProviders.Prepared)
    (choice : C) (kind : MIR.RuntimeChecks)
    (post : Bool → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre (Input.CompilerScalarLeaves.runtimeChecks prepared choice kind) post onError =
      scalarCheckPre ((Input.CompilerIntrinsicFacts.runtimeChecks prepared.intrinsics kind).mapError StepError.unsupported)
        post onError := by
  unfold Input.CompilerScalarLeaves.runtimeChecks
  cases Input.CompilerIntrinsicFacts.runtimeChecks prepared.intrinsics kind <;> rfl

@[miri_initial_wp] theorem actionPre_compilerBoolLayout (prepared : Input.CompilerProviders.Prepared)
    (choice : C) (post : LocalLayout → S → Prop) (onError : StepError → S → Prop) :
    actionPre (Input.CompilerScalarLeaves.boolLayout prepared choice) post onError =
      scalarCheckPre ((prepared.primitiveLayout "bool").mapError StepError.unsupported) post onError := by
  unfold Input.CompilerScalarLeaves.boolLayout
  cases prepared.primitiveLayout "bool" <;> rfl

@[miri_initial_wp] theorem canonical_runtimeChecks (config : Config) (choice : C)
    (kind : MIR.RuntimeChecks) :
    (ExecutionMachine.operandHooks config).runtimeChecks choice kind =
      config.operands.runtimeChecks choice kind := rfl

@[miri_initial_wp] theorem canonical_boolLayout (config : Config) (choice : C) :
    (ExecutionMachine.operandHooks config).boolLayout choice = config.operands.boolLayout choice := rfl

@[miri_initial_wp] theorem canonical_constant (config : Config) (choice : C)
    (constant : MIR.ConstOperand) (known : Option LocalLayout) :
    (ExecutionMachine.operandHooks config).constant choice constant known =
      config.operands.constant choice constant known := rfl

omit [DecidableEq K] in
@[miri_initial_wp] theorem actionPre_constantOperand (runtime : Input.RuntimeMetadata)
    (functions : FunctionPointers.Hooks K U O) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError) (constant : MIR.ConstOperand) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K U Bool))
    (post : Op → State → Prop) (onError : Errors) :
    actionPre (ConstantMachine.evalOperandWithLayout runtime functions arithmetic externStatic classify
      constant known checkKnown) post onError =
      match constant.value with
      | .Val value ty => actionPre
        (ConstantMachine.evalValueWithLayout runtime functions arithmetic externStatic classify
          value ty known checkKnown) post onError := by
  unfold ConstantMachine.evalOperandWithLayout
  cases constant.value <;> rfl

end Miri.Verification.OperandPlaceWP

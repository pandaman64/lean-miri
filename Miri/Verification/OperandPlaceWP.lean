import Miri.Verification.InitialWPAttr
import Miri.Verification.PlaceMentionWP
import Miri.Verification.StorageLiveWP
import Miri.Input.CompilerScalarLeaves
import Miri.Interpreter.ConstantMachine
import Miri.Input.EvalPlaceConstruction
import Miri.Verification.PlaceReadWriteWP

/-! Exact continuation rules for canonical operand reads and place projections.

A generated row polymorphic in `ExecutionMachine.Config` preserves that
configuration's dereference implementation. The production rules below expose
operand decoding, pointee construction, and validity when a client uses the
source configuration. Compiler layout, vtable, and memory policy queries
keep their own success and error continuations.
-/

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

@[miri_initial_wp high] theorem actionPre_evalPlaceToOpLocal (h : OperandMachine.Hooks K U C)
    (choice : C) (id : MIR.LocalId) (known : Option LocalLayout) (post : Op → State → Prop)
    (onError : Errors) :
    actionPre (OperandMachine.evalPlaceToOp h choice ⟨id, #[]⟩ known) post onError =
      localOperandPre h choice id known (fun result =>
        actionPre (h.checkPlaceType choice ⟨id, #[]⟩ result) (fun _ => post result) onError) onError := by
  rw [actionPre_evalPlaceToOp]
  rfl

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

/-- Resolve a bare local directly. The simple-dereference guard cannot
apply to an empty projection, so emitting a second continuation is redundant. -/
@[miri_initial_wp high] theorem actionPre_evalPlaceLocal [PointerProvenance P]
    (h : PlaceProjectionHooks P S C E) (choice : C) (id : MIR.LocalId) (skipValidity : Bool)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.evalPlace h choice ⟨id, #[]⟩ skipValidity) post onError =
      PlaceMentionWP.localPre h.place choice id (fun place =>
        actionPre (h.place.checkPlaceType choice ⟨id, #[]⟩ place)
          (fun _ => post place) onError) onError := by
  rw [actionPre_evalPlace]
  have notDeref : ((#[] : Array MIR.ProjectionElem) == #[.Deref]) = false := by decide
  cases skipValidity <;> simp only [notDeref, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte] <;> rfl

@[miri_initial_wp high] theorem actionPre_evalPlaceSimpleDeref [PointerProvenance P]
    (h : PlaceProjectionHooks P S C E) (choice : C) (id : MIR.LocalId)
    (post : RuntimePlace P → S → Prop) (onError : StepError → S → Prop) :
    actionPre (PlaceDynamic.evalPlace h choice ⟨id, #[.Deref]⟩ true) post onError =
      PlaceMentionWP.localPre h.place choice id
        (fun base => actionPre (h.place.deref choice base true) post onError) onError := by
  rw [actionPre_evalPlace]
  have deref : (true && (#[.Deref] : Array MIR.ProjectionElem) == #[.Deref]) = true := by decide
  simp only [deref, ↓reduceIte]

/-- A local race check commits the global and frame clocks before branching
on its result. Keep this transfer named in generated continuations so each
operand cache branch can share it. -/
def localReadClockPre (id : MIR.LocalId) (post : Unit → State → Prop) (onError : Errors) :
    State → Prop :=
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
          onError state) onError

@[miri_initial_wp] theorem actionPre_afterLocalRead (id : MIR.LocalId)
    (post : Unit → State → Prop) (onError : Errors) :
    actionPre (MachineHooks.afterLocalRead id) post onError =
      localReadClockPre id post onError := by
  funext before
  rw [MachineHooks.afterLocalRead, actionPre_bind_fun, StorageLiveWP.actionPre_currentFrame]
  unfold localReadClockPre StorageLiveWP.currentFramePre
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
        | ok unitValue => cases unitValue
                          rfl
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

section PointerProjection

variable {F T : Type}
local notation "DState" => ValidityMachine.State K U
local notation "DAccess" => ValidityMachine.Access K U
local notation "MPlace" => MPlaceTy Provenance

@[miri_initial_wp] theorem actionPre_validationInProgress (post : Bool → DState → Prop)
    (onError : StepError → DState → Prop) :
    actionPre ValidityMachine.validationInProgress post onError =
      fun state => post state.machine.user.payload.ghost state := rfl

@[miri_initial_wp] theorem actionPre_enforceValidity (post : Bool → DState → Prop)
    (onError : StepError → DState → Prop) :
    actionPre ValidityMachine.enforceValidity post onError =
      fun state => post (state.machine.user.payload.validation != .No) state := rfl

@[miri_initial_wp] theorem actionPre_scopedRead [DecidableEq K] (access : DAccess)
    (source : Op) (post : RvalueImmTy Provenance → DState → Prop)
    (onError : StepError → DState → Prop) :
    actionPre (ValidityMachine.readImmediate access source) post onError =
      fun state => actionPre (PlaceMachine.readImmediate
        {access with ghostMode := state.machine.user.payload.ghost} source) post onError state := rfl

@[miri_initial_wp] theorem actionPre_scalarMayBeNull (value : Scalar Provenance)
    (post : Bool → DState → Prop) (onError : StepError → DState → Prop) :
    actionPre (ValidityMachine.scalarMayBeNull value) post onError =
      match value.tryToScalarInt with
      | .ok (.integer integer) => post integer.isNull
      | .ok (.erasedPointer ..) => onError (.invalidProgram "absolute Miri pointer erased its address")
      | .error error => onError (ScalarOps.scalarError error) := by
  unfold ValidityMachine.scalarMayBeNull
  cases value.tryToScalarInt with
  | error => rfl
  | ok scalar => cases scalar <;> rfl

/-- The source alignment policy and one-byte ABI alignment both bypass
pointer resolution at place construction. -/
@[miri_initial_wp] theorem actionPre_misalignmentSkip (access : DAccess)
    (pointer : Pointer (Option Provenance)) (required : Align)
    (post : Option Misalignment → DState → Prop) (onError : StepError → DState → Prop)
    (before : DState)
    (skip : (before.machine.user.payload.alignment == .None || required.pow2 == 0) = true) :
    actionPre (PointerPlaceMachine.misalignment access pointer required) post onError before =
      post none before := by
  unfold PointerPlaceMachine.misalignment PointerPlaceMachine.misalignmentWith
  change actionPre (if (before.machine.user.payload.alignment == .None || required.pow2 == 0) = true
    then pure none else _) post onError before = _
  simp only [skip, ↓reduceIte]
  rfl

@[miri_initial_wp] theorem actionPre_pointerWithMetadata (access : DAccess)
    (pointer : Pointer (Option Provenance)) (metadata : MemPlaceMeta Provenance)
    (layout : LocalLayout) (unaligned : Bool) (post : MPlace → DState → Prop)
    (onError : StepError → DState → Prop) :
    actionPre (PointerPlaceMachine.withMetadata access pointer metadata layout unaligned) post onError =
      if unaligned then post ⟨⟨pointer, metadata, none⟩, layout⟩
      else actionPre (PointerPlaceMachine.misalignment access pointer layout.layout.align.abi)
        (fun mismatch => post ⟨⟨pointer, metadata, mismatch⟩, layout⟩) onError := by
  cases unaligned <;> simp only [PointerPlaceMachine.withMetadata, Bool.false_eq_true, ↓reduceIte,
    actionPre_bind_fun, purePre]

@[miri_initial_wp] theorem actionPre_pointerFromImmediate (access : DAccess)
    (compiler : PointerPlaceMachine.Compiler K U C) (choice : C) (value : RvalueImmTy Provenance)
    (post : MPlace → DState → Prop) (onError : StepError → DState → Prop) :
    actionPre (PointerPlaceMachine.fromImmediate access compiler choice value) post onError =
      actionPre (compiler.builtinDeref choice value.layout.ty) (fun
        | none => onError (.invalidProgram "imm_ptr_to_mplace called on non-pointer type")
        | some ty => actionPre (compiler.layoutOf choice ty) (fun layout =>
            scalarCheckPre (value.imm.toScalarAndMeta.mapError ScalarOps.immediateError)
              (fun pair => scalarCheckPre
                ((pair.1.toPointer access.runtime.base).mapError ScalarOps.scalarError)
                (fun pointer => actionPre
                  (PointerPlaceMachine.withMetadata access pointer pair.2 layout false) post onError)
                onError) onError) onError) onError := by
  simp only [PointerPlaceMachine.fromImmediate, actionPre_bind_fun]
  congr 1
  funext pointee
  cases pointee with
  | none => rfl
  | some ty =>
    rw [actionPre_bind_fun]
    congr 1
    funext layout
    let decoded := value.imm.toScalarAndMeta.mapError ScalarOps.immediateError
    change actionPre (checked decoded >>= _) _ _ = _
    rw [actionPre_bind_fun, checkedPre]
    unfold decoded
    congr 1
    funext pair
    rcases pair with ⟨scalar, metadata⟩
    let pointer := (scalar.toPointer access.runtime.base).mapError ScalarOps.scalarError
    change actionPre (checked pointer >>= _) _ _ = _
    rw [actionPre_bind_fun, checkedPre]

/-- Dereferencing reads and builds the pointee before applying source validity.
Safe pointers are checked for null, access and alignment in order. Raw dynamic
tails check their vtable identity without reading through the pointer. -/
@[miri_initial_wp] theorem actionPre_typedDereference [DecidableEq K] (access : DAccess)
    (compiler : PointerPlaceMachine.Compiler K U C)
    (dynamic : DynamicLayoutHooks Provenance DState C) (vtable : VTableHooks Provenance DState C F T)
    (fuel : Nat) (choice : C) (source : Op) (post : MPlace → DState → Prop)
    (onError : StepError → DState → Prop) :
    actionPre (PointerPlaceMachine.dereference access compiler dynamic vtable fuel choice source)
      post onError =
      actionPre (compiler.kind choice source.layout.ty) (fun kind =>
        if kind == .other then onError (.invalidProgram "dereferencing non-pointer type")
        else actionPre (PlaceMachine.readImmediate access source) (fun value =>
          actionPre (PointerPlaceMachine.fromImmediate access compiler choice value) (fun place =>
            actionPre ValidityMachine.enforceValidity (fun enforce =>
              if !enforce then post place
              else if kind == .reference || kind == .box then
                let name := if kind == .reference then "reference" else "box"
                scalarCheckPre (Scalar.fromMaybePointer access.runtime.base place.mplace.ptr |>.mapError
                  ScalarOps.scalarError) (fun scalar =>
                  actionPre (ValidityMachine.scalarMayBeNull scalar) (fun isNull =>
                    if isNull then onError (.undefinedBehavior s!"dereferencing a null {name}")
                    else actionPre (DynamicLayout.sizeAndAlignFromMeta dynamic choice fuel
                        place.mplace.metadata place.layout) (fun sizeAlign =>
                      let result := sizeAlign.getD (place.layout.layout.size, place.layout.layout.align.abi)
                      actionPre (ValidityMachine.checkPointerAccess access place.mplace.ptr result.1)
                        (fun _ => actionPre (ValidityMachine.checkPointerAlign access place.mplace.ptr result.2)
                          (fun _ => post place) onError) onError) onError) onError) onError
              else if kind == .raw then
                if !place.layout.layout.isSized then
                  actionPre (compiler.structTail choice place.layout.ty) (fun
                    | .dynamic expected => match place.mplace.metadata with
                      | .none => onError (.invalidProgram "dynamic raw pointer missing metadata")
                      | .metadata metadata => scalarCheckPre
                        ((metadata.toPointer access.runtime.base).mapError ScalarOps.scalarError)
                        (fun pointer => actionPre (VTable.getPtrVTableType vtable choice pointer (some expected))
                          (fun _ => post place) onError) onError
                    | .slice | .str | .foreign => post place
                    | .other => onError (.invalidProgram "unexpected unsized raw-pointer tail")) onError
                else post place
              else onError (.invalidProgram "dereferencing unexpected pointer kind"))
              onError) onError) onError) onError := by
  rw [PointerPlaceMachine.dereference, actionPre_bind_fun]
  congr 1
  funext kind
  simp only [actionPre_ite]
  split
  · rfl
  · simp only [actionPre_bind_fun]
    congr 1
    funext value
    congr 1
    funext place
    congr 1
    funext enforce
    cases enforce
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, actionPre_ite]
      split
      · let scalar := Scalar.fromMaybePointer access.runtime.base place.mplace.ptr |>.mapError
          ScalarOps.scalarError
        change actionPre (checked scalar >>= _) _ _ = _
        rw [actionPre_bind_fun, checkedPre]
        congr 1
        funext address
        simp only [actionPre_bind_fun, actionPre_ite, purePre] <;> rfl
      · split
        · split
          · simp only [actionPre_bind_fun]
            congr 1
            funext tail
            cases tail <;> try rfl
            rename_i expected
            cases place.mplace.metadata with
            | none => rfl
            | metadata metadataValue =>
              let pointer := (metadataValue.toPointer access.runtime.base).mapError ScalarOps.scalarError
              change actionPre (checked pointer >>= _) _ _ = _
              rw [actionPre_bind_fun, checkedPre]
              congr 1
              funext ptr
              simp only [actionPre_bind_fun, purePre]
          · rfl
        · rfl

end PointerProjection

section ProductionProjection

variable {Os R HostP H D O Aff B Host F T : Type}
local notation "Stored" => Input.EvalCoreMachine.Stored Os R HostP H D O Aff B Host
local notation "IndexState" => Input.EvalCoreMachine.State Os R HostP H D O Aff B Host
local notation "MemoryKind" => MiriMemoryKind

/-- The production index hook reads the actual local operand and decodes a
target-sized integer after the scoped memory read. -/
@[miri_initial_wp] theorem actionPre_productionLocalIndex
    (prepared : Input.CompilerProviders.Prepared) (options : Input.EvalPlaceConstruction.Options)
    (access : ValidityMachine.Access MemoryKind Stored)
    (allocation : PlaceMachine.AllocationConfig MemoryKind
      (Input.EvalCoreMachine.User Os R HostP H D O Aff B Host))
    (compiler : ValidityMachine.Compiler MemoryKind Stored C)
    (vtable : VTableHooks Provenance IndexState C F T) (choice : C) (id : MIR.LocalId)
    (post : UInt64 → IndexState → Prop) (onError : StepError → IndexState → Prop) :
    actionPre ((Input.EvalPlaceConstruction.projection prepared options access allocation compiler vtable).localIndex
      choice id) post onError =
      actionPre (PlaceMachine.localToOpCore (Input.EvalPlaceConstruction.localLayout prepared)
          ValidityMachine.validationInProgress id) (fun operand =>
        actionPre (ValidityMachine.readImmediate access operand) (fun value =>
          scalarCheckPre (value.imm.toScalar.mapError ScalarOps.immediateError) (fun scalar =>
            scalarCheckPre ((scalar.toTargetUsize access.runtime.pointerSize).mapError ScalarOps.scalarError)
              post onError) onError) onError) onError := by
  change actionPre
    (PlaceMachine.localToOpCore (Input.EvalPlaceConstruction.localLayout prepared)
      ValidityMachine.validationInProgress id >>= _) _ _ = _
  simp only [actionPre_bind_fun]
  congr 1
  funext operand
  congr 1
  funext value
  cases value.imm.toScalar with
  | error => rfl
  | ok scalar =>
    change actionPre ((pure scalar : MachineHooks.M MemoryKind _ _) >>= _) _ _ = _
    rw [pure_bind]
    change _ = scalarCheckPre ((scalar.toTargetUsize access.runtime.pointerSize).mapError
      ScalarOps.scalarError) post onError
    generalize scalar.toTargetUsize access.runtime.pointerSize = result
    cases result <;> rfl

/-- The compiler's local layout constructor memoizes only a successful cache
miss and checks the frame again after the query. -/
@[miri_initial_wp] theorem actionPre_productionLocalLayout
    (prepared : Input.CompilerProviders.Prepared) (id : MIR.LocalId)
    (post : LocalLayout → State → Prop) (onError : Errors) :
    actionPre (Input.EvalPlaceConstruction.localLayout prepared id) post onError =
      StorageLiveWP.currentFramePre (fun frame =>
        scalarCheckPre ((frame.getLocal id).mapError StepError.stack) (fun slot =>
          match slot.layout with
          | some layout => post layout
          | none =>
            actionPre (Input.CompilerFrameContext.computeLocalLayout prepared id) (fun computed =>
              StorageLiveWP.currentFramePre (fun frame =>
                scalarCheckPre ((frame.getOrCacheLocalLayout id computed).mapError StepError.stack)
                  (fun update => StorageLiveWP.setCurrentFramePre update.1
                    (fun _ => post update.2) onError) onError) onError) onError) onError) onError := by
  rw [Input.EvalPlaceConstruction.localLayout, actionPre_bind_fun, StorageLiveWP.actionPre_currentFrame]
  congr 1
  funext frame before
  cases frame.getLocal id with
  | error => rfl
  | ok slot =>
    simp only [pure_bind, Except.mapError, scalarCheckPre]
    cases slot.layout with
    | some layout => rfl
    | none =>
      simp only [actionPre_bind_fun, StorageLiveWP.actionPre_currentFrame]
      congr 1
      funext computed
      congr 1
      funext frame state
      cases frame.getOrCacheLocalLayout id computed with
      | error => rfl
      | ok update =>
        rcases update with ⟨updated, layout⟩
        simp only [actionPre_bind_fun, StorageLiveWP.actionPre_setCurrentFrame, purePre]
        rfl

/-- The place hook in the production projection record uses its compiler's
dereference operation. Keeping this projection explicit lets the source
compiler binding continue into typed pointer construction. -/
@[miri_initial_wp] theorem canonical_productionPlaceDeref
    (prepared : Input.CompilerProviders.Prepared) (options : Input.EvalPlaceConstruction.Options)
    (access : ValidityMachine.Access MemoryKind Stored)
    (allocation : PlaceMachine.AllocationConfig MemoryKind
      (Input.EvalCoreMachine.User Os R HostP H D O Aff B Host))
    (compiler : ValidityMachine.Compiler MemoryKind Stored C)
    (vtable : VTableHooks Provenance IndexState C F T)
    (choice : C) (base : RuntimePlace Provenance) (skip : Bool) :
    (Input.EvalPlaceConstruction.projection prepared options access allocation compiler vtable).place.deref
      choice base skip = compiler.deref choice base skip := rfl

/-- Source place dereference first obtains the pointer operand. The explicit
simple-dereference path still reads and decodes it but skips typed validity. -/
@[miri_initial_wp] theorem actionPre_productionCompilerDeref
    (prepared : Input.CompilerProviders.Prepared) (options : Input.EvalPlaceConstruction.Options)
    (access : ValidityMachine.Access MemoryKind Stored)
    (pointers : PointerMachine.Hooks MemoryKind (ValidityMachine.Control Stored))
    (vtable : VTableHooks Provenance IndexState C F T)
    (typeCheck : C → MIR.Place → RuntimePlace Provenance →
      EStateM StepError IndexState Unit)
    (validate : C → RuntimePlace Provenance → EStateM StepError IndexState Unit)
    (choice : C) (base : RuntimePlace Provenance) (skip : Bool)
    (post : RuntimePlace Provenance → IndexState → Prop) (onError : StepError → IndexState → Prop) :
    let compiler := Input.EvalPlaceConstruction.compiler prepared options access pointers vtable typeCheck validate
    let frameIndex : EStateM StepError IndexState Nat := do
      match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error)
    let readLocal := fun (_ : C) id =>
      PlaceMachine.localToOpCore (Input.EvalPlaceConstruction.localLayout prepared)
        ValidityMachine.validationInProgress id
    let pointerCompiler := CompilerExecutionProviders.pointerCompiler prepared.lifecycle.calls.symbols.facts
    actionPre (compiler.deref choice base skip) post onError =
      actionPre (placeToOpCore MachineHooks.currentFrame options.debugAssertions frameIndex readLocal
          compiler.projection choice base) (fun source =>
        let finish := fun (target : MPlaceTy Provenance) => post ⟨.memory target.mplace, target.layout⟩
        if skip then actionPre (ValidityMachine.readImmediate access source) (fun value =>
          actionPre (PointerPlaceMachine.fromImmediate access pointerCompiler choice value) finish onError)
          onError
        else actionPre (PointerPlaceMachine.dereference access pointerCompiler
          (Input.EvalPlaceConstruction.dynamic prepared options vtable) vtable options.dynamicFuel choice source)
          finish onError) onError := by
  dsimp only
  simp only [Input.EvalPlaceConstruction.compiler, actionPre_bind_fun]
  congr 1
  funext source
  cases skip <;> simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun, purePre]

end ProductionProjection

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

@[miri_initial_wp] theorem canonical_operandDeref (config : Config) (choice : C) (source : Op) :
    (ExecutionMachine.operandHooks config).dereference choice source =
      config.operands.dereference choice source := rfl

@[miri_initial_wp] theorem canonical_validationOperandDeref (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (source : Op) :
    (ExecutionMachine.withValidation config limits).operands.dereference choice source =
      config.operands.dereference choice source := rfl

@[miri_initial_wp] theorem canonical_operandCompiler (config : Config) :
    (ExecutionMachine.operandHooks config).compiler = config.compiler := rfl

@[miri_initial_wp] theorem canonical_operandLayoutCompatible (config : Config)
    (computed known : LocalLayout) :
    (ExecutionMachine.operandHooks config).layoutCompatible computed known =
      config.copy.compatible computed known := rfl

@[miri_initial_wp] theorem canonical_operandDebug (config : Config) (limits : ExecutionMachine.Limits) :
    (ExecutionMachine.withValidation config limits).compiler.debugAssertions =
      config.compiler.debugAssertions := rfl

@[miri_initial_wp] theorem canonical_operandValidation (config : Config) (limits : ExecutionMachine.Limits) :
    (ExecutionMachine.withValidation config limits).compiler.validationInProgress =
      config.compiler.validationInProgress := rfl

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

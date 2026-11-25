import Miri.Verification.InitialWPAttr
import Miri.Verification.RvalueWP
import Miri.Verification.ScalarMemoryWP

/-! Pull back reads and writes through the production rvalue/place callbacks. -/

namespace Miri.Verification.PlaceReadWriteWP

open Miri.ABI Miri.Interpreter Miri.Memory RvalueWP Std.WP

variable {P S C E K U O X Host : Type}
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "State" => MachineHooks.State K U
local notation "Access" => PlaceMachine.AccessConfig K U

/-- A checked write queries validity after the write succeeds. Its error
continuation therefore sees either the failed write state or the state reached
during the validity decision or validation. -/
def writeValidityPre (hooks : PlaceHooks P S C E) (choice : C) (dest : RuntimePlace P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  actionPre (hooks.enforceValidity choice dest.layout) (fun validate =>
    if validate then actionPre (hooks.validate choice dest) post onError else post ()) onError

/-- A sized place dispatches to either the typed memory writer or the
optimized-local writer. The resolver can materialize a projected local. -/
def writeNoValidatePre (hooks : PlaceHooks P S C E) (choice : C) (value : Immediate P)
    (dest : RuntimePlace P) (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  if dest.layout.layout.isSized then
    actionPre (asMplaceOrMutableLocal hooks choice dest) (fun
      | .memory place => actionPre (hooks.writeMemoryNoValidate choice value place) post onError
      | .immediateLocal id layout =>
        actionPre (hooks.writeLocalImmediate choice id layout value) post onError) onError
  else onError (.invalidProgram "unsized immediate destination")

@[miri_initial_wp, miri_rvalue] theorem actionPre_writePlaceImmediateNoValidate
    (hooks : PlaceHooks P S C E) (choice : C) (value : Immediate P) (dest : RuntimePlace P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    actionPre (writePlaceImmediateNoValidate hooks choice value dest) post onError =
      writeNoValidatePre hooks choice value dest post onError := by
  simp only [writePlaceImmediateNoValidate, writeNoValidatePre, actionPre_ite]
  cases dest.layout.layout.isSized <;>
    simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte]
  · rfl
  · rw [actionPre_bind_fun]
    congr 1
    funext target
    cases target <;> rfl

def writePre (hooks : PlaceHooks P S C E) (choice : C) (value : Immediate P)
    (dest : RuntimePlace P) (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  writeNoValidatePre hooks choice value dest (fun _ => writeValidityPre hooks choice dest post onError) onError

@[miri_initial_wp, miri_rvalue] theorem actionPre_writePlaceImmediate (hooks : PlaceHooks P S C E) (choice : C)
    (value : Immediate P) (dest : RuntimePlace P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    actionPre (writePlaceImmediate hooks choice value dest) post onError =
      writePre hooks choice value dest post onError := by
  simp only [writePlaceImmediate, writePre, writeValidityPre, actionPre_bind_fun,
    actionPre_writePlaceImmediateNoValidate, actionPre_ite]
  congr 2

/-- Lower the typed read after its callback projection has been reduced. -/
@[miri_initial_wp] theorem actionPre_readImmediate [DecidableEq K] (access : Access)
    (operand : OpTy Provenance) (post : RvalueImmTy Provenance → State → Prop)
    (onError : StepError → State → Prop) :
    actionPre (PlaceMachine.readImmediate access operand) post onError =
      fun before => MemoryWP.immediateReadPre access operand before post onError := by
  rw [actionPre_eq_wp]
  exact funext fun before =>
    propext (MemoryWP.immediateReadPre_iff access operand before post onError).symm

/-- The canonical read callback uses the primitive operand and memory
dispatcher with exactly the same postconditions. -/
@[miri_initial_wp, miri_rvalue] theorem actionPre_canonicalRead [DecidableEq K] (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : OpTy Provenance)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).readImmediate choice operand) post onError =
      fun before => MemoryWP.immediateReadPre config.access operand before post onError := by
  rw [canonical_readImmediate, actionPre_readImmediate]

/-- The canonical write callback uses the projection dictionary already
installed in the execution configuration. -/
@[miri_initial_wp, miri_rvalue] theorem actionPre_canonicalWrite [DecidableEq K] (config : Config) (limits : ExecutionMachine.Limits)
    (choice : C) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).writeImmediate choice value dest) post onError =
      writePre (ExecutionMachine.projectionHooks config).place choice value dest post onError := by
  rw [canonical_writeImmediate, actionPre_writePlaceImmediate]

/-- A direct memory destination retains its resolved pointer and layout. -/
theorem writePre_memory (hooks : PlaceHooks P S C E) (choice : C) (value : Immediate P)
    (dest : RuntimePlace P) (memory : MemPlace P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop)
    (target : dest.ref = .memory memory) (sized : dest.layout.layout.isSized = true) :
    writePre hooks choice value dest post onError =
      actionPre (hooks.writeMemoryNoValidate choice value ⟨memory, dest.layout⟩)
        (fun _ => writeValidityPre hooks choice dest post onError) onError := by
  simp only [writePre, writeNoValidatePre, sized, ↓reduceIte, asMplaceOrMutableLocal, target]
  rfl

/-- A source-owned memory callback samples ghost mode and validation policy
at the actual write state. Both exits retain the typed memory effects. -/
@[miri_initial_wp, miri_rvalue] theorem actionPre_scopedWriteMemory [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C) (value : Immediate Provenance)
    (place : MPlaceTy Provenance)
    (post : Unit → ValidityMachine.State K U → Prop)
    (onError : StepError → ValidityMachine.State K U → Prop) (before : ValidityMachine.State K U) :
    actionPre ((ValidityMachine.placeHooks access allocation compiler).writeMemoryNoValidate choice
      value place) post onError before =
      MemoryWP.immediateWritePre {access with ghostMode := before.machine.user.payload.ghost}
        (fun _ => before.machine.user.payload.validation != .No) value place before post onError := by
  change actionPre (PlaceMachine.writeMemory {access with ghostMode := before.machine.user.payload.ghost}
    (fun _ => before.machine.user.payload.validation != .No) value place) post onError before = _
  rw [actionPre_eq_wp]
  exact propext (MemoryWP.immediateWritePre_iff _ _ _ _ _ _ _).symm

/-- Reading an immediate operand checks the ABI and initialization without
acquiring an allocation. The configured state retention sees no touched allocation. -/
@[miri_initial_wp, miri_rvalue] theorem immediateReadPre_immediate [DecidableEq K]
    (config : Access) (value : Immediate Provenance) (layout : LocalLayout) (before : State)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    MemoryWP.immediateReadPre config ⟨.immediate value, layout⟩ before post onError =
      let after := {before with machine := config.retainTouched before.machine none}
      if isPrimitiveReadable (localMemoryLayout layout).backendRepr then
        match value with
        | .uninit => onError (config.memoryError .invalidUninitBytes) after
        | _ => post ⟨value, layout⟩ after
      else onError (config.memoryError .invalidPrimitiveRead) after := by
  cases value <;> simp only [MemoryWP.immediateReadPre, MemoryWP.rawOperandPre,
    finishImmediateRead, MemoryWP.resultPre] <;>
    split <;> rfl

/-- A whole local in the current frame resolves to its storage kind. The
specialization applies with debug assertions disabled. A projected local
uses the exact materializing resolver instead. -/
theorem writePre_wholeLocal (hooks : PlaceHooks P S C E) (choice : C)
    (value : Immediate P) (layout : LocalLayout) (frameIndex : Nat) (id : Miri.MIR.LocalId)
    (identity : LocalsIdentity) (before current checked : S) (frame : Frame P LocalLayout E)
    (operand : Operand P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop)
    (sized : layout.layout.isSized = true) (debugOff : hooks.debugAssertions = false)
    (index : hooks.frameIndex before = .ok frameIndex current)
    (frameRead : hooks.getFrame current = .ok frame checked)
    (loaded : frame.getLocalOperand id = .ok operand) :
    let dest : RuntimePlace P := ⟨.local frameIndex id none identity, layout⟩
    writePre hooks choice value dest post onError before =
      match operand with
      | .indirect memory =>
        actionPre (hooks.writeMemoryNoValidate choice value ⟨memory, layout⟩)
          (fun _ => writeValidityPre hooks choice dest post onError) onError checked
      | .immediate _ =>
        actionPre (hooks.writeLocalImmediate choice id layout value)
          (fun _ => writeValidityPre hooks choice dest post onError) onError checked := by
  dsimp only
  simp only [writePre, writeNoValidatePre, sized, ↓reduceIte, asMplaceOrMutableLocal, Option.isSome,
    Bool.false_eq_true, requireCurrent_eq, actionPre_bind_fun,
    pure_bind, checkLocalIdentity_debugOff _ _ debugOff, debugOff]
  cases operand <;> simp only [actionPre, index, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, frameRead, loaded,
    stackLift_ok, pure, Pure.pure, EStateM.pure]

/-- A local source resolves its layout and storage first. Its immediate path
records a local read unless validation is in progress. The indirect path
leaves the actual memory access to the eventual operand reader. -/
def localToOpPre (layoutOf : Miri.MIR.LocalId → MachineHooks.M K U LocalLayout)
    (validationInProgress : MachineHooks.M K U Bool) (id : Miri.MIR.LocalId)
    (post : OpTy Provenance → State → Prop) (onError : StepError → State → Prop) : State → Prop :=
  actionPre (layoutOf id) (fun layout =>
    actionPre MachineHooks.currentFrame (fun frame =>
      match frame.getLocalOperand id with
      | .error error => onError (.stack error)
      | .ok op =>
        match op with
        | .indirect _ => post ⟨op, layout⟩
        | .immediate _ =>
          if layout.layout.isSized then
            actionPre validationInProgress (fun active =>
              if active then post ⟨op, layout⟩
              else actionPre (MachineHooks.afterLocalRead id) (fun _ => post ⟨op, layout⟩) onError)
              onError
          else onError (.invalidProgram "unsized local is immediate")) onError) onError

theorem actionPre_localToOpCore (layoutOf : Miri.MIR.LocalId → MachineHooks.M K U LocalLayout)
    (validationInProgress : MachineHooks.M K U Bool) (id : Miri.MIR.LocalId)
    (post : OpTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    actionPre (PlaceMachine.localToOpCore layoutOf validationInProgress id) post onError =
      localToOpPre layoutOf validationInProgress id post onError := by
  simp only [PlaceMachine.localToOpCore, localToOpPre, actionPre_bind_fun]
  congr 1
  funext layout
  congr 1
  funext frame
  cases frame.getLocalOperand id with
  | error error => rfl
  | ok operand =>
    cases operand with
    | indirect memory => rfl
    | immediate value =>
      cases layout.layout.isSized <;> simp only [pure_bind, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      · rfl
      · rw [actionPre_bind_fun]
        congr 1
        funext flag
        cases flag <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · rw [actionPre_bind_fun]; rfl
        · rfl

@[miri_initial_wp, miri_rvalue] theorem actionPre_localToOp (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (id : Miri.MIR.LocalId) (post : OpTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    actionPre (PlaceMachine.localToOp compiler choice id) post onError =
      localToOpPre (PlaceMachine.layoutLocal compiler choice) compiler.validationInProgress
        id post onError :=
  actionPre_localToOpCore _ _ _ _ _

/-- On an initialized scalar layout, pull the indirect read back through
the checked place access and its scalar load continuation. -/
theorem immediateReadPre_scalar [DecidableEq K] (config : Access) (operand : OpTy Provenance)
    (memory : MemPlace Provenance) (primitive : BackendPrimitive) (validRange : WrappingRange)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop)
    (before : State)
    (checked : MemoryWP.CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨memory, localMemoryLayout operand.layout⟩)
    (indirect : operand.op = .indirect memory)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.runtime = .ok (localMemoryLayout operand.layout).size) :
    MemoryWP.immediateReadPre config operand before post onError =
      checked.pre (fun selected =>
        MemoryWP.resultPre config before
          (scalarReadAfterAccess (localMemoryLayout operand.layout) primitive config.runtime selected)
          (fun value => post ⟨value.value, operand.layout⟩) onError) := by
  apply propext
  rw [MemoryWP.immediateReadPre_iff, MemoryWP.readImmediate_iff]
  exact MemoryWP.scalarRead_resultPre_iff config operand memory primitive validRange post onError
    before checked indirect backend width

/-- A sized ABI-compatible scalar store proceeds from the selected mutable
access to byte mutation and commit. The same continuation receives a typed
access, mutation, or commit error with its resulting state. -/
theorem immediateWritePre_scalar [DecidableEq K] (config : Access)
    (later : MemoryOperandLayout → Bool) (value : Scalar Provenance) (place : MPlaceTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) (before : State)
    (checked : MemoryWP.CheckedPlaceAccess config true before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩)
    (sized : (localMemoryLayout place.layout).backendRepr.isUnsized = false)
    (abi : immediateMatchesAbi (.scalar value) (localMemoryLayout place.layout) config.runtime =
      .ok ()) :
    MemoryWP.immediateWritePre config later (.scalar value) place before post onError =
      checked.pre (fun selected =>
        MemoryWP.resultPre config before
          (writeImmediateAfterAccess (.scalar value) (localMemoryLayout place.layout)
            config.runtime later selected) post onError) := by
  apply propext
  rw [MemoryWP.immediateWritePre_iff, MemoryWP.writeMemory_iff]
  exact MemoryWP.immediateWrite_resultPre_iff config later (.scalar value) place post onError
    before checked sized abi

/-- Once an optimized-local write has selected a live immediate and a
replacement frame, install the frame before sampling validation-in-progress,
recording the local write, and checking the ABI. -/
theorem actionPre_scopedWriteLocal [DecidableEq K] (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C) (id : Miri.MIR.LocalId)
    (layout : LocalLayout) (old value : Immediate Provenance)
    (post : Unit → ValidityMachine.State K U → Prop)
    (onError : StepError → ValidityMachine.State K U → Prop)
    (before current : ValidityMachine.State K U)
    (frame updated : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (sized : layout.layout.isSized = true)
    (loaded : MachineHooks.currentFrame before = .ok frame current)
    (localValue : frame.getLocalOperand id = .ok (.immediate old))
    (written : frame.setLocalOperand id (.immediate value) = .ok updated) :
    actionPre ((ValidityMachine.placeHooks access allocation compiler).writeLocalImmediate choice
      id layout value) post onError before =
      actionPre (MachineHooks.setCurrentFrame updated) (fun _ =>
        actionPre ValidityMachine.validationInProgress (fun active =>
          if active then actionPre (compiler.debugAbiCheck value layout) post onError
          else actionPre (MachineHooks.afterLocalWrite id false)
            (fun _ => actionPre (compiler.debugAbiCheck value layout) post onError) onError)
          onError) onError current := by
  change actionPre (placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
    ValidityMachine.validationInProgress MachineHooks.afterLocalWrite compiler.debugAbiCheck
    id layout value) post onError before = _
  rw [actionPre_eq_wp]
  apply propext
  rw [MemoryWP.localImmediateWrite_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sized loaded localValue written]
  rw [← actionPre_eq_wp]
  simp only [actionPre_bind_fun, actionPre_ite]

@[miri_initial_wp, miri_rvalue] theorem writePre_memory_mk
    (hooks : PlaceHooks P S C E) (choice : C) (value : Immediate P)
    (memory : MemPlace P) (layout : LocalLayout)
    (post : Unit → S → Prop) (onError : StepError → S → Prop)
    (sized : layout.layout.isSized = true) :
    writePre hooks choice value ⟨.memory memory, layout⟩ post onError =
      actionPre (hooks.writeMemoryNoValidate choice value ⟨memory, layout⟩)
        (fun _ => writeValidityPre hooks choice ⟨.memory memory, layout⟩ post onError) onError :=
  writePre_memory hooks choice value _ memory post onError rfl sized

@[miri_initial_wp] theorem wp_canonicalRead [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (operand : OpTy Provenance)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    wp ((ExecutionMachine.rvalueHooks config limits).readImmediate choice operand) post onError =
      fun before => MemoryWP.immediateReadPre config.access operand before post onError := by
  rw [← actionPre_eq_wp, actionPre_canonicalRead]

@[miri_initial_wp] theorem wp_canonicalWrite [DecidableEq K] (config : Config)
    (limits : ExecutionMachine.Limits) (choice : C) (value : Immediate Provenance)
    (dest : RuntimePlace Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    wp ((ExecutionMachine.rvalueHooks config limits).writeImmediate choice value dest) post onError =
      writePre (ExecutionMachine.projectionHooks config).place choice value dest post onError := by
  rw [← actionPre_eq_wp, actionPre_canonicalWrite]

/-- Reify the retag scope's action as a predicate so the enclosed copy can
be simplified without expanding the borrow tracker scope. -/
@[miri_initial_wp] theorem retagModePre_eq_pullback {A : Type}
    (mode : Miri.TreeBorrows.RetagPolicy.RetagMode) (action : MachineHooks.M K U A)
    (post : A → State → Prop) (onError : StepError → State → Prop) :
    RvalueWP.retagModePre mode action post onError =
      RvalueWP.retagModePullback mode (actionPre action) post onError := rfl

/-- A copy checks type compatibility and padding before the source read.
An immediate is written directly when compatible, or through a materialized
destination for transmute. An indirect source uses the configured byte copy. -/
def copyNoValidatePre (hooks : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C)
    (choice : C) (source : OpTy P) (dest : RuntimePlace P) (allowTransmute : Bool)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
  match copy.compatible source.layout dest.layout with
  | .error error => onError error
  | .ok compatible =>
    if !compatible && !allowTransmute then onError (.invalidProgram "copy type mismatch")
    else
      match copy.hasPadding source.layout with
      | .error error => onError error
      | .ok padding =>
        let write : ImmediateOrPlace P → S → Prop := fun
          | .immediate value =>
            if !source.layout.layout.isSized || !dest.layout.layout.isSized then
              onError (.invalidProgram "copy immediate is unsized")
            else if source.layout.layout.size != dest.layout.layout.size then
              onError (.invalidProgram "copy immediate size mismatch")
            else if compatible then
              writeNoValidatePre hooks choice value.value dest post onError
            else
              actionPre (forceAllocation hooks choice dest) (fun memory =>
                actionPre (hooks.writeMemoryNoValidate choice value.value ⟨memory.mplace, source.layout⟩)
                  post onError) onError
          | .place memory =>
            actionPre (forceAllocation hooks choice dest) (fun target =>
              actionPre (copy.memoryCopy choice ⟨memory.mplace, source.layout⟩ target) post onError) onError
        if padding then
          write (match source.op with
            | .immediate value => .immediate ⟨value, localMemoryLayout source.layout⟩
            | .indirect mplace => .place ⟨mplace, localMemoryLayout source.layout⟩)
        else actionPre (copy.readRaw choice source) write onError

@[miri_initial_wp, miri_rvalue] theorem actionPre_copyRuntimePlaceNoValidate
    (hooks : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C)
    (choice : C) (source : OpTy P) (dest : RuntimePlace P) (allowTransmute : Bool)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) :
    actionPre (copyRuntimePlaceNoValidate hooks copy choice source dest allowTransmute) post onError =
      copyNoValidatePre hooks copy choice source dest allowTransmute post onError := by
  simp only [copyRuntimePlaceNoValidate, copyNoValidatePre]
  cases copy.compatible source.layout dest.layout with
  | error error => rfl
  | ok compatible =>
    change actionPre ((pure compatible : PlaceM S Bool) >>= _) post onError = _
    rw [pure_bind, actionPre_ite]
    split
    · simp only [actionPre_bind_fun, ite_eq_left ‹_›]
      rfl
    · simp only [ite_eq_right ‹_›]
      cases copy.hasPadding source.layout with
      | error error => rfl
      | ok padding =>
        change actionPre ((pure padding : PlaceM S Bool) >>= _) post onError = _
        simp only [pure_bind, actionPre_ite, actionPre_bind_fun]
        suffices branches : (fun value : ImmediateOrPlace P => actionPre (match value with
            | .immediate value => do
              if !source.layout.layout.isSized || !dest.layout.layout.isSized then
                throw (.invalidProgram "copy immediate is unsized")
              if source.layout.layout.size != dest.layout.layout.size then
                throw (.invalidProgram "copy immediate size mismatch")
              if compatible then writePlaceImmediateNoValidate hooks choice value.value dest
              else
                let memory ← forceAllocation hooks choice dest
                hooks.writeMemoryNoValidate choice value.value ⟨memory.mplace, source.layout⟩
            | .place memory => do
              let target ← forceAllocation hooks choice dest
              copy.memoryCopy choice ⟨memory.mplace, source.layout⟩ target) post onError) = _ by
          split
          case isFalse =>
            exact congrArg (fun success => actionPre (copy.readRaw choice source) success onError) branches
          case isTrue => exact congrFun branches _
        funext value
        cases value with
        | immediate value =>
          simp only [actionPre_ite, actionPre_bind_fun, actionPre_writePlaceImmediateNoValidate]
          rfl
        | place memory => rw [actionPre_bind_fun]

/-- Validity runs only after the copy. A type-changing copy validates the
source layout first, then validates the destination in the resulting state. -/
def copyPre (hooks : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C)
    (choice : C) (source : OpTy P) (dest : RuntimePlace P) (allowTransmute : Bool)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) : S → Prop :=
      copyNoValidatePre hooks copy choice source dest allowTransmute (fun _ =>
        actionPre (hooks.enforceValidity choice dest.layout) (fun validate =>
          if validate then
            if source.layout.ty != dest.layout.ty then
              actionPre (copy.validateSource choice source.layout dest)
                (fun _ => actionPre (hooks.validate choice dest) post onError) onError
            else actionPre (hooks.validate choice dest) post onError
          else post ()) onError) onError

@[miri_initial_wp, miri_rvalue] theorem actionPre_copyRuntimePlace
    (hooks : PlaceHooks P S C E) (copy : PlaceCopyHooks P S C)
    (choice : C) (source : OpTy P) (dest : RuntimePlace P) (allowTransmute : Bool) :
    actionPre (copyRuntimePlace hooks copy choice source dest allowTransmute) =
      copyPre hooks copy choice source dest allowTransmute := by
  funext post onError
  simp only [copyRuntimePlace, copyPre, actionPre_bind_fun, actionPre_ite,
    actionPre_copyRuntimePlaceNoValidate]
  congr 2

end Miri.Verification.PlaceReadWriteWP

import LanguageGuardStack
import LanguageGuardValidity
import Miri.Interpreter.TypedValidityProviders
import Miri.Input.RuntimeArrayQueries

namespace DuplicatePrefix.LanguageGuardValidity
open Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR ValidityVisitor

variable {K U C Fn A : Type} [DecidableEq K]
local notation "State" => ValidityMachine.State K U
local notation "Visitor" => ValidityVisitor.Hooks Provenance State C MachineHooks.FrameExtra Fn A ValidityMemory.PaddingHandle

/-- The runtime array wrappers preserve the canonical Boolean visitor's
ghost, place and memory fields. Only the live compiler-size/type cache
classification and the type name need to be resolved for this scalar. -/
theorem validateArrayWrappedBoolean
    (runtimeArrays : Miri.Input.RuntimeArrayQueries.Access State)
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (access : ValidityMachine.Access K U)
    (alloc : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (retagFuel fuel : Nat) (base : Visitor) (choice : C)
    (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (index : Miri.MIR.LocalId) (value : Bool) (layout : LocalLayout) (slot : LocalState Provenance LocalLayout)
    (atSlot : caller.locals[index]? = some slot)
    (cached : slot.layout = some layout)
    (stored : slot.value = .live (.immediate (.scalar (Scalar.fromBool value))))
    (sized : layout.layout.isSized = true)
    (inactive : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (debug : compiler.debugAssertions = false)
    (readable : isPrimitiveReadable layout.layout.backendRepr = true)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (name : String) :
    let h := Miri.Input.RuntimeArrayQueries.validityHooks runtimeArrays
      (TypedValidityProviders.visitor prepared runtime access alloc compiler pointers retag retagFuel base)
    let before : State := ⟨⟨older.push caller⟩, machine⟩
    let destination : RuntimePlace Provenance := ⟨.local older.size index none caller.localsIdentity, layout⟩
    h.typeName choice layout.ty before = .ok name before →
    h.classify choice layout.ty (ghostOn before) = .ok .boolean (ghostOn before) →
    ValidityMachine.validateRuntime h choice (fuel + 1) destination true before = .ok () before := by
  intro h before destination typeName classified
  let paths := CompilerPaths.validityHooks prepared base
  let dynamic := PlaceDynamic.withVTable paths.projection.dynamic paths.vtable
  let p : PointerPlaceMachine.Compiler K U C := CompilerExecutionProviders.pointerCompiler prepared
  let placeCompiler := PointerPlaceMachine.bindCompiler access alloc p dynamic paths.vtable
    paths.projection.dynamicFuel compiler
  let placeHooks := ValidityMachine.placeHooks access alloc (ValidityMachine.compilerPolicy placeCompiler)
  let environment := ValidityMachine.memoryEnvironment access
  have localRead := ghostLocalBoolean access alloc placeCompiler value choice older caller (ghostOn before).machine
    index layout slot atSlot cached stored sized rfl debug
  have localOperand :
      h.toOp choice destination (ghostOn before) =
        .ok ⟨.immediate (.scalar (Scalar.fromBool value)), layout⟩ (ghostOn before) := by
    exact localRead
  have checked := validateBooleanPlace value h choice fuel destination before name inactive
    (fun _ => rfl) typeName localOperand classified
  have validated : validatePlace h choice (fuel+1) destination false true before = .ok () before := by
    apply checked
    · change ((do
        let operand ← placeToOp placeHooks choice destination
        ValidityMemory.readImmediate environment operand .boolean) : ValidityMachine.M K U _)
          (ghostOn before) = _
      change placeToOp placeHooks choice destination (ghostOn before) = _ at localOperand
      simp only [bind, Bind.bind, EStateM.bind, localOperand]
      exact readBooleanImmediate value access layout (ghostOn before) readable (retain _)
    · exact clearBooleanImmediate value environment placeHooks choice ValidityMachine.validationInProgress
        MachineHooks.afterLocalWrite destination (ghostOn before) localOperand
  simp only [ValidityMachine.validateRuntime, ValidityMachine.enforceValidityRecursively, before, shallow,
    show (ValidityMachine.ValidationMode.Shallow == .Deep) = false from rfl, bind, Bind.bind, pure,
    Pure.pure, get, getThe, MonadStateOf.get, EStateM.get, EStateM.bind, EStateM.pure]
  exact validated

end DuplicatePrefix.LanguageGuardValidity


namespace DuplicatePrefix.GuardReturnCopy
open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR
open Miri.Input
open EmptyFunction.FrameExit
open DuplicatePrefix.LanguageGuardStack
open DuplicatePrefix.LanguageGuardValidity

variable {K U C F A : Type} [DecidableEq K]
local notation "State" => ValidityMachine.State K U

/-- Copy the actual Boolean return value into a live cached caller slot.
The nested compiler configuration lookup is explicit, and shallow
validation runs on the actual updated state. -/
theorem copyFalseShallow
    (runtimeArrays : RuntimeArrayQueries.Access State)
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (access : ValidityMachine.Access K U)
    (alloc : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (copy : PlaceCopyHooks Provenance State C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (base : ValidityVisitor.Hooks Provenance State C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (retagBudget fuel : Nat) (choice : C)
    (nested : Unit → Except StepError
      (ValidityVisitor.Hooks Provenance State C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle))
    (validator : compiler.validate = fun choice place => do
      match nested () with
      | .error error => throw error
      | .ok visitor => ValidityMachine.validateRuntime visitor choice (fuel + 1) place true)
    (older : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (index : Miri.MIR.LocalId) (layout : LocalLayout) (slot : LocalState Provenance LocalLayout)
    (atSlot : caller.locals[index]? = some slot)
    (live : ∃ old, slot.value = .live (.immediate old))
    (cached : slot.layout = some layout)
    (sized : layout.layout.isSized = true)
    (inactive : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (noClocks : caller.extra.dataRace = none)
    (debug : compiler.debugAssertions = false)
    (abi : compiler.debugAbiCheck = fun _ _ => pure ())
    (readable : isPrimitiveReadable layout.layout.backendRepr = true)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (compatible : copy.compatible layout layout = .ok true)
    (padding : ∃ hasPadding, copy.hasPadding layout = .ok hasPadding)
    (name : String) :
    let visitor := RuntimeArrayQueries.validityHooks runtimeArrays
      (TypedValidityProviders.visitor prepared runtime access alloc compiler pointers retag retagBudget base)
    let destination : RuntimePlace Provenance := ⟨.local older.size index none caller.localsIdentity, layout⟩
    let newSlot := {slot with value := .live (.immediate (.scalar (Scalar.fromBool false)))}
    let updatedCaller := {caller with locals := caller.locals.setIfInBounds index newSlot}
    let updated := withCurrent older updatedCaller machine
    let copy := {copy with readRaw := fun _ => PlaceMachine.readRaw access}
    nested () = .ok visitor →
    visitor.typeName choice layout.ty updated = .ok name updated →
    visitor.classify choice layout.ty (ghostOn updated) = .ok .boolean (ghostOn updated) →
    copyRuntimePlace (ValidityMachine.placeHooks access alloc compiler) copy choice
      ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ destination true
      (withCurrent older caller machine) = .ok () updated := by
  intro visitor destination newSlot updatedCaller updated copy' resolve typeName classified
  have copied := copyFalseScoped access alloc compiler copy' choice older caller machine index
    slot layout atSlot live sized noClocks debug abi compatible padding rfl (retain machine)
  change copyRuntimePlace (ValidityMachine.placeHooks access alloc compiler) copy' choice
    ⟨.immediate (.scalar (Scalar.fromBool false)), layout⟩ destination true
    (withCurrent older caller machine) = _ at copied
  rw [copied]
  have present : updatedCaller.locals[index]? = some newSlot := by
    have h := (Array.getElem?_eq_some_iff.mp atSlot).1
    simp [updatedCaller, Array.setIfInBounds, h]
  have validated := validateArrayWrappedBoolean runtimeArrays prepared runtime access alloc compiler pointers
    retag retagBudget fuel base choice older updatedCaller machine index false layout newSlot present cached
    rfl sized inactive shallow debug readable retain name typeName classified
  simp only [ValidityMachine.enforceValidity, withCurrent, shallow, bind, Bind.bind, get,
    getThe, MonadStateOf.get, EStateM.get, EStateM.bind, pure, Pure.pure, EStateM.pure,
    show (ValidityMachine.ValidationMode.Shallow != .No) = true from rfl, ↓reduceIte,
    validator, resolve]
  exact validated

end DuplicatePrefix.GuardReturnCopy

#print axioms DuplicatePrefix.LanguageGuardValidity.validateArrayWrappedBoolean
#print axioms DuplicatePrefix.GuardReturnCopy.copyFalseShallow

import Miri.Verification.DiscriminantWP

/-! Selected discriminant writes and their layout-dependent tag continuations. -/
namespace MiriTests.Verification.DiscriminantWP

open Miri Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- A selected uninhabited write reaches the UB continuation in the state
left by destination projection, before a compiler query or a tag access. -/
theorem selected_uninhabited (config : Config) (limits : ExecutionMachine.Limits)
    (place : Place) (variant : Nat) (before projected : State)
    (frame : Frame) (loc : Location) (block : BasicBlock) (stmt : Statement)
    (destination : RuntimePlace Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .SetDiscriminant place variant)
    (placeOk : PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
      () place false before = .ok destination projected)
    (uninhabited : destination.layout.layout.isVariantUninhabited variant = true)
    (handled : onError (.undefinedBehavior s!"UninhabitedEnumVariantWritten({variant})") projected) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind]
  rw [RvalueWP.actionPre_ok placeOk]
  simpa only [miri_rvalue, uninhabited, ↓reduceIte] using handled

/-- The projected tag layout and address feed the exact physical store.
The source-owned hook samples the ghost flag on entry, and the continuation
checks validity in the state produced by the store. -/
theorem tag_memory_write (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U Unit)
    (destination : RuntimePlace Provenance) (memory : MemPlace Provenance)
    (tagValue : ScalarInt) (before : ValidityMachine.State K U)
    (post : Unit → ValidityMachine.State K U → Prop)
    (onError : StepError → ValidityMachine.State K U → Prop)
    (sized : destination.layout.layout.isSized = true)
    (projected : destination.ref = .memory memory) :
    let hooks := ValidityMachine.placeHooks access allocation compiler
    wp (writePlaceImmediate hooks () (.scalar (.fromScalarInt tagValue)) destination) post onError before =
      MemoryWP.immediateWritePre {access with ghostMode := before.machine.user.payload.ghost}
        (fun _ => before.machine.user.payload.validation != .No) (.scalar (.fromScalarInt tagValue))
        ⟨memory, destination.layout⟩ before
        (fun _ => RvalueWP.actionPre (hooks.enforceValidity () destination.layout) (fun enforce =>
          if enforce then RvalueWP.actionPre (hooks.validate () destination) post onError else post ()) onError)
        onError := by
  simp only [← RvalueWP.actionPre_eq_wp, DiscriminantWP.actionPre_writePlaceScalar, sized,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [DiscriminantWP.actionPre_asMplace_memory _ _ _ _ _ _ projected]
  simp only [miri_rvalue]

private def tag : ABI.Scalar :=
  .Initialized (value := .Int .I8 false) (validRange := ⟨0, 255⟩)
private def layout (variants : Variants := .Single 0) (ty : Nat := 0)
    (size : Size := Size.ofBytes 1) : TyAndLayout TyId := ⟨ty, {
  fields := .Arbitrary #[Size.ZERO] #[0], variants := variants,
  backendRepr := .Scalar tag, largestNiche := none, uninhabited := false,
  align := .new .ONE, size := size, maxReprAlign := none,
  unadjustedAbiAlign := .ONE, reprC := false, randomizationSeed := 0 }⟩
private def variant : VariantLayout :=
  ⟨Size.ofBytes 1, .Scalar tag, #[], #[], none, false⟩
private def direct : TyAndLayout TyId := layout (.Multiple tag .Direct 0 #[variant, variant])
private def niche : TyAndLayout TyId :=
  layout (.Multiple tag (.Niche 2 0 1 255) 0 #[variant, variant, variant])

private structure Trace where
  value : Scalar AllocId
  events : List String

private def trace (event : String) : RvalueM Trace Unit :=
  modify fun state => { state with events := state.events ++ [event] }

private def scalar (value : UInt8) : Scalar AllocId :=
  .fromScalarInt (.ofUInt8 value)

private def hooks : DiscriminantHooks AllocId Trace Unit (TyAndLayout TyId) where
  runtimeTarget := RuntimeTargetDataLayout.default
  discriminantLayout := fun _ _ => do trace "type"; pure (layout (.Single 0) 10 (Size.ofBytes 2))
  discriminantValue := fun _ _ _ => do trace "bits"; pure (some (10, 258))
  tagLayout := fun _ _ => do trace "tag"; pure (layout (.Single 0) 11)
  variantForDiscriminant := fun _ _ _ => pure (some 1)
  adtVariantCount := fun _ _ => pure 3
  projectRead := fun _ operand _ => do trace "field"; pure operand
  readImmediate := fun _ _ => do
    trace "load"
    pure ⟨.scalar (← get).value, layout (.Single 0) 11⟩
  destLayout := id
  projectWrite := fun _ dest _ => do trace "project"; pure dest
  writeScalar := fun _ value _ => do
    trace "write"
    modify fun state => { state with value }
  toOp := fun _ dest => do trace "operand"; pure ⟨.immediate .uninit, dest⟩
  scalarMayBeNull := fun _ _ => pure false

/-- The compiler supplies a two-byte discriminant, and the write stores its
low byte using the one-byte tag layout. -/
example :
    wp (Discriminant.writeDiscriminant hooks () 1 direct)
      (fun _ after => after.value = scalar 2 ∧ after.events = ["type", "bits", "project", "write"])
      (fun _ _ => False) ⟨scalar 42, []⟩ := by
  rw [← RvalueWP.actionPre_eq_wp, DiscriminantWP.actionPre_writeDiscriminant]
  simp only [miri_rvalue, hooks, direct, layout]
  cbv
  exact ⟨rfl, trivial⟩

/-- The tagged niche maps 255 + 1 to zero at tag width. -/
example :
    wp (Discriminant.writeDiscriminant hooks () 1 niche)
      (fun _ after => after.value = scalar 0 ∧ after.events = ["tag", "project", "write"])
      (fun _ _ => False) ⟨scalar 42, []⟩ := by
  rw [← RvalueWP.actionPre_eq_wp, DiscriminantWP.actionPre_writeDiscriminant]
  cbv
  decide

/-- Zero already encodes variant one, so selecting implicit variant two
fails after reading the tag and before any write. -/
example :
    wp (Discriminant.writeDiscriminant hooks () 2 niche)
      (fun _ _ => False)
      (fun error failed => error = .undefinedBehavior "InvalidNichedEnumVariantWritten" ∧
        failed.events = ["operand", "type", "tag", "field", "load"])
      ⟨scalar 0, []⟩ := by
  rw [← RvalueWP.actionPre_eq_wp, DiscriminantWP.actionPre_writeDiscriminant]
  simp only [miri_rvalue, hooks, niche, layout]
  cbv

end MiriTests.Verification.DiscriminantWP

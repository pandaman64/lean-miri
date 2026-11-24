import duplicate_prefix.EmptyReferenceSteps

namespace DuplicatePrefix.EmptyWildcardRetag
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows

/-- An unresolved lookup in the actual address map leaves the zero-width
wildcard pointer unresolved. -/
theorem ofSelection
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (state : ValidityMachine.State K U) (address : UInt64)
    (selected : state.machine.user.addresses.ptrGetAlloc
      (Pointer.new .wildcard (Size.ofBytes address)) (Int64.ofInt 0)
      { sizeOf := fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size),
        isLive := fun id => some (state.machine.memory.isAllocLive id) }
      pointers.arithmetic = .ok none) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) state =
      .ok none state := by
  simp only [Pointer.new, Size.ofBytes] at selected
  unfold TypedValidityProviders.resolveAllocation PointerMachine.resolvePointer
  simp only [Pointer.new, Size.ofBytes, Id.run, bind, EStateM.bind, pure,
    get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set]
  simp only [show (decide ((0 : Int) < -2 ^ 63) || decide ((0 : Int) ≥ 2 ^ 63)) = false by decide,
    Bool.false_eq_true, ↓reduceIte, selected]
  rfl

/-- The actual unresolved zero-width reborrow keeps existing wildcard
provenance, without installing a child or protector. -/
theorem reborrow
    [DecidableEq K]
    (hooks : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (state : MachineHooks.State K U)
    (check : hooks.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state)
    (unresolved : hooks.resolveAllocation place.mplace.ptr state = .ok none state)
    (log : hooks.logCreation place Size.ZERO policy tag none state = .ok () state) :
    TypedRetag.reborrow hooks budget place Size.ZERO policy tag state =
      .ok place.mplace.ptr.provenance state := by
  unfold TypedRetag.reborrow
  simp only [bind, EStateM.bind, check, unresolved]
  simp only [Size.ZERO]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [EStateM.bind]
  erw [log]
  rfl

#print axioms ofSelection
#print axioms reborrow
end DuplicatePrefix.EmptyWildcardRetag

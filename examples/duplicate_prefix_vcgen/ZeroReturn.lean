import Miri.Verification.CanonicalStepWP
import Miri.Interpreter.Unwind
import ZeroBoolean

namespace DuplicatePrefix.ZeroBoolean
set_option linter.unusedSectionVars false
open Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- Normal cleanup of immediate locals executes no deallocation. The genuine
normal after-pop hook supplies the continuation action. -/
theorem cleanupImmediate (lifecycle : CallMachine.Lifecycle K U C)
    (unwind : Unwind.Hooks K U C O) (choice : C) (frame : Frame)
    (target : BasicBlockId) (action : UnwindAction)
    (continues : frame.returnContinuation = .goto (some target) action)
    (noVarargs : frame.vaList = #[])
    (immediate : ∀ slot ∈ frame.locals.toList, ∀ place, slot.value ≠ .live (.indirect place))
    (bindAfterPop : lifecycle.afterPop = fun c frame unwinding =>
      Unwind.afterStackPop unwind c frame.extra unwinding)
    (state : State) :
    CallMachine.cleanup lifecycle choice false frame state = .ok .normal state := by
  have noDealloc (slots : List (LocalState Provenance LocalLayout))
      (all : ∀ slot ∈ slots, ∀ place, slot.value ≠ .live (.indirect place)) :
      (forIn slots PUnit.unit (fun slot _ =>
        match slot.value with
        | .live (.indirect place) => do
          lifecycle.storage.deallocateStack place.ptr
          pure (.yield PUnit.unit)
        | _ => pure (.yield PUnit.unit)) : MachineHooks.M K U PUnit) = pure PUnit.unit := by
    induction slots with
    | nil => rfl
    | cons first rest ih =>
      have tail : ∀ slot ∈ rest, ∀ place, slot.value ≠ .live (.indirect place) := by
        intro slot inRest
        exact all slot (List.mem_cons_of_mem _ inRest)
      have step := ih tail
      funext before
      simp only [List.forIn_cons]
      cases firstValue : first.value with
      | dead => simpa [firstValue, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure] using congrFun step before
      | live operand =>
        cases operand with
        | immediate =>
          simpa [firstValue, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure] using congrFun step before
        | indirect place => exact (all first List.mem_cons_self place firstValue).elim
  unfold CallMachine.cleanup
  simp only [continues, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← Array.forIn_toList]
  change ((no_index (forIn frame.locals.toList PUnit.unit (fun slot _ =>
      match slot.value with
      | .live (.indirect place) => do
        lifecycle.storage.deallocateStack place.ptr
        pure (.yield PUnit.unit)
      | _ => pure (.yield PUnit.unit)) : MachineHooks.M K U PUnit)) >>= _) state = _
  rw [noDealloc frame.locals.toList immediate]
  simp [noVarargs, bindAfterPop, Unwind.afterStackPop, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure] <;> rfl

/-- Canonical Return transfers the Boolean to the caller's whole local zero,
performs source cleanup, and resumes the caller at its saved target. The pop
premise is the exact continuation theorem supplied by the release proof. -/
theorem normalReturnToCaller (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (choice : C) (layout : LocalLayout)
    (unwind : Unwind.Hooks K U C O)
    (afterPop : (ExecutionMachine.withValidation config limits).lifecycle.afterPop =
      fun c frame unwinding => Unwind.afterStackPop unwind c frame.extra unwinding)
    (older : Array Frame) (caller callee : Frame)
    (beforePop afterPopMachine : MachineHooks.MachineState K U)
    (profile : BooleanLocalProfile config limits choice layout beforePop)
    (callerProfile : BooleanLocalProfile config limits choice layout afterPopMachine)
    (block : BasicBlock) (pc : Location) (location : callee.location = .mir pc)
    (located : callee.body.basicBlocks[pc.block]? = some block) (normal : block.cleanup = false)
    (target : BasicBlockId) (action : UnwindAction)
    (continues : callee.returnContinuation = .goto (some target) action)
    (destination : callee.returnPlace = .frameLocal older.size 0 none layout caller.localsIdentity)
    (noVarargs : callee.vaList = #[])
    (immediate : ∀ slot ∈ callee.locals.toList, ∀ place, slot.value ≠ .live (.indirect place))
    (calleeBound : 0 < callee.locals.size)
    (calleeLive : callee.locals[0].value = .live (.immediate (.scalar (.fromBool true))))
    (calleeCached : callee.locals[0].layout = some layout)
    (calleeNoRace : callee.extra.dataRace = none)
    (reader : (profilePlace config limits).localToOp choice 0 =
      PlaceMachine.localToOp (ExecutionMachine.withValidation config limits).compiler choice 0)
    (callerBound : 0 < caller.locals.size) (callerOld : Immediate Provenance)
    (callerLive : caller.locals[0].value = .live (.immediate callerOld))
    (callerNoRace : caller.extra.dataRace = none)
    (pop : ∀ finish failure,
      ProtectorReleaseWP.popRawPre
        (TypedMachineBindings.retagHooks (ExecutionMachine.withValidation config limits).access
          (ExecutionMachine.withValidation config limits).retag)
        finish failure (atFrame (older.push caller) callee beforePop) ↔
      finish callee (atFrame older caller afterPopMachine))
    (post : State → Prop) (failure : StepError → State → Prop) :
    CanonicalStepWP.returnPre config limits choice false post failure (atFrame (older.push caller) callee beforePop) ↔
      post (atFrame older {setTrue caller callerBound with location := .mir ⟨target, 0⟩} afterPopMachine) := by
  have read := readReturnTrue config limits choice layout (older.push caller) callee beforePop profile
    calleeBound calleeLive calleeCached calleeNoRace reader
  have copied := copyReturnTrue config limits choice layout older caller afterPopMachine callerProfile
    callerBound callerOld callerLive callerNoRace
  have cleaned := cleanupImmediate (ExecutionMachine.withValidation config limits).lifecycle unwind choice callee
    target action continues noVarargs immediate afterPop (atFrame older (setTrue caller callerBound) afterPopMachine)
  have current : (atFrame (older.push caller) callee beforePop).stack.currentFrame? = some callee := by
    simp [atFrame, Stack.currentFrame?]
  simp only [CanonicalStepWP.returnPre, InstructionWP.returnPreWithEffects, current, location,
    located, normal, show (false != false) = false from rfl, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
  change InstructionWP.resultPre _ failure
    ((ExecutionMachine.terminatorHooks config limits).returnOperand choice (atFrame (older.push caller) callee beforePop)) ↔ _
  rw [read]
  simp only [InstructionWP.resultPre]
  rw [pop]
  rw [destination]
  change InstructionWP.resultPre (fun _ => CanonicalStepWP.cleanupFramePre
      (ExecutionMachine.withValidation config limits).lifecycle choice false callee
      (InstructionWP.finishReturnPre (ExecutionMachine.terminatorHooks config limits).toControlHooks
        choice false callee post failure) failure) failure
    ((ExecutionMachine.terminatorHooks config limits).copyReturn choice
      ⟨.immediate (.scalar (.fromBool true)), layout⟩
      (.frameLocal older.size 0 none layout caller.localsIdentity)
      (atFrame older caller afterPopMachine)) ↔ _
  rw [copied]
  simp only [InstructionWP.resultPre]
  rw [CanonicalStepWP.cleanupFramePre_iff]
  rw [RvalueWP.actionPre_ok cleaned]
  simp [InstructionWP.finishReturnPre, continues, InstructionWP.jumpPre,
    InstructionWP.locationPre, atFrame, Stack.currentFrame?, Array.set_push] <;> rfl

#print axioms normalReturnToCaller
#print axioms cleanupImmediate
end DuplicatePrefix.ZeroBoolean

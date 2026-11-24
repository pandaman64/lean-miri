import Representative
open Miri.Memory Miri.MIR Miri.Interpreter Miri.Verification

namespace DuplicatePrefix.ZeroTail
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

private theorem loadedSome : GeneratedBodySafety.loaded.toOption.isSome = true := by cbv
def program := Miri.Frontend.checkedSome GeneratedBodySafety.loaded.toOption loadedSome

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra
local notation "Config" => ExecutionMachine.Config K U C O X H

def atFrame (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U) : State :=
  ⟨⟨older.push frame⟩, machine⟩

private theorem deadStep (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (block : BasicBlock) (stmt : Statement) (pc : Location) (id : LocalId)
    (old : LocalState Provenance LocalLayout) (updated : Frame) (value : Immediate Provenance)
    (atPC : frame.location = .mir pc) (atBlock : frame.body.basicBlocks[pc.block]? = some block)
    (atStmt : block.statements[pc.statementIndex]? = some stmt)
    (opcode : stmt.kind = .StorageDead id) (nonreturn : id ≠ 0)
    (slot : frame.getLocal id = .ok old) (immediate : old.value = .live (.immediate value))
    (updatedLocal : frame.replaceLocalValue id .dead = .ok updated)
    (keptPC : updated.location = .mir pc) :
    ExecutionMachine.step config limits choice (atFrame older frame machine) =
      (atFrame older {updated with location := .mir ⟨pc.block, pc.statementIndex + 1⟩} machine, .ok true) := by
  rw [ExecutionMachine.step]
  simp only [Step.step, Id.run, pure, Pure.pure, atFrame, Stack.currentFrame?, Array.back?_push,
    atPC, atBlock, atStmt, Step.evalStatement, opcode, ExecutionMachine.stepHooks]
  change Step.finishStatement (older.push frame).size.pred
    (MachineHooks.run (MachineHooks.storageDead (ExecutionMachine.withValidation config limits).lifecycle.storage id)
      (atFrame older frame machine)) = _
  have retired : MachineHooks.run
      (MachineHooks.storageDead (ExecutionMachine.withValidation config limits).lifecycle.storage id)
      (atFrame older frame machine) = (atFrame older updated machine, .ok ()) := by
    simp [MachineHooks.run, Call.run, MachineHooks.storageDead, atFrame, nonreturn,
      MachineHooks.currentFrame, MachineHooks.setCurrentFrame,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      Stack.currentFrame?, slot, immediate, updatedLocal, MonadStateOf.set, set, EStateM.set] <;> rfl
  rw [retired]
  simp [Step.finishStatement, Id.run, atFrame, Stack.currentFrame?, keptPC, Array.set_push] <;> rfl

private def uncheckedTick : Clock.Monotonic H → Clock.Monotonic H
  | .host epoch => .host epoch
  | .virtual time => .virtual (BitVec.ofNat 128 (time.toNat + 5000))

def accounted (hooks : TerminatorMachine.Hooks K U H) (user : U) : U :=
  let control := hooks.getControl user
  let first := {control with basicBlockCount := control.basicBlockCount + 1}
  let second := {first with sinceGc := first.sinceGc + 1}
  hooks.setControl {second with monotonic := uncheckedTick second.monotonic}
    (hooks.setControl second (hooks.setControl first user))

theorem beforeTerminator_fixed (hooks : TerminatorMachine.Hooks K U H)
    (preempt : MachineHooks.M K U Bool) (state : State)
    (lens : ∀ control user, hooks.getControl (hooks.setControl control user) = control)
    (fixed : state.machine.threads.fixedScheduling = true)
    (gc : (hooks.getControl state.machine.user).gcInterval = 0)
    (unchecked : (hooks.getControl state.machine.user).checkedArithmetic = false) :
    TerminatorMachine.beforeTerminatorWithChoice hooks preempt state =
      .ok () {state with machine := {state.machine with user := accounted hooks state.machine.user}} := by
  unfold TerminatorMachine.beforeTerminatorWithChoice
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    unchecked,Bool.false_and,Bool.false_eq_true,↓reduceIte]
  rw [TerminatorMachine.updateControl_eq]
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    lens, unchecked, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [TerminatorMachine.updateControl_eq]
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    lens, gc, UInt32.lt_irrefl, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    TerminatorMachine.maybePreemptWithChoice, fixed, Bool.true_eq_false]
  cases clock : (hooks.getControl state.machine.user).monotonic <;>
    simp [Clock.Monotonic.tick, unchecked, fixed, gc, TerminatorMachine.updateControl_eq, lens, accounted, uncheckedTick,
      clock, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
      EStateM.pure, Except.pure, Except.bind] <;> rfl

private def selectedKind (body : Body) (pc : Location) : Option StatementKind :=
  (body.basicBlocks[pc.block]?).bind fun block =>
    (block.statements[pc.statementIndex]?).map (·.kind)

private theorem zeroDeadNodes :
    selectedKind program.root.body ⟨1, 0⟩ = some (.StorageDead 5) ∧
    selectedKind program.root.body ⟨1, 2⟩ = some (.StorageDead 4) ∧
    selectedKind program.root.body ⟨1, 3⟩ = some (.StorageDead 3) := by cbv

def retired (frame : Frame) (localId : LocalId) (valid : localId < frame.locals.size)
    (next : Location) : Frame :=
  { frame with
    locals := frame.locals.set localId { frame.locals[localId] with value := .dead } valid
    location := .mir next }

private theorem selected_deadStep (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (pc : Location) (id : LocalId) (valid : id < frame.locals.size) (nonreturn : id ≠ 0)
    (value : Immediate Provenance) (immediate : frame.locals[id].value = .live (.immediate value))
    (location : frame.location = .mir pc) (selected : selectedKind frame.body pc = some (.StorageDead id)) :
    ExecutionMachine.step config limits choice (atFrame older frame machine) =
      (atFrame older (retired frame id valid ⟨pc.block, pc.statementIndex + 1⟩) machine, .ok true) := by
  unfold selectedKind at selected
  obtain ⟨block, found, opcode⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨stmt, slot, opcode⟩ := Option.map_eq_some_iff.mp opcode
  let updated := { frame with locals := frame.locals.set id { frame.locals[id] with value := .dead } valid }
  exact deadStep config limits choice older frame machine block stmt pc id frame.locals[id] updated value
    location found slot opcode nonreturn (by simp [Frame.getLocal, valid] <;> rfl)
    immediate (by simp [Frame.replaceLocalValue, valid, updated] <;> rfl) location

/-- Each selected StorageDead in the zero path retains arbitrary allocation,
Tree Borrows and host state when its retired slot is immediate. -/
theorem zeroStorageDead (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (pc : Location) (id : LocalId) (valid : id < frame.locals.size)
    (node : (pc, id) = (⟨1, 0⟩, 5) ∨ (pc, id) = (⟨1, 2⟩, 4) ∨ (pc, id) = (⟨1, 3⟩, 3))
    (value : Immediate Provenance) (immediate : frame.locals[id].value = .live (.immediate value))
    (body : frame.body = program.root.body) (location : frame.location = .mir pc) :
    ExecutionMachine.step config limits choice (atFrame older frame machine) =
      (atFrame older (retired frame id valid ⟨pc.block, pc.statementIndex + 1⟩) machine, .ok true) := by
  have nonreturn : id ≠ 0 := by
    rcases node with h | h | h <;> obtain ⟨_, rfl⟩ := Prod.mk.inj h <;> decide
  have selected : selectedKind frame.body pc = some (.StorageDead id) := by
    rw [body]
    rcases node with h | h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact zeroDeadNodes.1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact zeroDeadNodes.2.1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact zeroDeadNodes.2.2
  exact selected_deadStep config limits choice older frame machine pc id valid nonreturn
    value immediate location selected

private def selectedTerminator (body : Body) (pc : Location) : Option Terminator :=
  (body.basicBlocks[pc.block]?).bind fun block =>
    match block.statements[pc.statementIndex]? with
    | some _ => none
    | none => some block.terminator

private theorem zeroGotoNode :
    (selectedTerminator program.root.body ⟨1, 4⟩).map (·.kind) = some (.Goto 10 #[]) := by
  cbv

/-- The actual zero branch reaches the return block independently of the
memory and borrow state under the fixed, GC-disabled control profile. -/
theorem zeroGoto (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (body : frame.body = program.root.body) (location : frame.location = .mir ⟨1, 4⟩)
    (lens : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control)
    (fixed : machine.threads.fixedScheduling = true)
    (gc : (config.terminators.getControl machine.user).gcInterval = 0)
    (unchecked : (config.terminators.getControl machine.user).checkedArithmetic = false) :
    ExecutionMachine.step config limits choice (atFrame older frame machine) =
      (atFrame older {frame with location := .mir ⟨10, 0⟩}
        {machine with user := accounted config.terminators machine.user}, .ok true) := by
  obtain ⟨term, selected, kind⟩ := Option.map_eq_some_iff.mp zeroGotoNode
  have current : StepWP.currentTerminator (atFrame older frame machine) = some term := by
    simp only [StepWP.currentTerminator, atFrame, Stack.currentFrame?, Array.back?_push,
      location, bind, Bind.bind, Option.bind]
    change selectedTerminator frame.body ⟨1, 4⟩ = some term
    rw [body]
    exact selected
  rw [ExecutionMachine.step, StepWP.step_eq_runTerminator current]
  have hook : (ExecutionMachine.stepHooks config limits).beforeTerminator choice
      (atFrame older frame machine) =
    (atFrame older frame {machine with user := accounted config.terminators machine.user}, .ok ()) := by
    change MachineHooks.run
      (TerminatorMachine.beforeTerminatorWithChoice config.terminators
        ((ExecutionMachine.withValidation config limits).preemptionChoice choice)) _ = _
    unfold MachineHooks.run Call.run
    rw [beforeTerminator_fixed _ _ _ lens fixed gc unchecked]
    rfl
  simp only [Step.runTerminator, hook, Id.run, pure, Pure.pure]
  rw [ExecutionMachine.stepHooks_goto config limits choice term 10 #[] kind]
  simp [ControlFlow.goToBlock, ControlFlow.setLocation, atFrame, Stack.currentFrame?] <;> rfl

/-- Starting after the zero branch stores its Boolean result, the real driver
retires both scalar locals and reaches the selected Return. The only machine
update along these three steps is terminator accounting. -/
theorem zeroCleanup (config : Config) (limits : ExecutionMachine.Limits) (choice : C)
    (older : Array Frame) (frame : Frame) (machine : MachineHooks.MachineState K U)
    (body : frame.body = program.root.body) (location : frame.location = .mir ⟨1, 2⟩)
    (bound : 4 < frame.locals.size) (value4 value3 : Immediate Provenance)
    (slot4 : frame.locals[4].value = .live (.immediate value4))
    (slot3 : (frame.locals[3]'(by omega)).value = .live (.immediate value3))
    (lens : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control)
    (fixed : machine.threads.fixedScheduling = true)
    (gc : (config.terminators.getControl machine.user).gcInterval = 0)
    (unchecked : (config.terminators.getControl machine.user).checkedArithmetic = false) :
    ∃ (middle next returned : Frame),
      ExecutionMachine.step config limits choice (atFrame older frame machine) =
        (atFrame older middle machine, .ok true) ∧
      ExecutionMachine.step config limits choice (atFrame older middle machine) =
        (atFrame older next machine, .ok true) ∧
      ExecutionMachine.step config limits choice (atFrame older next machine) =
        (atFrame older returned {machine with user := accounted config.terminators machine.user}, .ok true) ∧
      returned.body = program.root.body ∧ returned.location = .mir ⟨10, 0⟩ := by
  let middle := retired frame 4 bound ⟨1, 3⟩
  have valid3 : 3 < middle.locals.size := by
    simpa only [middle, retired, Array.size_set] using (show 3 < frame.locals.size by omega)
  let next := retired middle 3 valid3 ⟨1, 4⟩
  have slot : middle.locals[3].value = .live (.immediate value3) := by
    simpa [middle, retired, Array.getElem_set_ne bound (by omega : 3 < frame.locals.size) (by decide : 4 ≠ 3)] using slot3
  exact ⟨middle, next, {next with location := .mir ⟨10, 0⟩},
    zeroStorageDead config limits choice older frame machine ⟨1, 2⟩ 4 bound
      (.inr (.inl rfl)) value4 slot4 body location,
    zeroStorageDead config limits choice older middle machine ⟨1, 3⟩ 3 valid3
      (.inr (.inr rfl)) value3 slot body rfl,
    zeroGoto config limits choice older next machine body rfl lens fixed gc unchecked,
    body, rfl⟩

#print axioms zeroStorageDead
#print axioms zeroGoto
#print axioms zeroCleanup
#print axioms beforeTerminator_fixed

end DuplicatePrefix.ZeroTail

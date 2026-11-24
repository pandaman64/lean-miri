import duplicate_prefix.RootZeroCompletePrefix
import duplicate_prefix.ActiveStackRelease
import ZeroReturn
import ZeroReturnDriver
import ReturnPreOfEffects

namespace DuplicatePrefix.RootZeroShallowReturn
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Memory Miri.Interpreter Miri.Verification
open Miri.TreeBorrows Miri.DataStructures Miri.Concurrency

set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "MachineState" => MachineHooks.MachineState MiriMemoryKind Machine.RootUser
local notation "Frame" => CompilerFrameContext.ActualFrame

abbrev boolLayout := RootCompilerFacts.boolLayout
abbrev trueOp : OpTy Provenance := ⟨.immediate (.scalar (.fromBool true)), boolLayout⟩

def putBool (frame : Frame) (index : Miri.MIR.LocalId) (valid : index < frame.locals.size) : Frame :=
  {frame with locals := (frame.locals.set index
    ⟨.live (.immediate (.scalar (.fromBool true))), frame.locals[index].layout⟩ valid)}

theorem copyReturn (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1)
    (older : Array Frame) (caller : Frame) (machine : MachineState)
    (index : Miri.MIR.LocalId) (valid : index < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[index].value = .live (.immediate old))
    (cached : caller.locals[index].layout = some boolLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    (ExecutionMachine.terminatorHooks config limits).copyReturn () trueOp
      (.frameLocal older.size index none boolLayout caller.localsIdentity)
      (Storage.withCurrent older caller machine) =
      (Storage.withCurrent older (putBool caller index valid) machine, .ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let checked := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks checked).place
  let dest := LocalPlaces.localRuntimePlace older.size caller index boolLayout
  let before := Storage.withCurrent older caller machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : checked.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have padding : checked.copy.hasPadding = CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false := by
    change config.copy.hasPadding = _
    rw [fields.copyPadding, debugOff]
  obtain ⟨primitive, wrap, repr⟩ := CopyCompilerFacts.initialized_scalar_exists boolLayout
    RootGenericBoolWrite.bool_initialized
  have same : checked.copy.compatible boolLayout boolLayout = .ok true := by
    rw [compatible, ScalarCopyStage.same_type_copy]
  have changeTransmute (state : State) :
      copyRuntimePlaceNoValidate place checked.copy () trueOp dest true state =
      copyRuntimePlaceNoValidate place checked.copy () trueOp dest false state := by
    unfold copyRuntimePlaceNoValidate
    unfold_internal ".Interpreter.placeLift"
    simp only [trueOp, dest, LocalPlaces.localRuntimePlace, same, bind, Bind.bind, EStateM.bind, pure, Pure.pure,
      EStateM.pure, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have transmute : copyRuntimePlace place checked.copy () trueOp dest true =
      copyRuntimePlace place checked.copy () trueOp dest false := by
    unfold copyRuntimePlace
    exact congrArg (fun action => action >>= _) (funext changeTransmute)
  have traced := ScalarCopyStage.copy_immediate place checked.copy checked.access PreparedReflection.actual.compiler ()
    boolLayout (.scalar (.fromBool true)) dest rfl _ repr RootGenericBoolWrite.bool_sized compatible padding
    rfl (CanonicalConfigFacts.actual_retain_touched options () (remaining + 1) span)
  have wrote := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff fuel fuelEq
    older caller machine index old true valid live cached noClocks ghost shallow
  change MachineHooks.run (copyRuntimePlace place checked.copy () trueOp dest true) before = _
  rw [transmute, traced]
  change MachineHooks.run
    ((ExecutionMachine.rvalueHooks config limits).writeImmediate () (.scalar (.fromBool true)) dest) before = _
  unfold MachineHooks.run Call.run
  rw [wrote]
  rfl

theorem readReturn (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (older : Array Frame) (callee : Frame) (machine : MachineState)
    (bound : 0 < callee.locals.size)
    (live : callee.locals[0].value = .live (.immediate (.scalar (.fromBool true))))
    (cached : callee.locals[0].layout = some boolLayout) (noClocks : callee.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    (ExecutionMachine.terminatorHooks config limits).returnOperand () (Storage.withCurrent older callee machine) =
      (Storage.withCurrent older callee machine, .ok trueOp) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let checked := ExecutionMachine.withValidation config limits
  let before := Storage.withCurrent older callee machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have slot : callee.getLocal 0 = .ok callee.locals[0] := by simp [Frame.getLocal, bound] <;> rfl
  have operand : callee.getLocalOperand 0 = .ok (.immediate (.scalar (.fromBool true))) := by
    simp [Frame.getLocalOperand, slot, live, bind, Bind.bind, Except.bind, pure, Pure.pure,
      Except.pure, LocalState.access, Except.mapError]
  change MachineHooks.run (config.projection.place.localToOp () 0) before = _
  rw [fields.projectionLocalToOp]
  simp [MachineHooks.run, Call.run, PlaceMachine.localToOp, PlaceMachine.localToOpCore,
    PlaceMachine.layoutLocal, MachineHooks.currentFrame, Stack.currentFrame?, slot, operand,
    MachineHooks.afterLocalRead, noClocks, cached, RootGenericBoolWrite.bool_sized, boolLayout, before,
    Storage.withCurrent, ValidityMachine.compilerPolicy, ValidityMachine.validationInProgress, ghost,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get] <;> rfl

/-- The return destination, allocation, and protector law are independent of
control execution. All byte ranges of the protected slice allocation must
admit the source release from the installed protector. -/
structure ActiveCaller (older : Array Frame) (caller callee : Frame)
    (machine : MachineState) where
  target : BasicBlockId
  unwind : UnwindAction
  continuation : callee.returnContinuation = .goto (some target) unwind
  destinationIndex : Miri.MIR.LocalId
  destinationBound : destinationIndex < caller.locals.size
  destinationSlot : Immediate Provenance
  destinationLive : caller.locals[destinationIndex].value = .live (.immediate destinationSlot)
  destinationCached : caller.locals[destinationIndex].layout = some boolLayout
  destination : callee.returnPlace =
    .frameLocal older.size destinationIndex none boolLayout caller.localsIdentity
  callerClocks : caller.extra.dataRace = none
  varargs : callee.vaList = #[]
  id : AllocId
  tag : BorTag
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  present : machine.memory.live[id]? = some entry
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker = some tracker
  owned : FrameState
  ownership : callee.extra.borrowTracker = some owned
  ownedTags : owned.protectedTags = #[(id, tag)]
  source : UniIndex
  root : UniIndex
  indexed : entry.allocation.extra.indexOfTag tag = some source
  roots : entry.allocation.extra.roots = #[root]
  depth : GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes
  children : GeneralBorrowGraph.ChildNodes entry.allocation.extra
  node : TreeNode
  found : entry.allocation.extra.nodeAt source = some node
  unexposed : node.isExposed = false
  authorized : ∀ position < entry.allocation.extra.locations.entries.size, ∃ slot,
    entry.allocation.extra.locations.index position = .ok slot ∧
      ActiveRelease.ReleaseOwnership entry.allocation.extra source root tracker.global.protectedTags slot
  thread : ThreadRecord
  relevant : Nat
  active : machine.threads.activeThread? = some thread
  relevance : FrameRelevance.top ⟨(older.push caller).push callee⟩
    thread.topUserRelevantFrame = some relevant

private theorem returnBytecode :
    (RootBody.reflected.body.body.basicBlocks[10]?).map
      (fun block => (block.statements.size, block.terminator.kind, block.cleanup)) =
        some (0, .Return, false) := by rfl

theorem stepReturnToCaller (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1)
    (older : Array Frame) (caller callee : Frame) (machine : MachineState)
    (ready : ActiveCaller older caller callee machine)
    (body : callee.body = RootBody.reflected.body.body) (position : callee.location = .mir ⟨10, 0⟩)
    (bound : 0 < callee.locals.size)
    (live : callee.locals[0].value = .live (.immediate (.scalar (.fromBool true))))
    (cached : callee.locals[0].layout = some boolLayout) (clocks : callee.extra.dataRace = none)
    (immediate : ZeroImmediateFacts.AllImmediate callee)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ poppedMachine : MachineState,
      ExecutionMachine.step config limits () (Storage.withCurrent (older.push caller) callee machine) =
        (Storage.withCurrent older {putBool caller ready.destinationIndex ready.destinationBound with
          location := .mir ⟨ready.target, 0⟩} poppedMachine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let checked := ExecutionMachine.withValidation config limits
  let ticked := RootZeroCompleteState.tick options remaining span machine
  let before := Storage.withCurrent (older.push caller) callee ticked
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have postGhost := (RootZeroCompleteState.tick_ghost options remaining span machine).trans ghost
  have postShallow := (RootZeroCompleteState.tick_shallow options remaining span machine).trans shallow
  obtain ⟨pointers, table, globals, choice, retagHooks, _, _, ens, sync⟩ := fields.retagConstruction
  let retag := TypedMachineBindings.retagHooks checked.access checked.retag
  have ensure : retag.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals := by
    change config.retag.ensureTreeExtra = _
    rw [retagHooks]
    exact ens
  have synchronize : globals.synchronizeMemory ticked.memory ⟨ticked, none⟩ = ⟨ticked, none⟩ := by
    rw [sync]
  obtain ⟨popped, sameUser, released⟩ := ActiveRelease.popOfOwnership .global globals retag ensure
    ready.id ready.tag (older.push caller) callee ticked ready.entry ready.present synchronize ready.tracker
    ready.tracked ready.owned ready.ownership ready.ownedTags ready.source ready.root ready.indexed ready.roots
    ready.depth ready.children ready.node ready.found ready.unexposed ready.authorized ready.thread ready.relevant
    ready.active ready.relevance
  have released' (finish : Frame → State → Prop) (failure : StepError → State → Prop) :
      ProtectorReleaseWP.popRawPre (TypedMachineBindings.retagHooks
        (ExecutionMachine.withValidation config limits).access (ExecutionMachine.withValidation config limits).retag)
        finish failure (Storage.withCurrent (older.push caller) callee ticked) ↔
      finish callee (Storage.withCurrent older caller popped) :=
    released finish failure
  let after := Storage.withCurrent older
    {putBool caller ready.destinationIndex ready.destinationBound with location := .mir ⟨ready.target, 0⟩} popped
  refine ⟨popped, ?_⟩
  let post : Bool → State → Prop := fun more state => more = true ∧ state = after
  let failed : StepError → State → Prop := fun _ _ => False
  have code := returnBytecode
  obtain ⟨block, found, clean, opcode, selected⟩ :=
    ZeroTail.selectZeroReturn (older.push caller) callee machine position (by simpa only [body] using code)
  have lens : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control := by
    rw [fields.terminators]
    intros
    rfl
  have driver := ZeroTail.returnDriverPre config limits () (older.push caller) callee machine block.terminator
    selected opcode lens fixed gc unchecked post failed
  have read := readReturn options limits remaining span (older.push caller) callee ticked bound live cached clocks postGhost
  have copied := copyReturn options limits remaining span debugOff fuel fuelEq older caller popped
    ready.destinationIndex ready.destinationBound ready.destinationSlot ready.destinationLive ready.destinationCached
    ready.callerClocks (sameUser.symm ▸ postGhost) (sameUser.symm ▸ postShallow)
  obtain ⟨unwind, afterPop⟩ := fields.lifecycleAfterPop
  have cleaned := ZeroBoolean.cleanupImmediate checked.lifecycle unwind () callee ready.target ready.unwind
    ready.continuation ready.varargs
    (fun slot member => immediate slot (by simpa using member)) afterPop
    (Storage.withCurrent older (putBool caller ready.destinationIndex ready.destinationBound) popped)
  have copied' : (ExecutionMachine.terminatorHooks config limits).copyReturn () trueOp callee.returnPlace
        (Storage.withCurrent older caller popped) =
      (Storage.withCurrent older (putBool caller ready.destinationIndex ready.destinationBound) popped, .ok ()) := by
    rw [ready.destination]
    exact copied
  have contract := ZeroBoolean.returnPreOfEffects config limits () older caller callee
    (putBool caller ready.destinationIndex ready.destinationBound) ticked popped trueOp block ⟨10, 0⟩ position
    found clean ready.target ready.unwind ready.continuation read copied' cleaned released' (post true) failed
  have ok : CanonicalStepWP.returnPre config limits () false (post true) failed before :=
    contract.mpr ⟨rfl, rfl⟩
  have sameTick : {machine with user := ZeroTail.accounted config.terminators machine.user} = ticked := by
    unfold ticked RootZeroCompleteState.tick SourceControl.accounted ZeroTail.accounted
    rw [fields.terminators]
    rfl
  rw [sameTick] at driver
  have step := driver.mpr ok
  change ExecutionMachine.step config limits () (Storage.withCurrent (older.push caller) callee machine) = (after, .ok true)
  rcases ran : ExecutionMachine.step config limits () (Storage.withCurrent (older.push caller) callee machine) with ⟨result, answer⟩
  change InstructionWP.resultPre post failed
    (ExecutionMachine.step config limits () (Storage.withCurrent (older.push caller) callee machine)) at step
  rw [ran] at step
  cases answer with
  | error => exact (show False from step).elim
  | ok more =>
    obtain ⟨rfl, rfl⟩ := (show more = true ∧ result = after from step)
    rfl

/-- Prepared zero-count local state, with source body identity and the ordinary
immediate locals installed for the entry block. -/
structure ZeroEntry (frame : Frame) (machine : MachineState) where
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  location : frame.location = .mir ⟨0, 0⟩
  size : frame.locals.size = 25
  live0 : (frame.locals[0]'(by rw [size]; decide)).value = .live (.immediate .uninit)
  uncached0 : (frame.locals[0]'(by rw [size]; decide)).layout = none
  dead3 : (frame.locals[3]'(by rw [size]; decide)).value = .dead
  dead4 : (frame.locals[4]'(by rw [size]; decide)).value = .dead
  dead5 : (frame.locals[5]'(by rw [size]; decide)).value = .dead
  uncached4 : (frame.locals[4]'(by rw [size]; decide)).layout = none
  uncached5 : (frame.locals[5]'(by rw [size]; decide)).layout = none
  zero : (frame.locals[2]'(by rw [size]; decide)).value =
    .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0))))
  cached2 : (frame.locals[2]'(by rw [size]; decide)).layout = some RootCompilerFacts.usizeLayout
  noClocks : frame.extra.dataRace = none
  immediate : ZeroImmediateFacts.AllImmediate frame
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  fixed : machine.threads.fixedScheduling = true

def ActiveCaller.afterPrefix (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    {older : Array Frame} {caller frame result : Frame} {machine : MachineState}
    (ready : ActiveCaller older caller frame machine)
    (extra : result.extra = frame.extra) (place : result.returnPlace = frame.returnPlace)
    (resume : result.returnContinuation = frame.returnContinuation)
    (varargs : result.vaList = frame.vaList) :
    ActiveCaller older caller result
      (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)) :=
  { ready with continuation := resume.trans ready.continuation
               destination := place.trans ready.destination
               varargs := varargs.trans ready.varargs
               ownership := by rw [extra]; exact ready.ownership
               relevance := by simpa only [FrameRelevance.top, Array.isEmpty_push, Bool.false_eq_true,
                 ↓reduceIte, Array.size_push] using ready.relevance }

theorem executesZeroReturn (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1)
    (older : Array Frame) (caller frame : Frame) (machine : MachineState)
    (entry : ZeroEntry frame machine) (ready : ActiveCaller older caller frame machine)
    (defaultMode : ready.tracker.retagMode = .Default)
    (gc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent (older.push caller) frame machine
    ∃ final, SuccessfulTrace.Trace config limits before final ∧ final.stack.frames.size < before.stack.frames.size := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let olderFrames := older.push caller
  obtain ⟨result, trace, body, identity, instanceEq, extra, destination, continuation, varargs, localsId, size,
      location, slot, immediate⟩ := RootZeroCompletePrefix.reaches_return options limits remaining span source debugOff
    fuel fuelEq olderFrames frame machine entry.body entry.identity entry.callee entry.location entry.size
    entry.live0 entry.uncached0 entry.dead3 entry.dead4 entry.dead5 entry.uncached4 entry.uncached5
    entry.zero entry.cached2 entry.noClocks entry.immediate ready.tracker ready.tracked defaultMode
    entry.ghost entry.shallow unchecked gc entry.fixed
  let first := RootZeroCompleteState.tick options remaining span machine
  let second := RootZeroCompleteState.tick options remaining span first
  let finalReady := ready.afterPrefix options remaining span extra destination continuation varargs
  have bound : 0 < result.locals.size := by rw [size]; decide
  have localSlot : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))), some boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans slot)
  have ghost : second.user.payload.ghost = false :=
    (RootZeroCompleteState.tick_ghost options remaining span first).trans
      ((RootZeroCompleteState.tick_ghost options remaining span machine).trans entry.ghost)
  have shallow : second.user.payload.validation = .Shallow :=
    (RootZeroCompleteState.tick_shallow options remaining span first).trans
      ((RootZeroCompleteState.tick_shallow options remaining span machine).trans entry.shallow)
  have flagsFirst := RootZeroCompleteState.tick_flags options remaining span machine
  have flagsSecond := RootZeroCompleteState.tick_flags options remaining span first
  obtain ⟨popped, last⟩ := stepReturnToCaller options limits remaining span debugOff fuel fuelEq
    older caller result second finalReady (body.trans entry.body) location bound (congrArg (·.value) localSlot)
    (congrArg (·.layout) localSlot) (congrArg (·.dataRace) extra |>.trans entry.noClocks) immediate
    ghost shallow entry.fixed (flagsSecond.2.trans (flagsFirst.2.trans gc))
    (flagsSecond.1.trans (flagsFirst.1.trans unchecked))
  refine ⟨_, SuccessfulTrace.append trace (.next last (.refl _)), ?_⟩
  simp [Storage.withCurrent]

#print axioms executesZeroReturn
#print axioms stepReturnToCaller
#print axioms copyReturn
#print axioms readReturn
end DuplicatePrefix.RootZeroShallowReturn

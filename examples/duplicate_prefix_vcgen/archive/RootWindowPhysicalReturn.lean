import duplicate_prefix.PhysicalBoolWindowActual
import duplicate_prefix.PtrMetadataReturn

namespace DuplicatePrefix.RootWindowPhysicalReturn

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open SourceDomain ArchiveForestProjection GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual outer Return consumes the structural release plan, then stores
the Boolean at the original concrete return pointer, including an interior
offset in a larger allocation. The following step is the real stop. -/
theorem return_step_terminal (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (limits : ExecutionMachine.Limits)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (debugOff : options.place.debugAssertions = false)
    (frame : CompilerFrameContext.ActualFrame) (initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (charged : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (chargedEq : charged = PtrMetadataReturn.accountedMachine options remaining span initial)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initial.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initial.user).gcInterval = 0)
    (fixed : initial.threads.fixedScheduling = true)
    (tracker : MachineHooks.BorrowState) (owned : FrameState)
    (enabled : charged.borrowTracker = some tracker) (ledger : frame.extra.borrowTracker = some owned)
    (released : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags owned.protectedTags.toList charged.memory released)
    (thread : ThreadRecord) (active : charged.threads.activeThread? = some thread)
    (result : CanonicalConfigFacts.RootState)
    (resultEq : result = ⟨⟨#[]⟩, GenericPopFrame.afterRelevanceAt #[] frame
      (ActualPopPlan.released charged released tracker owned) (thread.topUserRelevantFrame.getD 0)⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : 0 < frame.locals.size) (value : Bool)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (noLocalClocks : frame.extra.dataRace = none) (beforeGhost : charged.user.payload.ghost = false)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance) (window : PhysicalBoolWindowWrite.Window result.machine place)
    (destination : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (newTracker : MachineHooks.BorrowState) (activeTracker : result.machine.borrowTracker = some newTracker)
    (noClocks : result.machine.dataRace = none) (noBackend : result.machine.user.payload.payload.user.backend = .none)
    (ghost : result.machine.user.payload.ghost = false) (shallow : result.machine.user.payload.validation = .Shallow)
    (source root : UniIndex) (node : TreeNode) (found : window.entry.allocation.extra.nodeAt source = some node)
    (key : window.entry.allocation.extra.indexOfTag window.tag = some source)
    (roots : window.entry.allocation.extra.roots = #[root])
    (coherent : CoherentForest window.entry.allocation.extra)
    (treeBounds : window.offset.toNat + 1 ≤ window.entry.allocation.extra.locations.size.bytes.toNat)
    (owners : OwnedOn (fun row => LocationRights window.entry.allocation.extra row newTracker.global.protectedTags source)
      window.offset (window.offset+1) window.entry.allocation.extra.locations)
    (extras : let context := (DuplicatePrefixPhysicalContexts.canonical options remaining span).writeContext
      (context.extras.get result.machine.user).allocations.find? (fun row => row.1 == window.id) =
        some (window.id,{weakMemory := none, backtrace := (AllocationBacktrace.get
          ((context.extras.get result.machine.user).allocations) window.id)}))
    (addressBound : place.mplace.ptr.offset.bytes.toNat + 1 < 2^64) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ updated,
      let finish := CanonicalCopy.replaceAllocation result window.id window.entry.kind updated
      ExecutionMachine.step config limits () (Storage.withCurrent #[] frame initial) = (finish,.ok true) ∧
      ExecutionMachine.step config limits () finish = (finish,.ok false) ∧
      updated.byteSize = window.entry.allocation.byteSize ∧ updated.len = window.entry.allocation.len ∧
      updated.mutability = .Mut := by
  intro config
  let control := GenericCallReturn.sourceControl config limits
  let before := Storage.withCurrent #[] frame charged
  let start := Storage.withCurrent #[] frame initial
  let operand : OpTy Provenance := ⟨.immediate (.scalar (.fromBool value)),RootCompilerFacts.boolLayout⟩
  have read : control.returnOperand () before = (before,.ok operand) :=
    PrimitiveCallReturn.read_current_return options limits (remaining+1) span #[] frame charged
      RootCompilerFacts.boolLayout (.scalar (.fromBool value)) valid0 live0 cached0 (by decide +kernel)
      noLocalClocks beforeGhost
  have pop : control.popFrame () before = (result,.ok frame) := by
    rw [resultEq]
    exact ActualPopPlan.pop_of_plan options limits (remaining+1) span #[] frame charged tracker owned
      enabled ledger released plan thread active
  obtain ⟨updated, copied, size, length, mutable⟩ :=
    PhysicalBoolWindowActual.copy_return options remaining span limits fuel debugOff validationFuel result place window
      value newTracker activeTracker noClocks noBackend ghost shallow source root node found key roots coherent
      treeBounds owners extras addressBound frame.returnPlace destination
  let after := CanonicalCopy.replaceAllocation result window.id window.entry.kind updated
  have cleanup := RootPhysicalReturnSupport.cleanup_actual_stop options limits (remaining+1) span after frame continuation immediateLocals varargs
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [body]; simp [block]
  have normal : block.cleanup = false := by with_unfolding_all rfl
  have empty : after.stack.frames = #[] := by rw [show after.stack.frames = result.stack.frames from rfl,resultEq]
  have returned := RootPhysicalReturnSupport.normal_stop control () before before result after frame ⟨10,0⟩ block operand
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt normal read pop copied cleanup continuation empty
  have accounting := SourceControl.before_terminator config limits () start
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounted : (ExecutionMachine.stepHooks config limits).beforeTerminator () start = (before,.ok ()) := by
    dsimp only [before]
    rw [chargedEq]
    exact accounting
  have noStatement : block.statements[0]? = none := by with_unfolding_all rfl
  have kind : block.terminator.kind = .Return := by with_unfolding_all rfl
  have actual := GenericCallReturn.return_step_exact config limits () start before after frame ⟨10,0⟩ block
    (by simp [start,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement kind accounted returned
  have terminal (state : CanonicalConfigFacts.RootState) (noFrames : state.stack.frames = #[]) :
      ExecutionMachine.step config limits () state = (state,.ok false) := by
    obtain ⟨⟨frames⟩,machine⟩ := state
    change frames = #[] at noFrames
    subst frames
    exact RootActualPhysicalReturn.terminal_empty config limits () machine
  have stopped := terminal after empty
  exact ⟨updated,actual,stopped,size,length,mutable⟩

end DuplicatePrefix.RootWindowPhysicalReturn

#print axioms DuplicatePrefix.RootWindowPhysicalReturn.return_step_terminal

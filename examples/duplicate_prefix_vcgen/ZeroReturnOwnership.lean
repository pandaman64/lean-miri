import duplicate_prefix.ActiveStackRelease
import ZeroReturn

namespace DuplicatePrefix.ZeroBoolean
open Miri.Concurrency Miri.DataStructures Miri.Interpreter Miri.Memory Miri.MIR
  Miri.TreeBorrows Miri.Verification

variable {K U C O X H : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- Source Return discharges its release from structural Tree Borrows
ownership, writes the Boolean result, and resumes the caller. -/
theorem normalReturnFromOwnership (config : ExecutionMachine.Config K U C O X H)
    (limits : ExecutionMachine.Limits) (choice : C) (layout : LocalLayout)
    (unwind : Unwind.Hooks K U C O)
    (afterPop : (ExecutionMachine.withValidation config limits).lifecycle.afterPop =
      fun c frame unwinding => Unwind.afterStackPop unwind c frame.extra unwinding)
    (older : Array Frame) (caller callee : Frame)
    (beforePop : MachineHooks.MachineState K U)
    (profile : BooleanLocalProfile config limits choice layout beforePop)
    (callerProfile : ∀ machine : MachineHooks.MachineState K U, machine.user = beforePop.user →
      BooleanLocalProfile config limits choice layout machine)
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
    (kind : K)
    (hooks : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (ensure : (ExecutionMachine.withValidation config limits).retag.ensureTreeExtra =
      GlobalAllocationMachine.ensure kind hooks)
    (id : AllocId) (tag : BorTag)
    (entry : LocalAllocation Provenance BorrowTree K)
    (present : beforePop.memory.live[id]? = some entry)
    (synchronize : hooks.synchronizeMemory beforePop.memory ⟨beforePop, none⟩ = ⟨beforePop, none⟩)
    (tracker : MachineHooks.BorrowState) (tracked : beforePop.borrowTracker = some tracker)
    (owned : FrameState) (ownership : callee.extra.borrowTracker = some owned)
    (ownedTags : owned.protectedTags = #[(id, tag)])
    (source root : UniIndex) (index : entry.allocation.extra.indexOfTag tag = some source)
    (roots : entry.allocation.extra.roots = #[root])
    (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth entry.allocation.extra.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes entry.allocation.extra)
    (node : TreeNode) (found : entry.allocation.extra.nodeAt source = some node)
    (unexposed : node.isExposed = false)
    (authorized : ∀ position < entry.allocation.extra.locations.entries.size, ∃ slot,
      entry.allocation.extra.locations.index position = .ok slot ∧
        ActiveRelease.ReleaseOwnership entry.allocation.extra source root tracker.global.protectedTags slot)
    (thread : ThreadRecord) (relevant : Nat)
    (active : beforePop.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨(older.push caller).push callee⟩ thread.topUserRelevantFrame = some relevant) :
    ∃ afterPopMachine : MachineHooks.MachineState K U, afterPopMachine.user = beforePop.user ∧
      ∀ post : State → Prop, ∀ failure : StepError → State → Prop,
    CanonicalStepWP.returnPre config limits choice false post failure (atFrame (older.push caller) callee beforePop) ↔
      post (atFrame older {setTrue caller callerBound with location := .mir ⟨target, 0⟩} afterPopMachine) := by
  let checked := ExecutionMachine.withValidation config limits
  let retag := TypedMachineBindings.retagHooks checked.access checked.retag
  obtain ⟨popped, user, released⟩ := ActiveRelease.popOfOwnership kind hooks retag ensure id tag
    (older.push caller) callee beforePop entry present synchronize tracker tracked owned ownership ownedTags
    source root index roots depth children node found unexposed authorized thread relevant active top
  refine ⟨popped, user, ?_⟩
  intro post failure
  exact normalReturnToCaller config limits choice layout unwind afterPop older caller callee beforePop popped
    profile (callerProfile popped user) block pc location located normal target action continues destination
    noVarargs immediate calleeBound calleeLive calleeCached calleeNoRace reader callerBound callerOld
    callerLive callerNoRace released post failure

#print axioms normalReturnFromOwnership
end DuplicatePrefix.ZeroBoolean

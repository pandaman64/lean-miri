import Miri.Verification.MutableRetagRights
import Miri.Interpreter.GlobalAllocationMachine

namespace Miri.Verification.MutableTypedRetag

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory
open Miri.TreeBorrows Miri.TreeBorrows.RetagPolicy Miri.Verification Std.WP
open Miri.Interpreter.TypedRetag

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "BorrowFrame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- The source protector registration updates both the global tag index and
the frame's ownership ledger. -/
def withStrongProtector (before : State) (location : RetagPipeline.ResolvedLocation)
    (tag : BorTag) (frame : BorrowFrame) (borrowFrame : FrameState)
    (tracker : MachineHooks.BorrowState) : State :=
  let (global, borrowFrame) := tracker.global.addProtector borrowFrame location.allocId tag .StrongProtector
  { before with
    machine := {before.machine with borrowTracker := some {tracker with global}}
    stack := ⟨before.stack.frames.pop.push
      {frame with extra := {frame.extra with borrowTracker := some borrowFrame}}⟩ }

/-- Both ownership records are visible in the actual post-registration state. -/
theorem register_strong (location : RetagPipeline.ResolvedLocation)
    (policy : NewPermission) (tag : BorTag) (before : State)
    (frame : BorrowFrame) (borrowFrame : FrameState) (borrow : MachineHooks.BorrowState)
    (selected : policy.protector = some .StrongProtector)
    (current : before.stack.currentFrame? = some frame)
    (frameLedger : frame.extra.borrowTracker = some borrowFrame)
    (tracked : before.machine.borrowTracker = some borrow) :
    TypedRetagWP.registerProtector location policy tag before =
      .ok () (withStrongProtector before location tag frame borrowFrame borrow) := by
  have nonempty : before.stack.frames.isEmpty = false := by
    cases empty : before.stack.frames.isEmpty with
    | false => rfl
    | true =>
      have none : before.stack.frames.back? = none :=
        Array.back?_eq_none_iff.mpr (Array.isEmpty_iff.mp empty)
      simp [Stack.currentFrame?, none] at current
  have hasFrames : before.stack.frames ≠ #[] := fun empty => by simp [empty] at nonempty
  simp [TypedRetagWP.registerProtector, selected, MachineHooks.currentFrame, current, frameLedger,
    tracker_apply, tracked, withStrongProtector, MachineHooks.setCurrentFrame, hasFrames, modify, modifyGet,
    get, getThe, MonadStateOf.get, set, MonadStateOf.set, MonadStateOf.modifyGet, EStateM.get, EStateM.set, EStateM.modifyGet,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- The actual retag write-back changes only the live allocation's Tree
Borrows extra. -/
def withTree (before : State) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) : State :=
  {before with machine := {before.machine with memory :=
    {before.machine.memory with live := (before.machine.memory.live.insert id
      {entry with allocation := entry.allocation.setExtra tree})}}}

theorem withTree_live [DecidableEq K] (before : State) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) :
    (withTree before id entry tree).machine.memory.live[id]? =
      some {entry with allocation := entry.allocation.setExtra tree} := by
  simp [withTree]

/-- A concrete typed reborrow of a live allocation executes its compiler
checks and protector installation before the actual permission/child stages. -/
theorem live_reborrow [DecidableEq K] (hooks : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag)
    (location : RetagPipeline.ResolvedLocation) (before pointed resolved logged registered : State)
    (inside : DedupRangeMap Tree.LocationState) (entry : LocalAllocation Provenance BorrowTree K)
    (post : Option Provenance → State → Prop)
    (check : hooks.checkPtrAccess place.mplace.ptr size before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place size policy tag (some location) resolved = .ok () logged)
    (register : TypedRetagWP.registerProtector location policy tag logged = .ok () registered)
    (live : registered.machine.memory.live[location.allocId]? = some entry)
    (permissions : insidePermissions hooks budget place size policy registered = .ok inside registered)
    (ensure : hooks.ensureTreeExtra location.allocId registered = .ok () registered)
    (segments : TypedRetagWP.segmentsPre location policy tag inside
      (post (some (.concrete location.allocId tag))) (fun _ _ => False) inside.iterAll.toList registered) :
    wp (reborrow hooks budget place size policy tag) post (fun _ _ => False) before := by
  rw [← TypedRetagWP.reborrowPre_iff]
  simp only [TypedRetagWP.reborrowPre, TypedRetagWP.effectPre, check, resolve]
  change TypedRetagWP.effectPre (hooks.logCreation place size policy tag (some location)) (fun _ =>
    TypedRetagWP.effectPre (TypedRetagWP.registerProtector location policy tag) (fun _ state =>
      TypedRetagWP.effectPre (checked "allocation kind" (state.machine.memory.getAllocInfo location.allocId))
        (fun info state =>
          if info.kind != .liveData then
            if size.bytes != 0 then False else post (some (.concrete location.allocId tag)) state
          else
            TypedRetagWP.effectPre (insidePermissions hooks budget place size policy) (fun inside =>
              TypedRetagWP.effectPre (hooks.ensureTreeExtra location.allocId) (fun _ =>
                TypedRetagWP.segmentsPre location policy tag inside (post (some (.concrete location.allocId tag)))
                  (fun _ _ => False) inside.iterAll.toList) (fun _ _ => False)) (fun _ _ => False) state)
        (fun _ _ => False) state) (fun _ _ => False)) (fun _ _ => False) resolved
  have info : registered.machine.memory.getAllocInfo location.allocId =
      .ok ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo, live, pure, Except.pure]
  simpa only [TypedRetagWP.effectPre, log, register, info, checked, pure, Pure.pure, EStateM.pure,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, permissions, ensure] using segments

/-- Race bookkeeping follows the source retag's associated access. -/
def retagRace (id : AllocId) (kind : AccessKind) (offset length : Size) : MachineHooks.M K U Unit := do
  if length.bytes != 0 then
    match kind with
    | .Read => MachineHooks.memoryRaceRead id (allocRange offset length) .Retag
    | .Write => MachineHooks.memoryRaceWrite id (allocRange offset length) .Retag

theorem retagRace_disabled (id : AllocId) (kind : AccessKind) (offset length : Size) (before : State)
    (raceOff : before.machine.dataRace = none) :
    retagRace id kind offset length before = .ok () before := by
  cases kind <;> by_cases empty : length.bytes = 0 <;>
    simp [retagRace, empty, MachineHooks.memoryRaceRead, MachineHooks.memoryRaceWrite,
      MachineHooks.memoryRaceAccess, Id.run, raceOff, get, getThe, MonadStateOf.get, set, MonadStateOf.set,
      EStateM.get, EStateM.set, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

private theorem race_machine_keeps (before : MachineHooks.MachineState K U) (id : AllocId)
    (range : AllocRange) (write : Option Miri.Concurrency.NaWriteType)
    (read : Miri.Concurrency.NaReadType) :
    let after := (MachineHooks.memoryRaceAccess before id range write read).1
    after.memory = before.memory ∧ after.borrowTracker = before.borrowTracker := by
  unfold MachineHooks.memoryRaceAccess
  simp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  repeat' first
    | exact ⟨rfl, rfl⟩
    | split

/-- Either read- or write-associated race bookkeeping keeps the retagged
allocation and both ownership ledgers. -/
theorem retagRace_keeps (id : AllocId) (kind : AccessKind) (offset length : Size) (before raced : State)
    (race : retagRace id kind offset length before = .ok () raced) :
    raced.machine.memory = before.machine.memory ∧
      raced.machine.borrowTracker = before.machine.borrowTracker ∧ raced.stack = before.stack := by
  by_cases empty : length.bytes = 0
  · simp [retagRace, empty, pure, Pure.pure, EStateM.pure] at race
    subst raced
    exact ⟨rfl, rfl, rfl⟩
  · let result := MachineHooks.memoryRaceAccess before.machine id (allocRange offset length)
      (if kind == .Write then some .Retag else none) (if kind == .Read then .Retag else .Read)
    have kept := race_machine_keeps before.machine id (allocRange offset length)
      (if kind == .Write then some .Retag else none) (if kind == .Read then .Retag else .Read)
    have action : retagRace id kind offset length before =
        match result.2 with
        | .ok () => .ok () {before with machine := result.1}
        | .error err => .error err {before with machine := result.1} := by
      cases kind <;>
        simp [retagRace, empty, result, MachineHooks.memoryRaceRead, MachineHooks.memoryRaceWrite,
          get, getThe, MonadStateOf.get, set, MonadStateOf.set, EStateM.get, EStateM.set,
          bind, Bind.bind, EStateM.bind, pure, Pure.pure, throw, throwThe,
          MonadExceptOf.throw] <;> split <;> simp_all only [EStateM.pure, EStateM.throw]
    rw [action] at race
    cases outcome : result.2 with
    | error error => simp [outcome] at race
    | ok value =>
      cases value
      simp only [outcome, EStateM.Result.ok.injEq, true_and] at race
      subst raced
      exact ⟨kept.1, kept.2, rfl⟩

private def requireMutable (id : AllocId) (kind : AccessKind) : MachineHooks.M K U Unit := do
  if kind == .Write then
    let some entry := (← get).machine.memory.live[id]?
      | throw (.invalidProgram "missing live allocation mutability")
    if entry.allocation.mutability == .Not then throw .retagWriteToReadOnly

private theorem requireMutable_live (id : AllocId) (kind : AccessKind) (before : State)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.machine.memory.live[id]? = some entry)
    (mutable : entry.allocation.mutability = .Mut) :
    requireMutable id kind before = .ok () before := by
  cases kind <;> simp [requireMutable, live, mutable, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- Install the exact tree produced by the parent operation before applying
its race action. The operation's completion is obtained from a Tree Borrows
permission theorem on the unchanged allocation entry. -/
theorem segment_of_parent_access [DecidableEq K] (location : RetagPipeline.ResolvedLocation)
    (segment : RangeMapSegment Tree.LocationState)
    (offset : Size) (kind : AccessKind) (before raced : State)
    (entry : LocalAllocation Provenance BorrowTree K) (borrow : MachineHooks.BorrowState)
    (next : State → Prop)
    (live : before.machine.memory.live[location.allocId]? = some entry)
    (tracked : before.machine.borrowTracker = some borrow)
    (mutable : entry.allocation.mutability = .Mut)
    (access : segment.data.permission.associatedAccess = some kind)
    (placed : Size.add location.baseOffset (Size.ofBytes segment.range.start) = .ok offset)
    (completed : (entry.allocation.extra.performBorrowAccessRange location.parentProvenance offset
      (Size.ofBytes (segment.range.stop - segment.range.start)) kind borrow.global.protectedTags
      .VisitChildrenOfAccessed).status = .Completed)
    (race : let length := Size.ofBytes (segment.range.stop - segment.range.start)
      let result := entry.allocation.extra.performBorrowAccessRange location.parentProvenance offset length
        kind borrow.global.protectedTags .VisitChildrenOfAccessed
      retagRace location.allocId kind offset length (withTree before location.allocId entry result.tree) =
        .ok () raced)
    (continues : next raced) :
    TypedRetagWP.segmentPre location segment next (fun _ _ => False) before := by
  unfold TypedRetagWP.segmentPre
  rw [access]
  change TypedRetagWP.effectPre (requireMutable location.allocId kind) (fun _ =>
    TypedRetagWP.effectPre
      (checked "reborrow offset" (Size.add location.baseOffset (Size.ofBytes segment.range.start)))
      (fun offset => let length := Size.ofBytes (segment.range.stop - segment.range.start)
        TypedRetagWP.parentAccessPre location offset length kind
          (TypedRetagWP.effectPre (retagRace location.allocId kind offset length) (fun _ => next) (fun _ _ => False))
          (fun _ _ => False))
      (fun _ _ => False)) (fun _ _ => False) before
  have writable := requireMutable_live location.allocId kind before entry live mutable
  simp only [withTree, tracked] at race
  simpa only [TypedRetagWP.effectPre, writable, placed, checked, pure, Pure.pure, EStateM.pure,
    TypedRetagWP.parentAccessPre, getTree_apply, tracker_apply, live, tracked, TreeBorrowsWP.accessPre_iff,
    completed, updateTree_apply, MemoryState.setLiveAllocation_of_find _ _ _ _ live, race]
    using continues

/-- A cached local allocation is returned directly by the real ensure hook.
The supplied synchronize equation is definitional for the source hook set. -/
theorem ensure_live [DecidableEq K] (globalKind : K)
    (hooks : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (id : AllocId) (before : State) (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.machine.memory.live[id]? = some entry)
    (sync : hooks.synchronizeMemory before.machine.memory ⟨before.machine, none⟩ =
      ⟨before.machine, none⟩) :
    GlobalAllocationMachine.ensure globalKind hooks id before = .ok () before := by
  simp [GlobalAllocationMachine.ensure, MemoryLifecycle.getAllocRaw, live, sync, Id.run,
    modify, modifyGet, MonadStateOf.modifyGet, get, getThe, MonadStateOf.get,
    EStateM.get, EStateM.modifyGet, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- Equality-shaped postconditions expose a successful machine result for
composition through the outer typed operations. -/
theorem run_eq_of_wp {A : Type} (action : MachineHooks.M K U A) (before after : State) (value : A)
    (safe : wp action (fun actual next => actual = value ∧ next = after) (fun _ _ => False) before) :
    action before = .ok value after := by
  cases result : action before with
  | error error state =>
    simp [wp, WP.wpTrans, result] at safe
  | ok actual state =>
    simp only [wp, WP.wpTrans, result] at safe
    rcases safe with ⟨rfl, rfl⟩
    rfl

/-- Retagging a reference place keeps the address and metadata, changing only
its concrete provenance and the state returned by the inner reborrow. -/
def taggedPlace (place : MPlaceTy Provenance) (provenance : Provenance) :
    MPlaceTy Provenance :=
  {place with mplace := {place.mplace with ptr := {place.mplace.ptr with provenance := some provenance}}}

theorem retag_place [DecidableEq K] (hooks : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (alignment : Align) (policy : NewPermission)
    (before shaped after : State) (borrow : MachineHooks.BorrowState)
    (global : GlobalState) (tag : BorTag) (old new : Provenance)
    (layout : hooks.sizeAndAlign place before = .ok (some (size, alignment)) shaped)
    (tracked : shaped.machine.borrowTracker = some borrow)
    (allocated : borrow.global.newPointerTag = .ok (global, tag))
    (parent : place.mplace.ptr.provenance = some old)
    (borrowed : reborrow hooks budget place size policy tag
      {shaped with machine := {shaped.machine with borrowTracker := some {borrow with global}}} =
        .ok (some new) after) :
    retagPlace hooks budget place policy before = .ok (taggedPlace place new) after := by
  simp [retagPlace, taggedPlace, tracked, tracker_apply, checked, layout, allocated, parent, borrowed,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- The real per-call tag counter chooses the old counter value and
advances it, provided the source u64 counter is not exhausted. -/
theorem allocate_tag (global : GlobalState)
    (room : global.nextPointerTag.value ≠ 18446744073709551615) :
    ∃ next, global.newPointerTag = .ok (next, global.nextPointerTag) := by
  let current := global.nextPointerTag.value
  have bound : current.toNat + 1 < 2 ^ 64 := by
    have maxBound := current.toNat_lt
    have notMax : current.toNat ≠ 18446744073709551615 := by
      intro reaches
      apply room
      apply UInt64.toNat_inj.mp
      exact reaches
    omega
  have nonzero : current + 1 ≠ 0 := by
    intro zero
    have sum : (current + 1).toNat = current.toNat + 1 := by
      simp [UInt64.toNat_add, Nat.mod_eq_of_lt bound]
    simp [zero] at sum
  refine ⟨{global with nextPointerTag := ⟨current + 1, nonzero⟩}, ?_⟩
  have nonzeroActual : global.nextPointerTag.value + 1 ≠ 0 := nonzero
  simp [GlobalState.newPointerTag, BorTag.succ, room, BorTag.ofUInt64, current, nonzeroActual]

/-- Select the pinned mutable FnEntry policy from the real compiler
queries, including its conditional no-writable attribute query. -/
theorem new_mutable_permission (hooks : Hooks K U) (pointee : Miri.MIR.TyId)
    (before unpinned unsafeUnpinned frozen configured defined after : State)
    (frame : BorrowFrame) (definition : Miri.MIR.DefId) (writes noWritable : Bool)
    (unpin : hooks.isUnpin pointee before = .ok true unpinned)
    (unsafeUnpin : hooks.isUnsafeUnpin pointee unpinned = .ok true unsafeUnpinned)
    (freeze : hooks.typeIsFreeze pointee unsafeUnpinned = .ok true frozen)
    (implicit : hooks.implicitWrites frozen = .ok writes configured)
    (current : configured.stack.currentFrame? = some frame)
    (lookup : hooks.instanceDefinition frame.functionInstance configured = .ok definition defined)
    (queriedAttribute : if writes then hooks.rustcNoWritable definition defined = .ok noWritable after
      else noWritable = false ∧ after = defined) :
    newPermission hooks pointee .Mutable .FnEntry before =
      .ok (create ⟨true, true, true⟩ .Mutable .FnEntry ⟨writes, noWritable⟩) after := by
  cases writes
  · obtain ⟨rfl, rfl⟩ := queriedAttribute
    simp [newPermission, unpin, unsafeUnpin, freeze, implicit, MachineHooks.currentFrame,
      current, lookup, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
  · have queried : hooks.rustcNoWritable definition defined = .ok noWritable after := queriedAttribute
    simp [newPermission, unpin, unsafeUnpin, freeze, implicit, MachineHooks.currentFrame,
      current, lookup, queried, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- The actual typed pointer retag consults the mutable reference type,
selects its FnEntry policy and reconstructs the value from the retagged
place. The nested place step can use `retag_place` and the live reborrow rule. -/
theorem machine_retag_mutable_pointer [DecidableEq K] (hooks : Hooks K U) (budget : Nat)
    (value output : RvalueImmTy Provenance) (ty pointee : Miri.MIR.TyId)
    (before shapeState referenceState policyState placeState placeAfter after : State)
    (place retagged : MPlaceTy Provenance) (borrow : MachineHooks.BorrowState) (policy : NewPermission)
    (tracked : before.machine.borrowTracker = some borrow) (mode : borrow.retagMode = .FnEntry)
    (shape : hooks.typeShape ty before = .ok RetagPipeline.RetagTypeShape.reference shapeState)
    (reference : hooks.referencePointee ty shapeState = .ok (pointee, .Mut) referenceState)
    (permission : newPermission hooks pointee .Mutable .FnEntry referenceState = .ok (some policy) policyState)
    (position : hooks.immPtrToMPlace value policyState = .ok place placeState)
    (styled : retagPlace hooks budget place policy placeState = .ok retagged placeAfter)
    (reassemble : hooks.reconstruct value retagged placeAfter = .ok output after) :
    machineRetagPtrValue hooks budget value ty before = .ok (some output) after := by
  simp [machineRetagPtrValue, retagPtrValue, RetagPipeline.RetagTypeShape.reference,
    RetagPipeline.RetagTypeShape.classify, tracked, mode, shape, reference, permission,
    position, styled, reassemble, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- The tag lookup created during strong registration is independent of
the frame's separately maintained ownership ledger. -/
def registeredTracker (borrow : MachineHooks.BorrowState) (tag : BorTag) : MachineHooks.BorrowState :=
  {borrow with global := {borrow.global with protectedTags := borrow.global.protectedTags.insert tag .StrongProtector}}

/-- The real live retag of a nonempty, uniform frozen extent. Once the
parent access and child constructor are discharged by their permission
theorems, this rule composes the compiler effects, ownership registration,
associated access, optional race bookkeeping and both keyed write-backs. -/
theorem uniform_live_reborrow [DecidableEq K] (hooks : Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag)
    (location : RetagPipeline.ResolvedLocation) (before pointed resolved logged raced : State)
    (frame : BorrowFrame) (frameLedger : FrameState) (borrow : MachineHooks.BorrowState)
    (initial : Tree.LocationState) (entry : LocalAllocation Provenance BorrowTree K) (kind : AccessKind)
    (check : hooks.checkPtrAccess place.mplace.ptr size before = .ok () pointed)
    (resolve : hooks.resolveAllocation place.mplace.ptr pointed = .ok (some location) resolved)
    (log : hooks.logCreation place size policy tag (some location) resolved = .ok () logged)
    (selected : policy.protector = some .StrongProtector)
    (current : logged.stack.currentFrame? = some frame)
    (ledger : frame.extra.borrowTracker = some frameLedger)
    (tracked : logged.machine.borrowTracker = some borrow)
    (live : logged.machine.memory.live[location.allocId]? = some entry)
    (mutable : entry.allocation.mutability = .Mut)
    (imprecise : hooks.preciseInteriorMut = pure false)
    (freeze : hooks.typeIsFreeze place.layout.ty = pure true)
    (initialized : initialLocationState policy true = .ok initial)
    (access : initial.permission.associatedAccess = some kind)
    (nonempty : size.bytes ≠ 0)
    (ensure : let registered := withStrongProtector logged location tag frame frameLedger borrow
      hooks.ensureTreeExtra location.allocId registered = .ok () registered)
    (parentAccess : let active := registeredTracker borrow tag
      (entry.allocation.extra.performBorrowAccessRange location.parentProvenance location.baseOffset size kind
        active.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (race : let registered := withStrongProtector logged location tag frame frameLedger borrow
      let active := registeredTracker borrow tag
      let parent := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
        location.baseOffset size kind active.global.protectedTags .VisitChildrenOfAccessed
      retagRace location.allocId kind location.baseOffset size
        (withTree registered location.allocId entry parent.tree) = .ok () raced)
    (childComplete : let active := registeredTracker borrow tag
      let parent := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
        location.baseOffset size kind active.global.protectedTags .VisitChildrenOfAccessed
      (parent.tree.newChild location.baseOffset location.parentProvenance tag
        (DedupRangeMap.new size initial) policy.outsidePermission policy.protector.isSome).outcome = .ok ()) :
    let active := registeredTracker borrow tag
    let parent := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
      location.baseOffset size kind active.global.protectedTags .VisitChildrenOfAccessed
    let child := parent.tree.newChild location.baseOffset location.parentProvenance tag
      (DedupRangeMap.new size initial) policy.outsidePermission policy.protector.isSome
    let updated := {entry with allocation := entry.allocation.setExtra parent.tree}
    reborrow hooks budget place size policy tag before =
      .ok (some (.concrete location.allocId tag)) (withTree raced location.allocId updated child.tree) := by
  let registered := withStrongProtector logged location tag frame frameLedger borrow
  let active := registeredTracker borrow tag
  let parent := entry.allocation.extra.performBorrowAccessRange location.parentProvenance
    location.baseOffset size kind active.global.protectedTags .VisitChildrenOfAccessed
  let inside := DedupRangeMap.new size initial
  let child := parent.tree.newChild location.baseOffset location.parentProvenance tag inside
    policy.outsidePermission policy.protector.isSome
  let updated := {entry with allocation := entry.allocation.setExtra parent.tree}
  let final := withTree raced location.allocId updated child.tree
  have reg := register_strong location policy tag logged frame frameLedger borrow selected current ledger tracked
  have regLive : registered.machine.memory.live[location.allocId]? = some entry := live
  have regBorrow : registered.machine.borrowTracker = some active := rfl
  have initializedMap : insidePermissions hooks budget place size policy registered = .ok inside registered := by
    rw [MutableRetagRights.frozen_insidePermissions hooks budget place size policy initial imprecise freeze initialized]
    rfl
  have racedMemory := retagRace_keeps location.allocId kind location.baseOffset size
    (withTree registered location.allocId entry parent.tree) raced race
  have racedLive : raced.machine.memory.live[location.allocId]? = some updated := by
    rw [racedMemory.1]
    exact withTree_live registered location.allocId entry parent.tree
  have childReady : TypedRetagWP.insertChildPre location policy tag inside
      (fun after => after = final) (fun _ _ => False) raced :=
    MutableRetagRights.insertChild_of_complete location policy tag inside raced updated racedLive childComplete
  apply run_eq_of_wp
  apply live_reborrow hooks budget place size policy tag location before pointed resolved logged registered
    inside entry _ check resolve log reg regLive initializedMap ensure
  let segment : RangeMapSegment Tree.LocationState := ⟨⟨0, size.bytes⟩, initial⟩
  have partition : inside.iterAll.toList = [segment] := by
    simp [inside, DedupRangeMap.new, DedupRangeMap.iterAll, nonempty, segment]
  rw [partition]
  simp only [TypedRetagWP.segmentsPre, eq_self, true_and]
  have offset : Size.add location.baseOffset (Size.ofBytes segment.range.start) = .ok location.baseOffset := by
    cases location.baseOffset
    simp [Size.add, Size.ofBytes, segment]
  have length : Size.ofBytes (segment.range.stop - segment.range.start) = size := by
    cases size
    simp [Size.ofBytes, segment]
  exact segment_of_parent_access location segment location.baseOffset kind registered raced entry active _
    regLive regBorrow mutable access offset (by simpa only [length] using parentAccess)
    (by simpa only [length] using race) childReady

end Miri.Verification.MutableTypedRetag

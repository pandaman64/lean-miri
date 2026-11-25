import Miri.Verification.RvalueWP
import Miri.Input.EvalConfiguration

/-! Exact reductions for stack allocation, including the state preserved on failure. -/

namespace Miri.Verification.StackAllocationWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.TreeBorrows RvalueWP Std.WP

variable {K U A : Type}
local notation "State" => MachineHooks.State K U
local notation "Machine" => MachineHooks.MachineState K U
local notation "Errors" => StepError → State → Prop

/-- The reserved ID is visible to initialization and the new live entry is
visible to root-address assignment. -/
def insertStackAllocation (id : AllocId) (allocation : Allocation Provenance Unit)
    (tree : BorrowTree) (state : State) : State :=
  {state with machine := {state.machine with memory := {state.machine.memory with
    live := state.machine.memory.live.insert id ⟨.stack, allocation.withExtra tree⟩}}}

def rootTagForStackAllocation (machine : Machine) (id : AllocId) : Option BorTag :=
  match machine.borrowTracker with
  | none => some BorTag.one
  | some tracker => tracker.global.rootTag? id

/-- The native backing is dropped only if no live entry owns it. Failure to
drop overrides the earlier error while preserving the drop action's state. -/
def stackBackingErrorPre [DecidableEq K] (config : PlaceMachine.AllocationConfig K U)
    (allocation : Allocation Provenance Unit) (onError : Errors) : Errors :=
  fun error failed =>
    if allocation.nativeBuffer.isSome &&
        !(failed.machine.memory.live.any fun _ entry => entry.allocation.nativeBuffer == allocation.nativeBuffer) then
      match config.nativeDrop with
      | none => onError (.invalidProgram "native stack backing lacks drop capability") failed
      | some drop => actionPre (drop allocation) (fun _ => onError error) onError failed
    else onError error failed

/-- Stack allocation first obtains uninitialized storage, reserves an ID,
initializes the tree and machine extras, publishes the live entry, then assigns
a root address. This uses the exact error continuations at each cut. -/
def allocateStackRawPre [DecidableEq K] (config : PlaceMachine.AllocationConfig K U)
    (size : Size) (align : Align) (post : Pointer (Option Provenance) → State → Prop)
    (onError : Errors) : State → Prop :=
  let storage := fun created (before : State) =>
    match created with
    | .error error => onError (.callback s!"stack allocation storage: {repr error}") before
    | .ok allocation =>
      let onFailure := stackBackingErrorPre config allocation onError
      if allocation.byteSize.bytes > config.maximumObjectSize.bytes then
        onFailure (.resourceExhaustion "stack allocation exceeds maximum object size") before
      else
        let (memory, reserved) := before.machine.memory.reserveAllocId
        let state := {before with machine := {before.machine with memory}}
        match reserved with
        | .error error => onFailure (.resourceExhaustion s!"stack allocation ID: {repr error}") state
        | .ok id =>
          actionPre (PlaceMachine.initializeAllocation config id .stack size align) (fun tree next =>
            let live := insertStackAllocation id allocation tree next
            match rootTagForStackAllocation live.machine id with
            | none => onFailure (.invalidProgram "initialized allocation missing root tag") live
            | some tag => actionPre (config.adjustRootAddress id tag)
                (fun pointer => post pointer.withOptionalProvenance) onFailure live) onFailure state
  match config.nativeStorage with
  | none => storage (Allocation.tryNew size align .Uninit config.zeroedStorage)
  | some create => actionPre (create size align .Uninit) storage onError

private theorem stackBackingErrorPre_eq [DecidableEq K] (config : PlaceMachine.AllocationConfig K U)
    (allocation : Allocation Provenance Unit) (onError : Errors) (error : StepError) (failed : State) :
    stackBackingErrorPre config allocation onError error failed =
      (if allocation.nativeBuffer.isSome then
        if failed.machine.memory.live.any (fun _ entry =>
            entry.allocation.nativeBuffer == allocation.nativeBuffer) then onError error failed
        else
          match config.nativeDrop with
          | none => onError (.invalidProgram "native stack backing lacks drop capability") failed
          | some drop => actionPre (drop allocation) (fun _ => onError error) onError failed
      else onError error failed) := by
  unfold stackBackingErrorPre
  by_cases h : allocation.nativeBuffer.isSome
  · cases result : failed.machine.memory.live.any (fun _ entry =>
        entry.allocation.nativeBuffer == allocation.nativeBuffer) <;> simp [h]
  · simp [h]

set_option maxHeartbeats 1200000 in
theorem actionPre_allocateStackRaw [DecidableEq K] (config : PlaceMachine.AllocationConfig K U)
    (size : Size) (align : Align) (post : Pointer (Option Provenance) → State → Prop)
    (onError : Errors) :
    actionPre (PlaceMachine.allocateStackRaw config size align) post onError =
      allocateStackRawPre config size align post onError := by
  funext before
  unfold PlaceMachine.allocateStackRaw allocateStackRawPre
  cases storage : config.nativeStorage
  case' none =>
    simp only [actionPre, get, getThe, MonadStateOf.get, EStateM.get,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    generalize Allocation.tryNew (Prov := Provenance) size align .Uninit config.zeroedStorage = result
    cases result <;> try rfl
  case' some create =>
    simp only [actionPre, bind, Bind.bind, EStateM.bind]
    cases create size align .Uninit before
    case error => rfl
    case' ok result state =>
      clear before
      revert state
      intro before
      cases result <;> try rfl
  all_goals
    rename_i allocation
    by_cases exceeds : allocation.byteSize.bytes > config.maximumObjectSize.bytes
    all_goals simp only [get, getThe, MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
      EStateM.modifyGet, set, MonadStateOf.set, EStateM.set, pure, Pure.pure, EStateM.pure,
      Bind.bind, EStateM.bind, throw, MonadExceptOf.throw, EStateM.throw,
      tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, EStateM.Backtrackable.restore,
      throwThe, EStateM.nonBacktrackable, EStateM.dummyRestore,
      EarlyReturn.runK, EarlyReturnT.return, ExceptT.run, exceeds, ite_true, ite_false]
  all_goals
    try
      have bounded : ¬allocation.byteSize.bytes > config.maximumObjectSize.bytes := exceeds
      cases reserved : before.machine.memory.reserveAllocId
      case' mk memory result =>
        cases result
        case' error error => simp only [EStateM.bind, EStateM.throw]
        case' ok id =>
          simp only [EStateM.bind, EStateM.pure]
          let reservedState : State := {before with machine := {before.machine with memory}}
          cases initialized : PlaceMachine.initializeAllocation config id .stack size align reservedState
          case' error error failed => simp only [reservedState] at initialized; simp only [initialized]
          case' ok tree next =>
            simp only [reservedState] at initialized
            simp only [initialized, EStateM.modifyGet, EStateM.get, rootTagForStackAllocation]
            have tracks : (insertStackAllocation id allocation tree next).machine.borrowTracker =
                next.machine.borrowTracker := rfl
            simp only [tracks]
            cases tracked : next.machine.borrowTracker
            case' none =>
              cases adjusted : config.adjustRootAddress id BorTag.one (insertStackAllocation id allocation tree next) <;>
                simp only [insertStackAllocation, tracked] at adjusted <;>
                simp only [insertStackAllocation, EStateM.bind, EStateM.pure, actionPre, tracked, adjusted, ExceptT.mk]
            case' some tracker =>
              cases rooted : tracker.global.rootTag? id
              case' none => simp only [rooted, EStateM.bind, EStateM.throw]
              case' some tag =>
                simp only [rooted, EStateM.bind, EStateM.pure]
                cases adjusted : config.adjustRootAddress id tag (insertStackAllocation id allocation tree next) <;>
                  simp only [insertStackAllocation, tracked] at adjusted <;>
                  simp only [insertStackAllocation, EStateM.bind, EStateM.pure, actionPre, tracked, adjusted, ExceptT.mk]
  all_goals
    try rfl
  all_goals
    symm
    rw [stackBackingErrorPre_eq]
    try simp only [insertStackAllocation, tracked]
    try simp only [insertStackAllocation]
    split
    next native =>
      simp only [native, ↓reduceIte, EStateM.get, EStateM.bind]
      split
      next owned => simp only [owned, ↓reduceIte, EStateM.bind, EStateM.throw]
      next owned =>
        cases drops : config.nativeDrop
        next => simp only [drops, EStateM.bind, EStateM.throw]
        next drop =>
          simp only [drops, actionPre, EStateM.bind]
          split
          all_goals
            rename_i _ _ dropped
            simp only [dropped, EStateM.throw]
    next native => simp only [native, ↓reduceIte, EStateM.bind, EStateM.throw]

/-- Machine-only initialization effects retain every update on either exit. -/
def machinePre (action : PlaceMachine.MachineM K U A) (post : A → State → Prop)
    (onError : Errors) (state : State) : Prop :=
  match action state.machine with
  | .ok value machine => post value {state with machine}
  | .error error machine => onError error {state with machine}

/-- Construct the borrow tree at the root tag and install allocation-local
race clocks at the active thread's timestamp before calling the tail. -/
def initStackExtraPre
    (tail : AllocId → Size → Align → PlaceMachine.MachineM K U Unit)
    (id : AllocId) (size : Size) (align : Align) (post : BorrowTree → State → Prop)
    (onError : Errors) (state : State) : Prop :=
  let finish := fun (machine : Machine) tag =>
    let tree := BorrowTree.new tag size
    match machine.dataRace with
    | none => machinePre (tail id size align) (fun _ => post tree) onError {state with machine}
    | some global =>
      match global.activeThreadState machine.threads with
      | .error error => onError (.invalidProgram s!"allocation clocks: {repr error}") {state with machine}
      | .ok (index, clocks) =>
        let length := Miri.Concurrency.ByteSize.ofU64 size.bytes.toNat (by have h := UInt64.toNat_lt size.bytes; omega)
        let allocation := Miri.Concurrency.VClockAlloc.newAllocation length (clocks.clock.index index) index
        machinePre (tail id size align) (fun _ => post tree) onError
          {state with machine := {machine with raceAllocations := machine.raceAllocations.insert id allocation}}
  match state.machine.borrowTracker with
  | none => finish state.machine BorTag.one
  | some tracker =>
    match tracker.global.rootPointerTag id with
    | .error error => onError (.resourceExhaustion s!"allocation root tag: {repr error}") state
    | .ok (global, tag) => finish {state.machine with borrowTracker := some {tracker with global}} tag

private theorem initStackExtra_exact
    (tail : AllocId → Size → Align → PlaceMachine.MachineM K U Unit)
    (id : AllocId) (size : Size) (align : Align) (post : BorrowTree → State → Prop)
    (onError : Errors) (state : State) :
    machinePre (PlaceMachine.initStackExtra tail id size align) post onError state =
      initStackExtraPre tail id size align post onError state := by
  simp only [initStackExtraPre, PlaceMachine.initStackExtra, machinePre, bind, Bind.bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
    pure, Pure.pure, EStateM.pure, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  cases tracked : state.machine.borrowTracker
  case' some tracker =>
    simp only [tracked]
    cases rooted : tracker.global.rootPointerTag id
    case error error => simp only [rooted]; rfl
    case' ok result =>
      rcases result with ⟨global, tag⟩
      simp only [rooted, EStateM.bind, EStateM.pure]
  all_goals
    cases race : state.machine.dataRace
    case none =>
      simp only [race, EStateM.bind, EStateM.pure, EStateM.set]
      generalize action : tail id size align _ = result
      cases result <;> try simp only [tracked, race] at action
      all_goals simp only [action, tracked, race] <;> rfl
    case some raceState =>
      simp only [race, EStateM.bind, EStateM.pure, EStateM.set]
      cases active : raceState.activeThreadState state.machine.threads with
      | error error => simp only [active]; rfl
      | ok result =>
        rcases result with ⟨index, clocks⟩
        simp only [active, EStateM.bind, EStateM.pure, EStateM.modifyGet, EStateM.set]
        generalize action : tail id size align _ = result
        cases result <;> try simp only [tracked, race] at action
        all_goals simp only [action, tracked, race] <;> rfl

/-- Backtrace and span failures discard uninserted side indices after the
failure. Earlier initialization failures retain their own machine result. -/
def initializeAllocationPre (config : PlaceMachine.AllocationConfig K U) (id : AllocId)
    (kind : MemoryKind K) (size : Size) (align : Align) (post : BorrowTree → State → Prop)
    (onError : Errors) : State → Prop :=
  machinePre (config.diagnostic id size align) (fun _ =>
    initStackExtraPre config.allocationTail id size align (fun tree =>
      let onFailure := fun error => machinePre (config.discardUninserted id)
        (fun _ => onError error) onError
      let finish := machinePre (config.allocationSpan id size align) (fun _ => post tree) onFailure
      match config.allocationBacktrace with
      | none => finish
      | some capture => actionPre (capture id kind) (fun _ => finish) onFailure) onError) onError

set_option maxHeartbeats 1200000 in
theorem actionPre_initializeAllocation (config : PlaceMachine.AllocationConfig K U) (id : AllocId)
    (kind : MemoryKind K) (size : Size) (align : Align) (post : BorrowTree → State → Prop)
    (onError : Errors) :
    actionPre (PlaceMachine.initializeAllocation config id kind size align) post onError =
      initializeAllocationPre config id kind size align post onError := by
  funext state
  unfold initializeAllocationPre
  unfold PlaceMachine.initializeAllocation actionPre machinePre
  simp only [bind, Bind.bind, EStateM.bind]
  -- The lifted actions operate only on the machine component of the state.
  unfold PlaceMachine.allocationMachine
  cases diagnostic : config.diagnostic id size align state.machine
  case error error failed => rfl
  case' ok value machine =>
    cases value
    dsimp only
    rw [← initStackExtra_exact]
    unfold machinePre
    cases initialized : PlaceMachine.initStackExtra config.allocationTail id size align machine
    case error error failed => rfl
    case' ok tree machine =>
      simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
        EStateM.Backtrackable.restore, EStateM.nonBacktrackable, EStateM.dummyRestore,
        EarlyReturn.runK, EarlyReturnT.return, ExceptT.run, ExceptT.mk]
      cases backtrace : config.allocationBacktrace
      case' some capture =>
        simp only [EStateM.bind]
        cases ran : capture id kind {state with machine}
        case' error error failed => simp only [ran]
        case' ok value next =>
          simp only [ran]
          cases span : config.allocationSpan id size align next.machine <;> simp only [span]
      case' none =>
        simp only [EStateM.bind]
        cases span : config.allocationSpan id size align machine <;> simp only [span]
      all_goals
        try rfl
        try
          symm
          split
          all_goals
            rename_i _ _ discarded
            simp only [discarded, throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind]

/-- The production allocation tail writes the allocation's weak-memory entry.
Failure before publication may erase only the reserved ID's race and span indices. -/
def memoryExtrasPre [DecidableEq K] (extras : MemoryExtras.Hooks K U A) (id : AllocId)
    (weak : Bool) (post : Unit → State → Prop) (onError : Errors) (state : State) : Prop :=
  let machine := state.machine
  let failed := {state with machine := MemoryExtras.discardUninserted extras id machine false true true}
  if (extras.get machine.user).allocations.any (fun entry => entry.1 == id) then
    onError (.invalidProgram "allocation extras initialized twice") state
  else if weak && machine.dataRace.isNone then
    onError (.invalidProgram "weak memory requires vector clocks") failed
  else if weak && !machine.raceAllocations.contains id then
    onError (.invalidProgram "weak memory requires allocation race clocks") failed
  else
    let extra : MemoryExtras.AllocationExtra A :=
      {weakMemory := if weak then some Miri.Concurrency.StoreBufferAlloc.newAllocation else none}
    post () {state with machine := MemoryExtras.putAllocation extras machine id extra}

theorem machinePre_initAllocation [DecidableEq K] (extras : MemoryExtras.Hooks K U A) (id : AllocId)
    (weak : Bool) (post : Unit → State → Prop) (onError : Errors) (state : State) :
    machinePre (MemoryExtras.initAllocation extras id weak) post onError state =
      memoryExtrasPre extras id weak post onError state := by
  unfold memoryExtrasPre MemoryExtras.initAllocation machinePre
  cases duplicate : (extras.get state.machine.user).allocations.any (fun entry => entry.1 == id) <;>
    cases weak <;> cases global : state.machine.dataRace.isNone <;>
    cases localClocks : state.machine.raceAllocations.contains id <;>
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      duplicate, global, localClocks, Bool.false_eq_true, Bool.true_and, Bool.false_and,
      Bool.not_true, Bool.not_false, ↓reduceIte, tryCatch, tryCatchThe, MonadExceptOf.tryCatch,
      EStateM.tryCatch, EStateM.Backtrackable.restore, EStateM.dummyRestore,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw, set, MonadStateOf.set, EStateM.set,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, Pure.pure, EStateM.pure,
      EarlyReturn.runK, EarlyReturnT.return, ExceptT.run, ExceptT.mk] <;> rfl

open Miri.Memory.AllocAddresses in
/-- Form the concrete-provenance root pointer with the allocated ID and borrow
tag. The address source sees the already-published live entry. -/
def evalRootAddressPre {V : Type} (tape : ExecutionChoices.Access (PointerMachine.State K V))
    (pointers : PointerMachine.Hooks K V) (id : AllocId) (tag : BorTag)
    (post : Pointer Provenance → PointerMachine.State K V → Prop)
    (onError : StepError → PointerMachine.State K V → Prop)
    (state : PointerMachine.State K V) : Prop :=
  match state.machine.memory.live[id]? with
  | none => onError (.invalidProgram "new root allocation is not live") state
  | some entry =>
    let kind : AddressMemoryKind := match entry.kind with
      | .stack => .stack
      | .callerLocation | .machine _ => .other
    actionPre (ExecutionAddressChoices.addrFromAllocId tape pointers id (some kind))
      (fun address => post (Pointer.new (.concrete id tag) (Size.ofBytes address))) onError state

open Miri.Input Miri.Memory.AllocAddresses in
theorem actionPre_evalConfigurationRootAddress
    (maximum : Size) (storage : Size → Align → Option (Array UInt8))
    (diagnostic : AllocId → Size → Align → PlaceMachine.MachineM MiriMemoryKind
      (EvalConfiguration.User Os R P H D O Aff B Host) Unit)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalConfiguration.Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalConfiguration.User Os R P H D O Aff B Host) P)
    (id : AllocId) (tag : BorTag)
    (post : Pointer Provenance → EvalConfiguration.State Os R P H D O Aff B Host → Prop)
    (onError : StepError → EvalConfiguration.State Os R P H D O Aff B Host → Prop) :
    actionPre ((EvalConfiguration.allocation maximum storage diagnostic pointers extras).adjustRootAddress id tag)
      post onError = evalRootAddressPre EvalCoreMachine.tape pointers id tag post onError := by
  funext state
  have read (next : EvalConfiguration.State Os R P H D O Aff B Host →
        EvalConfiguration.State Os R P H D O Aff B Host → Prop) :
      actionPre get next onError state = next state state := rfl
  simp only [EvalConfiguration.allocation, evalRootAddressPre, actionPre_bind_fun, read]
  cases state.machine.memory.live[id]? with
  | none => rfl
  | some entry =>
    dsimp only
    rw [actionPre_bind_fun]
    congr 1
    funext after
    cases entry.kind <;> rfl

open Miri.Input in
theorem machinePre_evalConfigurationTail
    (maximum : Size) (storage : Size → Align → Option (Array UInt8))
    (diagnostic : AllocId → Size → Align → PlaceMachine.MachineM MiriMemoryKind
      (EvalConfiguration.User Os R P H D O Aff B Host) Unit)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalConfiguration.Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalConfiguration.User Os R P H D O Aff B Host) P)
    (id : AllocId) (size : Size) (align : Align)
    (post : Unit → EvalConfiguration.State Os R P H D O Aff B Host → Prop)
    (onError : StepError → EvalConfiguration.State Os R P H D O Aff B Host → Prop)
    (state : EvalConfiguration.State Os R P H D O Aff B Host) :
    machinePre ((EvalConfiguration.allocation maximum storage diagnostic pointers extras).allocationTail id size align)
      post onError state =
      match EvalBackendMachine.handler state.machine with
      | .error error => onError error state
      | .ok selected => memoryExtrasPre extras id (match selected with
          | .vclocks global => global.weakMemory
          | .none => false) post onError state := by
  simp only [EvalConfiguration.allocation, ← machinePre_initAllocation, machinePre,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind]
  cases EvalBackendMachine.handler state.machine <;> rfl

open Miri.Memory.AllocAddresses in
/-- An uncached stack address in managed mode uses exactly one slack request.
The source reuse pool is untouched, and errors retain the tape's output. -/
theorem actionPre_managedStackAddress {K U : Type}
    (tape : ExecutionChoices.Access (PointerMachine.State K U))
    (pointers : PointerMachine.Hooks K U) (id : AllocId)
    (post : UInt64 → PointerMachine.State K U → Prop)
    (onError : StepError → PointerMachine.State K U → Prop)
    (before : PointerMachine.State K U) (info : AllocationInfo) (generation : AddressGenerationState)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) = none)
    (metadata : before.machine.memory.getAllocInfo id = .ok info)
    (live : before.machine.memory.isAllocLive id = true)
    (kind : info.kind = .liveData)
    (managed : before.machine.user.addresses.addressMode = .managed)
    (generated : before.machine.user.addresses.generation = some generation) :
    actionPre (ExecutionAddressChoices.addrFromAllocId tape pointers id (some .stack)) post onError before =
      actionPre (ExecutionChoices.index tape .addressSlack 16) (fun selected state =>
        if support : selected < 16 then
          actionPre (PointerMachine.addrFromAllocId pointers id (some .stack) ⟨false, false, 0, ⟨selected, support⟩⟩)
            post onError state
        else onError (.invalidProgram "checked address slack exceeded support") state)
        onError before := by
  have notDead : (AllocationKind.liveData == .dead) = false := rfl
  have notTypeId : (AllocationKind.liveData == .typeId) = false := rfl
  have isManaged : (AddressSpaceMode.managed != .managed) = false := rfl
  have isStack : (AddressMemoryKind.stack == .stack) = true := rfl
  unfold ExecutionAddressChoices.addrFromAllocId actionPre
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, uncached, metadata, live, kind, managed, generated,
    Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    notDead, notTypeId, isManaged, isStack, ReusePool.prepareTakeAddr, Id.run]
  let addresses := {before.machine.user.addresses with addressMode := .managed, generation := some generation}
  let updated : PointerMachine.State K U :=
    {before with machine := {before.machine with user := {before.machine.user with addresses}}}
  have same : updated = before := by simp only [updated, addresses, ← managed, ← generated]
  let slack : PointerMachine.M K U (Fin 16) := do
    let selected ← ExecutionChoices.index tape .addressSlack 16
    if support : selected < 16 then pure ⟨selected, support⟩
    else throw (.invalidProgram "checked address slack exceeded support")
  change actionPre (slack >>= fun draw =>
      PointerMachine.addrFromAllocId pointers id (some .stack) ⟨false, false, 0, draw⟩)
    post onError updated = _
  rw [same, actionPre_bind_fun]
  unfold slack
  rw [actionPre_bind_fun]
  congr 1
  funext selected state
  by_cases support : selected < 16
  · simp only [support, ↓reduceDIte]
    rfl
  · simp only [support, ↓reduceDIte]
    rfl

open Miri.Memory.AllocAddresses

/-- Managed assignments for fresh stack allocations generate an address and
publish it in the base and inverse maps. The generator's partial state is
retained on exhaustion. A cache failure retains the publication prefix. -/
def freshStackAddress (addresses : GlobalAddressState) (id : AllocId)
    (size : Size) (align : Align) (slack : Fin 16) : AddressStateResult UInt64 :=
  match addresses.generation with
  | none => ⟨addresses, .error .missingAddressGeneration⟩
  | some generation =>
    let generated := generation.generator.generate size align slack
    let generation := {generation with generator := generated.state}
    let after := {addresses with generation := some generation}
    match generated.outcome with
    | .error error => ⟨after, .error (.addressGenerator error)⟩
    | .ok address =>
      let remaining := generated.state.getRemaining
      let pool := if remaining.start > remaining.stop / 2 then
          generation.reusePool.addressSpaceShortage
        else generation.reusePool
      let cached := ({after with generation := some {generation with reusePool := pool}}).cacheAddress id address
      ⟨cached.state, cached.outcome.map (fun () => address)⟩

theorem addrFromAllocId_freshStack
    (addresses : GlobalAddressState) (id : AllocId)
    (size : Size) (align : Align) (slack : Fin 16) (thread : AddressThreadId)
    (uncached : addresses.baseAddr.find? (fun entry => entry.allocId == id) = none)
    (managed : addresses.addressMode = .managed) :
    addresses.addrFromAllocId id (some ⟨.liveData, true, size, align, some .stack, thread⟩)
      ⟨false, false, 0, slack⟩ =
      let result := freshStackAddress addresses id size align slack
      ⟨result.state, result.outcome.map AddressAssignment.ready⟩ := by
  have notDead : (AllocationAddressKind.liveData == .dead) = false := rfl
  have notTypeId : (AllocationAddressKind.liveData == .typeId) = false := rfl
  have isStack : (AddressMemoryKind.stack == .stack) = true := rfl
  unfold GlobalAddressState.addrFromAllocId
  simp only [Id.run, pure, Pure.pure, notDead, notTypeId, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, managed, ReusePool.takeAddr, isStack]
  split
  next address cached =>
    change (Option.map BaseAddressEntry.address (addresses.baseAddr.find?
      (fun entry => entry.allocId == id))) = some address at cached
    simp [uncached] at cached
  next cached =>
    unfold freshStackAddress
    cases generationEq : addresses.generation
    case none => rfl
    case some generation =>
      dsimp only
      cases generated : (generation.generator.generate size align slack).outcome
      case error error => rfl
      case ok address =>
        dsimp only
        let generator := (generation.generator.generate size align slack).state
        let remaining := generator.getRemaining
        let pool := if remaining.start > remaining.stop / 2 then
            generation.reusePool.addressSpaceShortage else generation.reusePool
        let ready := {addresses with generation := some ⟨generator, pool⟩}
        let published := ready.cacheAddress id address
        change (match published.outcome with
          | .ok _ => ⟨published.state, .ok (.ready address)⟩
          | .error error => ⟨published.state, .error error⟩ : AddressStateResult AddressAssignment) =
          ⟨published.state, (published.outcome.map (fun () => address)).map AddressAssignment.ready⟩
        cases published.outcome <;> rfl

local notation "AddressState" => PointerMachine.State K U
local notation "AddressErrors" => StepError → AddressState → Prop

/-- Continue through the original address operation for states outside the
fresh managed allocation domain. -/
def addressFallbackPre (action : PointerMachine.M K U UInt64)
    (post : UInt64 → AddressState → Prop) (onError : AddressErrors) : AddressState → Prop :=
  actionPre action post onError

/-- Evaluate the pure address generation and publication result on a fresh live
stack entry, retaining the result's address state on either exit. -/
def stackAssignmentPre (pointers : PointerMachine.Hooks K U) (id : AllocId) (slack : Fin 16)
    (post : UInt64 → AddressState → Prop) (onError : AddressErrors) (before : AddressState) : Prop :=
  let fallback := addressFallbackPre
    (PointerMachine.addrFromAllocId pointers id (some .stack) ⟨false, false, 0, slack⟩) post onError before
  let machine := before.machine
  match machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id), machine.memory.getAllocInfo id with
  | none, .ok info =>
    if machine.memory.isAllocLive id = true ∧ info.kind = .liveData ∧
        machine.user.addresses.addressMode = .managed then
      let result := freshStackAddress machine.user.addresses id info.size info.align slack
      let after := {before with machine := {machine with user := {machine.user with addresses := result.state}}}
      match result.outcome with
      | .ok address => post address after
      | .error error => onError (pointers.classifyAddressError error) after
    else fallback
  | _, _ => fallback

theorem actionPre_stackAssignment (pointers : PointerMachine.Hooks K U) (id : AllocId) (slack : Fin 16)
    (post : UInt64 → AddressState → Prop) (onError : AddressErrors) (before : AddressState) :
    actionPre (PointerMachine.addrFromAllocId pointers id (some .stack) ⟨false, false, 0, slack⟩)
      post onError before = stackAssignmentPre pointers id slack post onError before := by
  unfold stackAssignmentPre
  dsimp only
  cases uncached : before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id)
  case some entry => rfl
  case none =>
    cases metadata : before.machine.memory.getAllocInfo id
    case error error => rfl
    case ok info =>
      by_cases domain : before.machine.memory.isAllocLive id = true ∧
          info.kind = .liveData ∧ before.machine.user.addresses.addressMode = .managed
      · simp only [domain, ↓reduceIte]
        obtain ⟨live, kind, managed⟩ := domain
        unfold actionPre
        rw [PointerMachine.addrFromAllocId_managedFresh pointers id slack before info uncached metadata live kind managed _
          (addrFromAllocId_freshStack _ _ _ _ _ _ uncached managed)]
        cases (freshStackAddress before.machine.user.addresses id info.size info.align slack).outcome <;> rfl
      · simp only [domain, ↓reduceIte, addressFallbackPre]

/-- Managed stack address selection consumes a slack request at the source
event site, then uses the address result of the state left by that request. -/
def stackAddressChoicePre (tape : ExecutionChoices.Access AddressState)
    (pointers : PointerMachine.Hooks K U) (id : AllocId)
    (post : UInt64 → AddressState → Prop) (onError : AddressErrors) (before : AddressState) : Prop :=
  let fallback := addressFallbackPre
    (ExecutionAddressChoices.addrFromAllocId tape pointers id (some .stack)) post onError before
  let machine := before.machine
  match machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id),
      machine.memory.getAllocInfo id, machine.user.addresses.generation with
  | none, .ok info, some _ =>
    if machine.memory.isAllocLive id = true ∧ info.kind = .liveData ∧
        machine.user.addresses.addressMode = .managed then
      actionPre (ExecutionChoices.index tape .addressSlack 16) (fun selected state =>
        if support : selected < 16 then
          stackAssignmentPre pointers id ⟨selected, support⟩ post onError state
        else onError (.invalidProgram "checked address slack exceeded support") state) onError before
    else fallback
  | _, _, _ => fallback

theorem actionPre_stackAddressChoice (tape : ExecutionChoices.Access AddressState)
    (pointers : PointerMachine.Hooks K U) (id : AllocId)
    (post : UInt64 → AddressState → Prop) (onError : AddressErrors) (before : AddressState) :
    actionPre (ExecutionAddressChoices.addrFromAllocId tape pointers id (some .stack)) post onError before =
      stackAddressChoicePre tape pointers id post onError before := by
  unfold stackAddressChoicePre
  dsimp only
  cases uncached : before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id)
  case some entry => rfl
  case none =>
    cases metadata : before.machine.memory.getAllocInfo id
    case error error => rfl
    case ok info =>
      cases generated : before.machine.user.addresses.generation
      case none => rfl
      case some generation =>
        by_cases domain : before.machine.memory.isAllocLive id = true ∧
            info.kind = .liveData ∧ before.machine.user.addresses.addressMode = .managed
        · simp only [domain]
          obtain ⟨live, kind, managed⟩ := domain
          rw [actionPre_managedStackAddress tape pointers id post onError before info generation
            uncached metadata live kind managed generated]
          simp only [actionPre_stackAssignment, true_and, ↓reduceIte]
        · simp only [domain, ↓reduceIte, addressFallbackPre]

/-- Select the managed stack reduction even when the memory kind is still
computed from a symbolic live entry. Other kinds use their source operation. -/
theorem actionPre_addressChoice (tape : ExecutionChoices.Access AddressState)
    (pointers : PointerMachine.Hooks K U) (id : AllocId) (kind : Option AddressMemoryKind)
    (post : UInt64 → AddressState → Prop) (onError : AddressErrors) (before : AddressState) :
    actionPre (ExecutionAddressChoices.addrFromAllocId tape pointers id kind) post onError before =
      match kind with
      | some .stack => stackAddressChoicePre tape pointers id post onError before
      | _ => addressFallbackPre (ExecutionAddressChoices.addrFromAllocId tape pointers id kind)
          post onError before := by
  cases kind with
  | none => rfl
  | some kind =>
    cases kind with
    | stack => exact actionPre_stackAddressChoice tape pointers id post onError before
    | other => rfl

end Miri.Verification.StackAllocationWP

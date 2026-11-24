import Miri.Verification.MemoryWP
import Miri.Verification.NondivergingIntrinsicWP
import Miri.Memory.AllocationVerification

/-! Exact continuations for the production memory-copy adapter. -/
namespace Miri.Verification.CopyMemoryWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.TreeBorrows Std.WP
open RvalueWP (actionPre actionPre_eq_wp actionPre_bind_fun actionPre_pure actionPre_throw)

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "Alloc" => Allocation Provenance BorrowTree
local notation "Ptr" => Pointer (Option Provenance)
local notation "Parts" => Option (AllocId × Size × ProvenanceExtra)
local notation "Hooks" => MemoryCopyHooks Provenance BorrowTree K (PlaceMachine.AccessState K U)
  ProvenanceExtra

/-- Preserve machine and memory changes made by the chosen pointer or allocation hook. -/
def memoryHookPre {A : Type}
    (hook : PlaceMachine.AccessState K U →
      MemoryStateHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) A)
    (post : A → State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  let result := hook ⟨before.machine, none⟩
  let after := {before with machine := {result.state.machine with memory := result.memory}}
  match result.outcome with
  | .ok value => post value after
  | .error error => onError (result.state.pendingError.getD (.callback error)) after

private theorem memoryHookPre_eq {A : Type}
    (hook : PlaceMachine.AccessState K U →
      MemoryStateHookResult Provenance BorrowTree K (PlaceMachine.AccessState K U) A)
    (post : A → State → Prop) (onError : StepError → State → Prop) :
    actionPre (GlobalMemoryCopyMachine.runMemoryHook hook) post onError = memoryHookPre hook post onError := by
  funext before
  unfold GlobalMemoryCopyMachine.runMemoryHook actionPre memoryHookPre
  cases ran : (hook ⟨before.machine, none⟩).outcome <;>
    simp [Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, ran] <;> rfl

/-- Check the two pointer ranges through the production hook. -/
def pointerPre (hooks : Hooks) (pointer : Ptr) (size : Size)
    (post : Parts → State → Prop) (onError : StepError → State → Prop) : State → Prop :=
  memoryHookPre (fun state => hooks.pointerAccess state.machine.memory state pointer size) post onError

/-- Call the allocation hook before touching bytes, retaining its effects. -/
def allocationHookPre (hooks : Hooks) (id : AllocId)
    (post : State → Prop) (onError : StepError → State → Prop) : State → Prop :=
  memoryHookPre (fun state => hooks.beforeAllocationAccess state.machine.memory state id)
    (fun _ => post) onError

/-- Resolve the live allocation or materialize a global. Read-only errors
observe any materialization performed by the mutable lookup. -/
def rawPre [DecidableEq K] (config : Config) (write : Bool) (id : AllocId)
    (post : Alloc → State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  let hookState := ⟨before.machine, none⟩
  let result := if write then
    MemoryLifecycle.getAllocRawMut before.machine.memory hookState id config.globalKind config.globalHooks
  else MemoryLifecycle.getAllocRaw before.machine.memory hookState id config.globalKind config.globalHooks
  let after := {before with machine := {result.hooks.machine with memory := result.memory}}
  match result.outcome with
  | .ok allocation => post allocation after
  | .error error => onError (result.hooks.pendingError.getD
      (config.memoryError (.pointerAccess (.rawAccess error)))) after

private theorem rawPre_eq [DecidableEq K] (config : Config) (write : Bool) (id : AllocId)
    (post : Alloc → State → Prop) (onError : StepError → State → Prop) :
    actionPre (GlobalMemoryCopyMachine.lookupAllocation config write id) post onError = rawPre config write id post onError := by
  funext before
  cases write <;> simp only [rawPre, GlobalMemoryCopyMachine.lookupAllocation, actionPre,
    Bool.false_eq_true, ↓reduceIte]
  · cases ran : (MemoryLifecycle.getAllocRaw before.machine.memory ⟨before.machine, none⟩
      id config.globalKind config.globalHooks).outcome <;>
      simp [Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, ran] <;> rfl
  · cases ran : (MemoryLifecycle.getAllocRawMut before.machine.memory ⟨before.machine, none⟩
      id config.globalKind config.globalHooks).outcome <;>
      simp [Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, ran] <;> rfl

/-- Verify that the source bytes and metadata can be snapshotted before any
destination lookup. -/
def snapshotPre (config : Config) (source : Alloc) (range : AllocRange) (pointerSize : Size)
    (post : State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  match source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) with
  | .error error => onError (config.memoryError (.allocation error)) before
  | .ok bytes =>
    match source.provenanceMap.prepareCopy range bytes pointerSize with
    | .error error => onError (config.memoryError (.allocation (.provenance error))) before
    | .ok _ =>
      match source.initializationMask.prepareCopy range with
      | .error error => onError (config.memoryError (.allocation (.memory error))) before
      | .ok _ => post before

private theorem snapshotPre_eq (config : Config) (source : Alloc) (range : AllocRange)
    (pointerSize : Size) (post : State → Prop) (onError : StepError → State → Prop) :
    actionPre (GlobalMemoryCopyMachine.checkSnapshot config source range pointerSize)
      (fun _ => post) onError = snapshotPre config source range pointerSize post onError := by
  funext before
  unfold GlobalMemoryCopyMachine.checkSnapshot snapshotPre actionPre
  cases full : source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) with
  | error => rfl
  | ok bytes =>
    cases prov : source.provenanceMap.prepareCopy range bytes pointerSize with
    | error => simp [Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, prov] <;> rfl
    | ok =>
      cases source.initializationMask.prepareCopy range <;>
        simp [Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, prov] <;> rfl

/-- Publish the allocation returned by the byte operation even when that
operation failed after mutating the destination. -/
def commitPre [DecidableEq K] (config : Config) (id : AllocId)
    (result : EStateM.Result AllocError Alloc Unit)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  let (outcome, allocation) := match result with
    | .ok () allocation => (Except.ok (), allocation)
    | .error error allocation => (Except.error error, allocation)
  match before.machine.memory.setLiveAllocation id allocation with
  | .error error => onError (config.memoryError (.memoryUpdate error)) before
  | .ok memory =>
    let after := {before with machine := {before.machine with memory}}
    match outcome with
    | .ok () => post () after
    | .error error => onError (config.memoryError (.allocation error)) after

/-- Reduce the physical copy to its byte and metadata checks while retaining
the destination update on either outcome. -/
theorem commitPre_copyRepeatedly [DecidableEq K] (config : Config) (id : AllocId)
    (source : Alloc) (sourceRange : AllocRange) (destStart : Size) (repeatCount : UInt64)
    (pointerSize : Size) (sameAllocation nonoverlap : Bool) (dest : Alloc)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) (before : State) :
    commitPre config id
      (source.copyRepeatedly sourceRange destStart repeatCount pointerSize sameAllocation nonoverlap dest)
      post onError before =
      Allocation.Bridge.copyRepeatedlyPre source sourceRange destStart repeatCount pointerSize
        sameAllocation nonoverlap
        (fun updated => commitPre config id (.ok () updated) post onError before)
        (fun error updated => commitPre config id (.error error updated) post onError before) dest := by
  rw [← Allocation.Bridge.copyRepeatedlyPre_eq]
  cases source.copyRepeatedly sourceRange destStart repeatCount pointerSize sameAllocation nonoverlap dest with
  | ok value => cases value; rfl
  | error => rfl

/-- The copy control flow with a precondition supplied for its two access
hooks. Pointer checks, snapshot preparation and the final commit always use
their concrete machine rules. -/
def copyPreUsing [DecidableEq K]
    (access : Bool → Alloc → AllocId → ProvenanceExtra → AllocRange →
      (Alloc → State → Prop) → (StepError → State → Prop) → State → Prop)
    (config : Config) (addresses : U → AllocAddresses.GlobalAddressState)
    (arithmetic : PointerArithmetic) (source dest : Ptr) (size : Size)
    (repeatCount : UInt64) (nonoverlapping : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) : State → Prop :=
  let hooks := MemoryCopyMachine.genericHooks config addresses arithmetic
  pointerPre hooks source size (fun srcParts state =>
    match Size.mul size repeatCount with
    | .error error => onError (config.memoryError (.allocation (.memory (.sizeError error)))) state
    | .ok destSize =>
      pointerPre hooks dest destSize (fun dstParts state =>
        let afterProbe := fun state =>
          match srcParts with
          | none => post () state
          | some (srcId, srcOffset, srcProv) =>
            rawPre config false srcId (fun srcAlloc state =>
              if config.ghostMode then onError (.invalidProgram "cannot copy during validation") state
              else
                let range := allocRange srcOffset size
                access false srcAlloc srcId srcProv range (fun srcAlloc state =>
                  match dstParts with
                  | none => post () state
                  | some (dstId, dstOffset, dstProv) =>
                    snapshotPre config srcAlloc range arithmetic.pointerSize
                      (rawPre config true dstId (fun dstAlloc =>
                        allocationHookPre hooks dstId
                          (access true dstAlloc dstId dstProv (allocRange dstOffset destSize)
                            (fun dstAlloc state =>
                              Allocation.Bridge.copyRepeatedlyPre srcAlloc range dstOffset repeatCount
                                arithmetic.pointerSize (srcId == dstId) nonoverlapping
                                (fun updated => commitPre config dstId (.ok () updated) post onError state)
                                (fun error updated =>
                                  commitPre config dstId (.error error updated) post onError state)
                                dstAlloc) onError) onError) onError)
                      onError state) onError state) onError state
        match hooks.tryGetAllocId state.machine.memory ⟨state.machine, none⟩ source size.bytes with
        | none => afterProbe state
        | some id => allocationHookPre hooks id afterProbe onError state) onError state) onError

private theorem actionPre_get (post : State → State → Prop)
    (onError : StepError → State → Prop) (before : State) :
    actionPre (get : MachineHooks.M K U State) post onError before = post before before := rfl

/-- The exact memory-copy precondition uses the actual source and destination
allocation IDs, offsets and provenance selected by pointer resolution. -/
def copyPre [DecidableEq K] (config : Config) (addresses : U → AllocAddresses.GlobalAddressState)
    (arithmetic : PointerArithmetic) (source dest : Ptr) (size : Size)
    (repeatCount : UInt64) (nonoverlapping : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) : State → Prop :=
  copyPreUsing (fun write allocation id provenance range =>
    actionPre (GlobalMemoryCopyMachine.access config write allocation id provenance range))
    config addresses arithmetic source dest size repeatCount nonoverlapping post onError

set_option maxHeartbeats 600000 in
theorem copyPre_eq [DecidableEq K] (config : Config)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (source dest : Ptr) (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    actionPre (GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest size
      repeatCount nonoverlapping) post onError =
      copyPre config addresses arithmetic source dest size repeatCount nonoverlapping post onError := by
  unfold GlobalMemoryCopyMachine.genericCopy copyPre copyPreUsing
  simp only [actionPre_bind_fun, memoryHookPre_eq, pointerPre, allocationHookPre]
  congr 1
  funext srcParts state
  cases Size.mul size repeatCount with
  | error => rfl
  | ok destSize =>
    simp only [actionPre_bind_fun, memoryHookPre_eq, actionPre_pure]
    congr 1
    funext dstParts state
    rw [actionPre_get]
    cases probe : (MemoryCopyMachine.genericHooks config addresses arithmetic).tryGetAllocId
      state.machine.memory ⟨state.machine, none⟩ source size.bytes
    case' some id =>
      simp only [actionPre_bind_fun, memoryHookPre_eq]
      congr 1
      funext _ state
    all_goals
      cases srcParts with
      | none => rfl
      | some parts =>
        rcases parts with ⟨srcId, srcOffset, srcProv⟩
        simp only [actionPre_bind_fun, rawPre_eq]
        congr 1
        funext srcAlloc state
        cases config.ghostMode
        · simp only [Bool.false_eq_true, ↓reduceIte, actionPre_bind_fun]
          congr 1
          funext srcAlloc state
          cases dstParts with
          | none => rfl
          | some parts =>
            rcases parts with ⟨dstId, dstOffset, dstProv⟩
            simp only [actionPre_bind_fun, snapshotPre_eq, rawPre_eq, memoryHookPre_eq]
            congr 1
            funext _
            congr 1
            funext dstAlloc
            congr 1
            funext _
            congr 1
            funext dstAlloc state
            rw [← commitPre_copyRepeatedly]
            unfold commitPre
            simp only [actionPre_bind_fun]
            rw [actionPre_get]
            generalize srcAlloc.copyRepeatedly (allocRange srcOffset size) dstOffset repeatCount
              arithmetic.pointerSize (srcId == dstId) nonoverlapping dstAlloc = result
            cases result with
            | ok value allocation =>
              cases value
              cases state.machine.memory.setLiveAllocation dstId allocation <;> rfl
            | error error allocation =>
              cases state.machine.memory.setLiveAllocation dstId allocation <;> rfl
        · simp only [↓reduceIte, actionPre_bind_fun, actionPre_throw]

/-- Both the normal and error continuation use the interpreter's resulting state. -/
theorem wp_copy [DecidableEq K] (config : Config)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (source dest : Ptr) (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    wp (GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest size
      repeatCount nonoverlapping) post onError =
      copyPre config addresses arithmetic source dest size repeatCount nonoverlapping post onError := by
  rw [← actionPre_eq_wp, copyPre_eq]

/-- A copy's final live-map update replaces exactly the selected entry and
then dispatches to the continuation for the allocation-level outcome. -/
theorem commitPre_live [DecidableEq K] (config : Config) (id : AllocId)
    (before : State) (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.machine.memory.live[id]? = some entry) (updated : Alloc)
    (outcome : Except AllocError Unit)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    commitPre config id (match outcome with
      | .ok () => .ok () updated
      | .error error => .error error updated) post onError before =
      let memory := {before.machine.memory with live :=
          (before.machine.memory.live.insert id {entry with allocation := updated})}
      let after := {before with machine := {before.machine with memory}}
      match outcome with
      | .ok () => post () after
      | .error error => onError (config.memoryError (.allocation error)) after := by
  have installed := before.machine.memory.setLiveAllocation_of_find id entry updated live
  cases outcome with
  | ok value => cases value; simp only [commitPre, installed]
  | error => simp only [commitPre, installed]

/-- Specialize the final continuation to an initialized one-copy range.
The destination image and initialization/provenance updates come from the
allocation rule and are installed at the exact destination allocation key. -/
theorem initializedCopy_live [DecidableEq K] (config : Config)
    (before : State) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.machine.memory.live[id]? = some entry)
    (source dest : Alloc) (sourceRange : AllocRange) (sourceEnd destStart pointerSize : Size)
    (sameAllocation nonoverlap : Bool)
    (bytes sourceImage destImage : Array UInt8) (copied : ProvenanceCopy Provenance)
    (cleared final : ProvenanceMap Provenance)
    (srcStorage : source.len = source.byteSize.bytes.toNat)
    (srcEnd : sourceRange.endExclusive = .ok sourceEnd)
    (srcNonzero : sourceRange.size.bytes ≠ 0)
    (srcMaskLen : source.initializationMask.len = source.byteSize)
    (srcMaskWF : InitMask.WriteProof.WellFormed source.initializationMask)
    (srcInit : source.initializationMask.isRangeInitialized sourceRange = .ok (.ok ()))
    (srcSlice : source.getBytesUnchecked sourceRange = .ok bytes)
    (srcInBounds : sourceEnd.bytes.toNat ≤ source.byteSize.bytes.toNat)
    (srcFull : source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) = .ok sourceImage)
    (prepare : source.provenanceMap.prepareCopy sourceRange sourceImage pointerSize = .ok copied)
    (disjoint : sameAllocation = true → nonoverlap = true →
      sourceEnd.bytes.toNat ≤ destStart.bytes.toNat ∨
        destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ sourceRange.start.bytes.toNat)
    (destStorage : dest.len = dest.byteSize.bytes.toNat)
    (destMutable : dest.mutability = .Mut)
    (destMaskLen : dest.initializationMask.len = dest.byteSize)
    (destMaskWF : InitMask.WriteProof.WellFormed dest.initializationMask)
    (destInBounds : destStart.bytes.toNat + sourceRange.size.bytes.toNat ≤ dest.byteSize.bytes.toNat)
    (destFull : dest.getBytesUnchecked (allocRange Size.ZERO dest.byteSize) = .ok destImage)
    (clear : dest.provenanceMap.clear (allocRange destStart sourceRange.size) destImage pointerSize =
      .ok () cleared)
    (apply : cleared.applyCopy copied (allocRange destStart sourceRange.size) 1 = .ok () final)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    ∃ updated,
      updated.getBytesUnchecked (allocRange destStart sourceRange.size) = .ok bytes ∧
      updated.initializationMask.isRangeInitialized (allocRange destStart sourceRange.size) =
        .ok (.ok ()) ∧
      updated.provenanceMap = final ∧
      (commitPre config id
        (source.copyRepeatedly sourceRange destStart 1 pointerSize sameAllocation nonoverlap dest)
        post onError before =
        let memory := {before.machine.memory with live :=
            (before.machine.memory.live.insert id {entry with allocation := updated})}
        post () {before with machine := {before.machine with memory}}) := by
  have prepareImage image (known : source.getBytesUnchecked (allocRange Size.ZERO source.byteSize) =
      .ok image) : source.provenanceMap.prepareCopy sourceRange image pointerSize = .ok copied := by
    rw [srcFull] at known
    rw [← Except.ok.inj known]
    exact prepare
  have clearImage image (known : dest.getBytesUnchecked (allocRange Size.ZERO dest.byteSize) =
      .ok image) : dest.provenanceMap.clear (allocRange destStart sourceRange.size) image pointerSize =
        .ok () cleared := by
    rw [destFull] at known
    rw [← Except.ok.inj known]
    exact clear
  obtain ⟨updated, copied, _, _, _, _, _, _, _, _, initialized, _, _, provenance, bytes, _⟩ :=
    Allocation.copy_initialized_spec source dest sourceRange sourceEnd destStart pointerSize
      sameAllocation nonoverlap bytes copied cleared final srcStorage srcEnd srcNonzero srcMaskLen
      srcMaskWF srcInit srcSlice srcInBounds prepareImage disjoint destStorage destMutable
      destMaskLen destMaskWF destInBounds clearImage apply
  refine ⟨updated, bytes, initialized, provenance, ?_⟩
  unfold Allocation.copy at copied
  rw [copied]
  exact commitPre_live config id before entry live updated (.ok ()) post onError

section Canonical

variable {C O X Host : Type} [DecidableEq K]

/-- The memory callback used by a canonical MIR `CopyNonOverlapping` statement. -/
theorem actionPre_intrinsic_copy (config : ExecutionMachine.Config K U C O X Host)
    (choice : C) (source dest : Ptr) (size : Size) (nonoverlap : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    actionPre ((ExecutionMachine.memoryIntrinsicHooks config).memCopy
      choice source dest size nonoverlap) post onError =
      copyPre config.access config.addresses config.arithmetic source dest size 1 nonoverlap
        post onError := by
  rw [EffectSpecs.canonical_intrinsic_copy, copyPre_eq]

/-- The copy callback of the canonical function-intrinsic evaluator uses the
same primitive. In particular the `copy` intrinsic passes `false`. -/
theorem wp_intrinsic_hooks_copy (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits)
    (context : IntrinsicHooks Provenance State C ExecutionMachine.Value)
    (choice : C) (source dest : Ptr) (size : Size) (nonoverlap : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    wp ((ExecutionMachine.intrinsicHooks config limits context).memCopy
      choice source dest size nonoverlap) post onError =
      copyPre config.access config.addresses config.arithmetic source dest size 1 nonoverlap
        post onError :=
  wp_copy config.access config.addresses config.arithmetic source dest size 1 nonoverlap post onError

theorem actionPre_intrinsic_hooks_copy (config : ExecutionMachine.Config K U C O X Host)
    (limits : ExecutionMachine.Limits)
    (context : IntrinsicHooks Provenance State C ExecutionMachine.Value)
    (choice : C) (source dest : Ptr) (size : Size) (nonoverlap : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    actionPre ((ExecutionMachine.intrinsicHooks config limits context).memory.memCopy
      choice source dest size nonoverlap) post onError =
      copyPre config.access config.addresses config.arithmetic source dest size 1 nonoverlap
        post onError :=
  copyPre_eq config.access config.addresses config.arithmetic source dest size 1 nonoverlap post onError

end Canonical

macro "miri_copy_memory_wp" : tactic =>
  `(tactic| simp only [actionPre_intrinsic_copy, actionPre_intrinsic_hooks_copy, copyPre_eq, wp_copy,
    wp_intrinsic_hooks_copy,
    commitPre_copyRepeatedly])

macro "miri_copy_bytes_wp" : tactic =>
  `(tactic| simp only [commitPre_copyRepeatedly, Allocation.Bridge.copyRepeatedlyPre,
    Allocation.Bridge.prepareCopyOverwritePre_eq, Allocation.Bridge.overwriteCopyBytes_eq])

end Miri.Verification.CopyMemoryWP

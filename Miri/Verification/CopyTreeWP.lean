import Miri.Verification.MemoryWP
import Miri.Verification.CopyMemoryWP
import Miri.Verification.TreeOverlapWP

/-! Tree obligations for the concrete source and destination copy hooks. -/
namespace Miri.Verification.CopyTreeWP

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Std.WP

variable {K U A : Type}
local notation "State" => MachineHooks.State K U
local notation "Machine" => PlaceMachine.Machine K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "Allocation" => Miri.Memory.Allocation Provenance BorrowTree

/-- Evidence for reaching one tracked permission check. Each phase uses the
machine produced by the preceding phase. The destination has its own readiness
proof, so its protector set can differ from the source's. -/
structure Ready (config : Config) (write : Bool) (id : AllocId)
    (range : AllocRange) (before : State) where
  diagnosed : Machine
  raced : Machine
  machine : Machine
  tracker : MachineHooks.BorrowState
  diagnostic : config.diagnostic write id range before.machine = .ok () diagnosed
  race : MachineHooks.memoryRaceAccess diagnosed id range (if write then some .Write else none)
    .Read = (raced, .ok ())
  weak : if write then config.weakMemoryWrite id range raced = .ok () machine else machine = raced
  tracked : machine.borrowTracker = some tracker

/-- Pull a concrete copy access back to its ranged Tree Borrows contract once
its pre-access policies have succeeded. The postconditions still run through
synchronization and the live-cache commit. Tree errors retain the partially
updated allocation and do not run synchronization. -/
theorem access_iff [DecidableEq K] (config : Config) (write : Bool)
    (allocation : Allocation) (id : AllocId) (provenance : ProvenanceExtra)
    (range : AllocRange) (before : State) (ready : Ready config write id range before)
    (post : Allocation → State → Prop) (onError : StepError → State → Prop) :
    wp (GlobalMemoryCopyMachine.access config write allocation id provenance range)
      post onError before ↔
    TreeBorrowsWP.accessPre allocation.extra provenance range.start range.size
      (if write then .Write else .Read) ready.tracker.global.protectedTags .VisitChildrenOfAccessed
      (fun tree _ => MemoryWP.policyPre (config.syncAccess write id range) ⟨ready.machine, none⟩ tree
        (fun state tree => MemoryWP.copyAccessCommitPre config before allocation id range state tree
          (.ok ()) post onError)
        (fun message state tree => MemoryWP.copyAccessCommitPre config before allocation id range state tree
          (.error message) post onError))
      (fun status tree _ =>
        let error := PlaceMachine.treeError write status
        MemoryWP.copyAccessCommitPre config before allocation id range ⟨ready.machine, some error⟩ tree
          (.error (reprStr error)) post onError) := by
  rw [MemoryWP.copyAccess_iff]
  unfold MemoryWP.memoryAccessPre
  have diagnostic := ready.diagnostic
  have race := ready.race
  have weak := ready.weak
  have tracked := ready.tracked
  cases write
  · simp only [Bool.false_eq_true, ↓reduceIte] at weak race ⊢
    simp only [MemoryWP.policyPre, wp, WP.wpTrans, diagnostic, race, ← weak, tracked, MemoryWP.failurePre]
  · simp only [↓reduceIte] at weak race ⊢
    simp only [MemoryWP.policyPre, wp, WP.wpTrans, diagnostic, race, weak, tracked, MemoryWP.failurePre]

/-- A copy access with both outcomes routed through its actual cache commit. -/
def accessPre [DecidableEq K] (config : Config) (write : Bool)
    (allocation : Allocation) (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (post : Allocation → State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  MemoryWP.memoryAccessPre config write ⟨before.machine, none⟩ allocation.extra id provenance range
    (fun state tree => MemoryWP.copyAccessCommitPre config before allocation id range state tree
      (.ok ()) post onError)
    (fun message state tree => MemoryWP.copyAccessCommitPre config before allocation id range state tree
      (.error message) post onError)

theorem accessPre_eq [DecidableEq K] (config : Config) (write : Bool)
    (allocation : Allocation) (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (post : Allocation → State → Prop) (onError : StepError → State → Prop) :
    RvalueWP.actionPre (GlobalMemoryCopyMachine.access config write allocation id provenance range)
      post onError = accessPre config write allocation id provenance range post onError := by
  rw [RvalueWP.actionPre_eq_wp]
  funext before
  exact propext (MemoryWP.copyAccess_iff config write allocation id provenance range post onError before)

/-- Once a tracked copy access reaches Tree Borrows, check its initial byte
locations. The success continuation receives the byte relation of the updated
tree and still runs the configured synchronization and cache commit. -/
theorem accessPre_observe_iff [DecidableEq K] (config : Config) (write : Bool)
    (allocation : Allocation) (id : AllocId) (provenance : ProvenanceExtra)
    (range : AllocRange) (before : State) (ready : Ready config write id range before)
    (finish : Size) (wellFormed : allocation.extra.locations.WellFormed)
    (endpoint : range.start.add range.size = .ok finish)
    (bound : finish.bytes ≤ allocation.extra.locations.size.bytes)
    (post : Allocation → State → Prop) :
    accessPre config write allocation id provenance range post (fun _ _ => False) before ↔
    let initial := allocation.extra
    let kind : AccessKind := if write then .Write else .Read
    let tags := ready.tracker.global.protectedTags
    let mode := Tree.ChildrenVisitMode.VisitChildrenOfAccessed
    let bytes : Miri.DataStructures.ByteRange := ⟨range.start.bytes, finish.bytes⟩
    TreeOverlapWP.accessBytePre initial provenance range.start range.size bytes kind tags mode
      (fun _ updated =>
        updated = { initial with locations := updated.locations } →
        updated.locations.WellFormed → updated.locations.size = initial.locations.size →
        (∀ byte data, updated.locations.MapAt byte data ↔
          TreeOverlapWP.afterAccess initial provenance kind bytes tags mode byte data) →
        MemoryWP.policyPre (config.syncAccess write id range) ⟨ready.machine, none⟩ updated
          (fun state tree => MemoryWP.copyAccessCommitPre config before allocation id range state tree
            (.ok ()) post (fun _ _ => False))
          (fun message state tree => MemoryWP.copyAccessCommitPre config before allocation id range state tree
            (.error message) post (fun _ _ => False))) := by
  rw [← accessPre_eq, RvalueWP.actionPre_eq_wp, access_iff config write allocation id provenance range before ready]
  have reject (status : BorrowTree.BorrowTreeAccessStatus) (tree : BorrowTree) :
      MemoryWP.copyAccessCommitPre config before allocation id range
        ⟨ready.machine, some (PlaceMachine.treeError write status)⟩ tree
        (.error (reprStr (PlaceMachine.treeError write status))) post (fun _ _ => False) ↔ False := by
    dsimp only [MemoryWP.copyAccessCommitPre]
    split <;> rfl
  simp only [reject]
  refine ((TreeRangeOutcomeWP.wp_access_outcomePre_iff _ _ _ _ _ _ _ _ _).symm.trans
    (TreeOverlapWP.wp_access_bytes_iff _ _ _ _ _ _ _ _ wellFormed endpoint bound _)).trans ?_
  constructor
  · rintro ⟨checks, done⟩
    exact ⟨checks, fun _ _ _ _ => done⟩
  · intro checked
    obtain ⟨checks, shape, formed, extent, locations, done⟩ :=
      (TreeOverlapWP.accessBytePre_observe _ _ _ _ _ _ _ _ wellFormed endpoint bound _).mp checked
    exact ⟨checks, done shape formed extent locations⟩

/-- Rewriting principle for the concrete read and write, with ordered machine
work in between. The destination selector runs after the source read and may
inspect its returned allocation and the committed machine. This covers local
and global lookups and any interposed policy errors. -/
theorem readWrite_iff [DecidableEq K] (config : Config)
    (source : Allocation) (srcId dstId : AllocId) (srcProv dstProv : ProvenanceExtra)
    (srcRange dstRange : AllocRange) (selectDest : Allocation → MachineHooks.M K U Allocation)
    (finish : Allocation → Allocation → MachineHooks.M K U A)
    (post : A → State → Prop) (onError : StepError → State → Prop) (before : State) :
    wp (do
      let read ← GlobalMemoryCopyMachine.access config false source srcId srcProv srcRange
      let destination ← selectDest read
      let written ← GlobalMemoryCopyMachine.access config true destination dstId dstProv dstRange
      finish read written) post onError before ↔
    accessPre config false source srcId srcProv srcRange (fun read =>
      wp (selectDest read) (fun destination =>
        accessPre config true destination dstId dstProv dstRange (fun written =>
          wp (finish read written) post onError) onError) onError) onError before := by
  simp only [← RvalueWP.actionPre_eq_wp, RvalueWP.actionPre_bind_fun, accessPre_eq]

/-- A local access commits its updated allocation on either outcome.
The touched-state policy runs after the cache insertion, and the resulting
machine is passed to the selected continuation. -/
theorem commitLocal_iff [DecidableEq K] (config : Config) (before : State)
    (allocation : Allocation) (id : AllocId) (range : AllocRange)
    (state : PlaceMachine.AccessState K U) (tree : BorrowTree)
    (entry : LocalAllocation Provenance BorrowTree K) (live : state.machine.memory.live[id]? = some entry)
    (outcome : Except String Unit) (post : Allocation → State → Prop) (onError : StepError → State → Prop) :
    MemoryWP.copyAccessCommitPre config before allocation id range state tree outcome post onError ↔
      let updated := allocation.setExtra tree
      let memory := {state.machine.memory with live := (state.machine.memory.live.insert id
          {entry with allocation := updated})}
      let after := {before with machine := config.retainTouched {state.machine with memory} (some ⟨id, range, updated⟩)}
      match outcome with
      | .ok () => post updated after
      | .error message => onError (state.pendingError.getD (.callback message)) after := by
  dsimp only [MemoryWP.copyAccessCommitPre]
  rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, live]
  simp only [Option.isSome_some, ↓reduceIte, MemoryState.setLiveAllocation_of_find _ _ _ _ live]
  rcases outcome with ⟨⟨⟩⟩ | ⟨_⟩ <;> rfl

/-- The immediate cache insertion replaces the source under its allocation ID
and leaves every distinct destination key intact. Instantiate this at the
pre-lookup memory only after establishing that the interposed policies preserve
the lookup at that key. -/
theorem committedLookup [DecidableEq K]
    (memory : MemoryState Provenance BorrowTree K) (srcId dstId : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (updated : Allocation)
    (live : memory.live[srcId]? = some entry) :
    memory.setLiveAllocation srcId updated = .ok {memory with live := memory.live.insert srcId {entry with allocation := updated}} ∧
    (memory.live.insert srcId {entry with allocation := updated})[dstId]? =
      if srcId = dstId then some {entry with allocation := updated} else memory.live[dstId]? := by
  refine ⟨MemoryState.setLiveAllocation_of_find _ _ _ _ live, ?_⟩
  by_cases same : srcId = dstId
  · subst dstId
    simp
  · simp [Std.ExtTreeMap.getElem?_insert, same]

/-- Mutable lookup resolves a selected live allocation before the destination
allocation policy runs. The returned snapshot continues to be the input to
the write, including when the policy changes machine state. -/
private theorem localMutableLookup [DecidableEq K] (config : Config)
    (before : State) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.machine.memory.live[id]? = some entry)
    (mutable : entry.allocation.mutability ≠ .Not) :
    MemoryLifecycle.getAllocRawMut before.machine.memory ⟨before.machine, none⟩ id
      config.globalKind config.globalHooks =
      ⟨before.machine.memory,
        config.globalHooks.synchronizeMemory before.machine.memory ⟨before.machine, none⟩,
        .ok entry.allocation⟩ := by
  simp [MemoryLifecycle.getAllocRawMut, live, mutable]

/-- Discharge the mutable-lookup portion of the exact copy WP for a known
live destination. The continuation still receives the machine produced by
global memory synchronization. -/
theorem localMutableLookupPre_iff [DecidableEq K] (config : Config)
    (before : State) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.machine.memory.live[id]? = some entry)
    (mutable : entry.allocation.mutability ≠ .Not)
    (post : Allocation → State → Prop) (onError : StepError → State → Prop) :
    CopyMemoryWP.rawPre config true id post onError before ↔
    let synced := config.globalHooks.synchronizeMemory before.machine.memory ⟨before.machine, none⟩
    post entry.allocation {before with machine := {synced.machine with memory := before.machine.memory}} := by
  simp only [CopyMemoryWP.rawPre, ↓reduceIte, localMutableLookup config before id entry live mutable]

/-- For the aliasing case, reduce the two authorization obligations to
pointwise checks. Its write authorization uses the read's retained locations,
which may cover part or all of the write range. Apply this after the exact
machine continuations establish that the writer receives that tree. -/
theorem permissions_pointwise_iff (tree : BorrowTree) (reader writer : ProvenanceExtra)
    (readRange writeRange : AllocRange) (readTags writeTags : ProtectedTags) :
    TreeBorrowsWP.accessPre tree reader readRange.start readRange.size .Read readTags .VisitChildrenOfAccessed
      (fun after _ => TreeBorrowsWP.accessPre after writer writeRange.start writeRange.size .Write writeTags
        .VisitChildrenOfAccessed (fun _ _ => True) (fun _ _ _ => False))
      (fun _ _ _ => False) ↔
    TreeRangePointwiseWP.readWritePre tree reader writer readRange.start readRange.size
      writeRange.start writeRange.size readTags writeTags .VisitChildrenOfAccessed
      .VisitChildrenOfAccessed := by
  rw [← TreeRangePointwiseWP.wp_read_write_pointwise_iff]
  simp only [TreeRangeOutcomeWP.wp_pair_bind_iff, TreeRangeOutcomeWP.wp_access_outcomePre_iff]

/-- The exact physical copy WP with both access hooks reduced to their
ordered diagnostic, policy, Tree Borrows and cache continuations. -/
def copyPre [DecidableEq K] (config : Config) (addresses : U → AllocAddresses.GlobalAddressState)
    (arithmetic : PointerArithmetic) (source dest : Pointer (Option Provenance))
    (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) : State → Prop :=
  CopyMemoryWP.copyPreUsing (accessPre config) config addresses arithmetic source dest size repeatCount
    nonoverlapping post onError

theorem copyPre_eq [DecidableEq K] (config : Config) (addresses : U → AllocAddresses.GlobalAddressState)
    (arithmetic : PointerArithmetic) (source dest : Pointer (Option Provenance))
    (size : Size) (repeatCount : UInt64) (nonoverlapping : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    RvalueWP.actionPre (GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest size
      repeatCount nonoverlapping) post onError =
    copyPre config addresses arithmetic source dest size repeatCount nonoverlapping post onError := by
  rw [CopyMemoryWP.copyPre_eq]
  unfold CopyMemoryWP.copyPre copyPre
  congr 1
  funext write allocation id provenance range post onError
  exact accessPre_eq config write allocation id provenance range post onError

/-- Keep the postconditions abstract so this rewrite applies under an
intrinsic's continuation, before its final postcondition is supplied. -/
theorem copyActionPre_eq [DecidableEq K] (config : Config)
    (addresses : U → AllocAddresses.GlobalAddressState) (arithmetic : PointerArithmetic)
    (source dest : Pointer (Option Provenance)) (size : Size) (repeatCount : UInt64)
    (nonoverlapping : Bool) :
    RvalueWP.actionPre (GlobalMemoryCopyMachine.genericCopy config addresses arithmetic source dest size
      repeatCount nonoverlapping) =
    copyPre config addresses arithmetic source dest size repeatCount nonoverlapping :=
  funext fun post => funext fun onError =>
    copyPre_eq config addresses arithmetic source dest size repeatCount nonoverlapping post onError

/-- Production copy-intrinsic dispatch selects the same tree-aware
continuation with one physical copy repetition. -/
theorem intrinsicCopyPre_eq {C O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (choice : C)
    (source dest : Pointer (Option Provenance)) (size : Size) (nonoverlapping : Bool) :
    RvalueWP.actionPre
        ((ExecutionMachine.memoryIntrinsicHooks config).memCopy choice source dest size nonoverlapping) =
      copyPre config.access config.addresses config.arithmetic source dest size 1 nonoverlapping := by
  rw [EffectSpecs.canonical_intrinsic_copy]
  exact copyActionPre_eq config.access config.addresses config.arithmetic source dest size 1 nonoverlapping

/-- Reduce a selected copy statement through concrete memory checks to the
tree-aware copy continuation. The memory-only tactic
`miri_copy_memory_wp` instead leaves the two copy access hooks as actions. -/
macro "miri_copy_tree_wp" : tactic =>
  `(tactic| simp only [NondivergingIntrinsicWP.statementPre_intrinsic, NondivergingIntrinsicWP.evalPre,
    NondivergingIntrinsicWP.copyPre, copyActionPre_eq, intrinsicCopyPre_eq])

/-- Open a tracked access after supplying its ready policy state and checked
range geometry. The explicit arguments select the actual policy results. -/
macro "miri_copy_tree_wp" &"observe" "using" ready:term "," formed:term "," endpoint:term ","
    bound:term : tactic =>
  `(tactic| rw [accessPre_observe_iff _ _ _ _ _ _ _ $ready _ $formed $endpoint $bound])

end Miri.Verification.CopyTreeWP

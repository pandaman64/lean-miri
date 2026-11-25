import Miri.Verification.CopyLoadObservationWP
import Miri.Verification.TreeObservationWP

/-! Initial-state normalization for an ordered copy and its successor. -/
namespace Miri.Verification.CopyInitialWP

open Miri.ABI Miri.Interpreter Miri.Memory Miri.TreeBorrows

variable {K U : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "Alloc" => Allocation Provenance BorrowTree

/-- An observation can alias either earlier access. The last write wins if
all three IDs agree. Otherwise the source access's retained tree is visible
only at its own allocation ID. -/
@[miri_initial_wp] theorem lookup_after_copy_accesses
    (memory : MemoryState Provenance BorrowTree K) (read write observe : AllocId)
    (readEntry writeEntry : LocalAllocation Provenance BorrowTree K) :
    ((memory.live.insert read readEntry).insert write writeEntry)[observe]? =
      if observe = write then some writeEntry
      else if observe = read then some readEntry else memory.live[observe]? := by
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert]
  simp only [Std.compare_eq_iff_eq, eq_comm (a := write) (b := observe),
    eq_comm (a := read) (b := observe)]

/-- A successful checked load at any ID obtains its bytes from the selected
initial image. Its permission check uses the actual selected allocation and
the success and failure continuations retain the interpreter's machine. -/
theorem scalarLoadFromImage [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (before : State) (place : MemPlace Provenance)
    (primitive : BackendPrimitive) (validRange : WrappingRange)
    (checked : MemoryWP.CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨place, localMemoryLayout operand.layout⟩)
    (entry : LocalAllocation Provenance BorrowTree K)
    (live : checked.rawMemory.live[checked.resolved.allocId]? = some entry)
    (indirect : operand.op = .indirect place)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.runtime = .ok (localMemoryLayout operand.layout).size)
    (aligned : place.misaligned = none)
    (range : AllocRange)
    (component : (allocRange checked.resolved.offset (localMemoryLayout operand.layout).size).subrange
      (allocRange Size.ZERO (localMemoryLayout operand.layout).size) = .ok range)
    (finish : Size) (image : Array UInt8)
    (full : checked.allocation.getBytesUnchecked
      (allocRange Size.ZERO checked.allocation.byteSize) = .ok image)
    (endpoint : range.endExclusive = .ok finish)
    (ordered : range.start.bytes.toNat ≤ finish.bytes.toNat)
    (bound : finish.bytes.toNat ≤ checked.allocation.byteSize.bytes.toNat)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    MemoryWP.immediateReadPre config operand before post onError =
      CopyLoadObservationWP.selectedScalarImagePre config operand before primitive
        checked.accessHooks checked.rawMemory checked.resolved.allocId checked.resolved.extra
        checked.resolved.offset entry checked.allocation range
        (.ok (image.extract range.start.bytes.toNat finish.bytes.toNat)) post onError := by
  rw [CopyLoadObservationWP.liveScalarLoadPre config operand before place primitive validRange
    checked entry live indirect backend width aligned range component]
  unfold CopyLoadObservationWP.selectedScalarLoadPre
  rw [Allocation.Bridge.getBytesUnchecked_eq_extract _ _ _ _ full endpoint ordered bound]

/-- Normalize the access checks after the concrete policy results are known.
An error still receives the partially updated tree on the exact path. -/
theorem trackedAccessPre [DecidableEq K] (config : Config) (write : Bool)
    (allocation : Alloc) (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (before : State) (ready : CopyTreeWP.Ready config write id range before)
    (post : Alloc → State → Prop) (onError : StepError → State → Prop) :
    CopyTreeWP.accessPre config write allocation id provenance range post onError before ↔
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
  rw [← CopyTreeWP.accessPre_eq, RvalueWP.actionPre_eq_wp]
  exact CopyTreeWP.access_iff config write allocation id provenance range before ready post onError

/-- A checked access with a rejecting error continuation can be proved from
the permission of each initial byte even when its success continuation also
needs the committed tree for later machine work. -/
theorem accessPre_checkedBytes (tree : BorrowTree) (provenance : ProvenanceExtra)
    (offset length finish : Size) (kind : AccessKind) (tags : ProtectedTags)
    (mode : Tree.ChildrenVisitMode) (formed : tree.locations.WellFormed)
    (endpoint : offset.add length = .ok finish) (bound : finish.bytes ≤ tree.locations.size.bytes)
    (post : BorrowTree → TreeRangeOutcomeWP.Trace → Prop) :
    TreeBorrowsWP.accessPre tree provenance offset length kind tags mode post (fun _ _ _ => False) ↔
      TreeOverlapWP.accessBytePre tree provenance offset length ⟨offset.bytes, finish.bytes⟩
        kind tags mode (fun trace after => post after trace) :=
  (TreeRangeOutcomeWP.wp_access_outcomePre_iff tree provenance offset length kind tags mode
    (fun trace after => post after trace) (fun _ _ => False)).symm.trans
    (TreeOverlapWP.wp_access_bytes_iff tree provenance offset length _ kind tags mode formed endpoint bound _)

private theorem size_mul_one (size : Size) : size.mul 1 = .ok size := by
  cases size
  simp only [Size.mul, UInt64.mul_one, UInt64.div_one, bne_self_eq_false,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, Size.ofBytes]

private theorem append_one_copy (bytes : Array UInt8) :
    (forIn (m := Id) [:UInt64.toNat 1] #[] fun _ acc =>
      pure (ForInStep.yield (acc ++ bytes))) = bytes := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  change (#[] ++ bytes) = bytes
  exact Array.empty_append

private theorem copyAccessCommitPre_live [DecidableEq K] (config : Config) (before : State)
    (allocation : Alloc) (id : AllocId) (range : AllocRange)
    (state : PlaceMachine.AccessState K U) (tree : BorrowTree)
    (entry : LocalAllocation Provenance BorrowTree K) (live : state.machine.memory.live[id]? = some entry)
    (outcome : Except String Unit) (post : Alloc → State → Prop) (onError : StepError → State → Prop) :
    MemoryWP.copyAccessCommitPre config before allocation id range state tree outcome post onError =
      let updated := allocation.setExtra tree
      let memory := {state.machine.memory with live :=
        (state.machine.memory.live.insert id {entry with allocation := updated})}
      let after := {before with machine := (config.retainTouched {state.machine with memory}
        (some ⟨id, range, updated⟩))}
      match outcome with
      | .ok () => post updated after
      | .error message => onError (state.pendingError.getD (.callback message)) after :=
  propext (CopyTreeWP.commitLocal_iff config before allocation id range state tree entry live outcome post onError)

/-- Open the exact copy and observer continuations under the current policy
and geometry hypotheses. Symbolic allocation IDs remain as case splits. -/
macro "miri_copy_initial_wp" : tactic =>
  `(tactic| first
    | (simp (disch := assumption) only [
        lookup_after_copy_accesses, CopyLoadObservationWP.liveLookup_insert,
        CopyLoadObservationWP.copyCommit_eq, CopyLoadObservationWP.copyCommitPre,
        Allocation.splice_getElem?, and_true, true_and, ↓reduceIte, *]; done)
    | (simp only [CopyLoadObservationWP.wp_copyThenLoad, CopyTreeWP.copyPre,
        CopyMemoryWP.copyPreUsing, CopyMemoryWP.pointerPre, CopyMemoryWP.memoryHookPre, *]; done)
    | simp (config := { failIfUnchanged := false }) (disch := assumption) only [
    lookup_after_copy_accesses, CopyLoadObservationWP.liveLookup_insert,
    CopyLoadObservationWP.copyCommit_eq, CopyLoadObservationWP.copyCommitPre,
    CopyLoadObservationWP.getAllocRaw_insert, MemoryLifecycle.getAllocRawFromLookup,
    MemoryObservationWP.readScalar_eq_image, accessPre_checkedBytes, TreeOverlapWP.accessPre_byteObservation_iff,
    CopyLoadObservationWP.wp_copyThenLoad,
    CopyTreeWP.intrinsicCopyPre_eq, CopyTreeWP.copyActionPre_eq,
    CopyTreeWP.copyPre, CopyMemoryWP.copyPreUsing, CopyMemoryWP.pointerPre,
    CopyMemoryWP.allocationHookPre, CopyMemoryWP.memoryHookPre, CopyMemoryWP.rawPre,
    CopyMemoryWP.snapshotPre, CopyTreeWP.accessPre, MemoryWP.memoryAccessPre,
    MemoryWP.policyPre, MemoryWP.failurePre, copyAccessCommitPre_live,
    MemoryWP.copyAccessCommitPre, Std.ExtTreeMap.contains_eq_isSome_getElem?,
    MemoryState.setLiveAllocation_eq_lookup, MemoryLifecycle.getAllocRaw_eq_lookup,
    MemoryLifecycle.getAllocRawMut,
    MemoryWP.immediateReadPre, MemoryWP.rawOperandPre, MemoryWP.placeAccessPre,
    MemoryWP.pointerAccessPre, MemoryWP.accessResultPre, MemoryWP.resultPre,
    AllocationAccess.finishCheckedAccess, AllocationAccess.preparePtrAllocation,
    selectedSizeAndAlign, isPrimitiveReadable, finishPlaceAccess, readImmediateAfterAccess_scalar,
    finishRawOperandRead, finishImmediateRead,
    Except.map, Except.mapError, Option.getD,
    Allocation.Bridge.copyRepeatedlyPre, Allocation.Bridge.prepareCopyOverwrite_eq,
    Allocation.Bridge.overwriteCopyBytes_eq, Allocation.Bridge.rawBytes_eq_fullImage,
    Allocation.setExtra, Allocation.mapExtra, Allocation.splice_getElem?, size_mul_one, append_one_copy,
    Allocation.Bridge.getBytesUnchecked_eq_extract, CopyLoadObservationWP.selectedScalarLoadPre,
    CopyLoadObservationWP.selectedScalarImagePre,
    Std.compare_eq_iff_eq, beq_self_eq_true, beq_iff_eq, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.false_eq_true, dite_true, dite_false,
    ↓reduceIte, *])

end Miri.Verification.CopyInitialWP

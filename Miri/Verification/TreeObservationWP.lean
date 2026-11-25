import Miri.Verification.TreeOverlapWP
import Miri.Verification.InitialWPAttr

/-! Compose a ranged Tree Borrows read and write with a third access. -/
namespace Miri.Verification.TreeObservationWP

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Std.WP
open BorrowTree TreeRangeOutcomeWP

structure Access where
  provenance : ProvenanceExtra
  offset : Size
  length : Size
  tags : ProtectedTags
  mode : Tree.ChildrenVisitMode

abbrev Traces := (Trace × Trace) × Trace
abbrev ByteLocations := UInt64 → LocationTree → Prop

/-- Execute the third access on the state committed by both earlier accesses. -/
def readWriteObserve (read write observe : Access) (kind : AccessKind) :
    EStateM RangeAccessError BorrowTree Traces := do
  let first ← (do
    let reads ← TreeBorrowsWP.access read.provenance read.offset read.length .Read read.tags read.mode
    let writes ← TreeBorrowsWP.access write.provenance write.offset write.length .Write write.tags write.mode
    pure (reads, writes))
  let observed ← TreeBorrowsWP.access observe.provenance observe.offset observe.length kind observe.tags observe.mode
  pure (first, observed)

/-- The exact continuation passes the first failing access's own trace and
retained tree to the caller, and passes all three traces on success. -/
def readWriteObservePre (tree : BorrowTree) (read write observe : Access) (kind : AccessKind)
    (post : Traces → BorrowTree → Prop) (failure : RangeAccessError → BorrowTree → Prop) : Prop :=
  readWritePre tree read.provenance write.provenance read.offset read.length write.offset write.length
    read.tags write.tags read.mode write.mode (fun first after =>
      TreeBorrowsWP.accessPre after observe.provenance observe.offset observe.length kind observe.tags observe.mode
        (fun final observed => post (first, observed) final)
        (fun status retained visited => failure (status, visited) retained)) failure

@[miri_initial_wp]
theorem wp_readWriteObserve_iff (tree : BorrowTree) (read write observe : Access) (kind : AccessKind)
    (post : Traces → BorrowTree → Prop) (failure : RangeAccessError → BorrowTree → Prop) :
    wp (readWriteObserve read write observe kind) post failure tree ↔
      readWriteObservePre tree read write observe kind post failure := by
  simp only [readWriteObserve, wp_pair_bind_iff, wp_access_outcomePre_iff, readWriteObservePre, readWritePre]

/-- A byte interpretation of one successful access. The old byte relation can
itself be the interpretation of an earlier access. -/
def Access.observeBytes (access : Access) (tree : BorrowTree) (finish : Size) (kind : AccessKind)
    (before : ByteLocations) : ByteLocations :=
  TreeOverlapWP.afterAccessFrom tree access.provenance kind ⟨access.offset.bytes, finish.bytes⟩
    access.tags access.mode before

/-- Check a single access's byte permissions. Its continuation can inspect the
successful trace, tree, and the partition facts needed for the following access. -/
def Access.bytePre (access : Access) (tree : BorrowTree) (finish : Size) (kind : AccessKind)
    (post : Trace → BorrowTree → Prop) : Prop :=
  TreeOverlapWP.accessBytePre tree access.provenance access.offset access.length
    ⟨access.offset.bytes, finish.bytes⟩ kind access.tags access.mode
    (fun trace after =>
      after = { tree with locations := after.locations } ∧
      after.locations.WellFormed ∧ after.locations.size = tree.locations.size ∧
      (∀ byte data, after.locations.MapAt byte data ↔ access.observeBytes tree finish kind tree.locations.MapAt byte data) ∧
      post trace after)

private theorem Access.bytePre_congr (access : Access) (tree : BorrowTree) (finish : Size)
    (kind : AccessKind) {left right : Trace → BorrowTree → Prop}
    (same : ∀ trace after, after = { tree with locations := after.locations } →
      after.locations.WellFormed → after.locations.size = tree.locations.size →
      (∀ byte data, after.locations.MapAt byte data ↔ access.observeBytes tree finish kind tree.locations.MapAt byte data) →
      (left trace after ↔ right trace after)) :
    access.bytePre tree finish kind left ↔ access.bytePre tree finish kind right := by
  unfold Access.bytePre TreeOverlapWP.accessBytePre TreeOverlapWP.byteChecks
  constructor
  · rintro ⟨⟨tag, checks⟩, backbone, formed, size, locations, done⟩
    exact ⟨⟨tag, checks⟩, backbone, formed, size, locations, (same _ _ backbone formed size locations).mp done⟩
  · rintro ⟨⟨tag, checks⟩, backbone, formed, size, locations, done⟩
    exact ⟨⟨tag, checks⟩, backbone, formed, size, locations, (same _ _ backbone formed size locations).mpr done⟩

private theorem Access.wp_bytePre_iff (access : Access) (tree : BorrowTree) (finish : Size)
    (kind : AccessKind) (formed : tree.locations.WellFormed)
    (checkedEnd : access.offset.add access.length = .ok finish)
    (bound : finish.bytes ≤ tree.locations.size.bytes) (post : Trace → BorrowTree → Prop) :
    wp (TreeBorrowsWP.access access.provenance access.offset access.length kind access.tags access.mode)
      post (fun _ _ => False) tree ↔ access.bytePre tree finish kind post := by
  rw [TreeOverlapWP.wp_access_bytes_iff _ _ _ _ _ _ _ _ formed checkedEnd bound]
  exact TreeOverlapWP.accessBytePre_observe _ _ _ _ _ _ _ _ formed checkedEnd bound post

/-- The observation begins at the initial byte partition. Each access changes
the byte only when it covers it, in read, write, then observation order. -/
def observedBytes (tree : BorrowTree) (read write observe : Access) (kind : AccessKind)
    (readFinish writeFinish observeFinish : Size) : ByteLocations :=
  observe.observeBytes tree observeFinish kind
    (write.observeBytes tree writeFinish .Write (read.observeBytes tree readFinish .Read tree.locations.MapAt))

/-- With checked endpoints and a well-formed initial partition, successful
permission checks expose the final byte relation directly from initial bytes. -/
theorem wp_readWriteObserve_bytes_iff (tree : BorrowTree) (read write observe : Access) (kind : AccessKind)
    (readFinish writeFinish observeFinish : Size) (formed : tree.locations.WellFormed)
    (readEnd : read.offset.add read.length = .ok readFinish)
    (writeEnd : write.offset.add write.length = .ok writeFinish)
    (observeEnd : observe.offset.add observe.length = .ok observeFinish)
    (readBound : readFinish.bytes ≤ tree.locations.size.bytes)
    (writeBound : writeFinish.bytes ≤ tree.locations.size.bytes)
    (observeBound : observeFinish.bytes ≤ tree.locations.size.bytes)
    (post : Traces → ByteLocations → Prop) :
    wp (readWriteObserve read write observe kind)
      (fun traces final => post traces final.locations.MapAt) (fun _ _ => False) tree ↔
    read.bytePre tree readFinish .Read (fun reads afterRead =>
      write.bytePre afterRead writeFinish .Write (fun writes afterWrite =>
        observe.bytePre afterWrite observeFinish kind (fun observed _ =>
          post ((reads, writes), observed)
            (observedBytes tree read write observe kind readFinish writeFinish observeFinish)))) := by
  simp only [readWriteObserve, wp_pair_bind_iff]
  rw [read.wp_bytePre_iff tree readFinish .Read formed readEnd readBound]
  apply read.bytePre_congr
  intro reads afterRead readTree readFormed readSize readMap
  rw [write.wp_bytePre_iff afterRead writeFinish .Write readFormed writeEnd (readSize.symm ▸ writeBound)]
  apply write.bytePre_congr
  intro writes afterWrite writeTree writeFormed writeSize writeMap
  rw [observe.wp_bytePre_iff afterWrite observeFinish kind writeFormed observeEnd
    ((writeSize.trans readSize).symm ▸ observeBound)]
  apply observe.bytePre_congr
  intro observed final _ _ _ observeMap
  have sameRead : afterRead.locations.MapAt =
      read.observeBytes tree readFinish .Read tree.locations.MapAt :=
    funext fun byte => funext fun data => propext (readMap byte data)
  have sameWrite : afterWrite.locations.MapAt =
      write.observeBytes tree writeFinish .Write (read.observeBytes tree readFinish .Read tree.locations.MapAt) := by
    have same := funext fun byte => funext fun data => propext (writeMap byte data)
    rw [same, sameRead]
    cases afterRead
    simp only at readTree
    rw [readTree]
    rfl
  have sameObserve : final.locations.MapAt =
      observedBytes tree read write observe kind readFinish writeFinish observeFinish := by
    have same := funext fun byte => funext fun data => propext (observeMap byte data)
    rw [same, sameWrite]
    cases afterWrite
    simp only at writeTree
    rw [writeTree]
    cases afterRead
    simp only at readTree
    rw [readTree]
    rfl
  rw [sameObserve]

/-- The endpoint certifies the byte-range interpretation of the access. The
interpreter still uses the original offset and length. -/
structure PlannedAccess extends Access where
  kind : AccessKind
  finish : Size

def runPlan : List PlannedAccess → EStateM RangeAccessError BorrowTree Unit
  | [] => pure ()
  | access :: rest => do
    let _ ← TreeBorrowsWP.access access.provenance access.offset access.length
      access.kind access.tags access.mode
    runPlan rest

/-- Check all accesses against the initial tree topology. Carry only the
byte-local permissions and exposure caches from one access to the next. -/
def planBytePre (tree : BorrowTree) (post : ByteLocations → Prop) :
    List PlannedAccess → ByteLocations → Prop
  | [], before => post before
  | access :: rest, before =>
    TreeOverlapWP.byteChecks tree access.provenance ⟨access.offset.bytes, access.finish.bytes⟩
        access.kind access.tags access.mode before ∧
      planBytePre tree post rest (access.toAccess.observeBytes tree access.finish access.kind before)

private theorem planBytePre_replaceLocations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (post : ByteLocations → Prop) (plan : List PlannedAccess) (before : ByteLocations) :
    planBytePre { tree with locations } post plan before ↔ planBytePre tree post plan before := by
  induction plan generalizing before with
  | nil => rfl
  | cons access rest ih =>
    simp only [planBytePre, Access.observeBytes, TreeOverlapWP.byteChecks_replaceLocations,
      TreeOverlapWP.afterAccessFrom_replaceLocations]
    exact and_congr_right fun _ => ih _

/-- For a sequence whose postcondition reads only byte locations, discharge
every access against the initial partition and the preceding local updates. -/
theorem wp_plan_bytes_iff (tree : BorrowTree) (plan : List PlannedAccess)
    (formed : tree.locations.WellFormed)
    (ends : ∀ access ∈ plan, access.offset.add access.length = .ok access.finish)
    (bounds : ∀ access ∈ plan, access.finish.bytes ≤ tree.locations.size.bytes)
    (post : ByteLocations → Prop) :
    wp (runPlan plan) (fun _ final => post final.locations.MapAt) (fun _ _ => False) tree ↔
      planBytePre tree post plan tree.locations.MapAt := by
  induction plan generalizing tree with
  | nil => rfl
  | cons access rest ih =>
    let first := TreeBorrowsWP.access access.provenance access.offset access.length
      access.kind access.tags access.mode
    have checkedEnd := ends access (.head _)
    have bound := bounds access (.head _)
    have headWP :
        wp (runPlan (access :: rest)) (fun _ final => post final.locations.MapAt) (fun _ _ => False) tree ↔
        wp first (fun _ next => wp (runPlan rest) (fun _ final => post final.locations.MapAt)
          (fun _ _ => False) next) (fun _ _ => False) tree := by
      simp only [runPlan, wp, WP.wpTrans, bind, Bind.bind, EStateM.bind]
      dsimp only [first]
      cases TreeBorrowsWP.access access.provenance access.offset access.length
        access.kind access.tags access.mode tree <;> rfl
    rw [headWP, access.toAccess.wp_bytePre_iff tree access.finish access.kind formed checkedEnd bound]
    calc
      _ ↔ access.toAccess.bytePre tree access.finish access.kind
          (fun _ after => planBytePre tree post rest after.locations.MapAt) := by
        apply access.toAccess.bytePre_congr
        intro trace after backbone nextFormed nextSize _
        rw [ih after nextFormed (fun next included => ends next (.tail _ included))
          (fun next included => nextSize.symm ▸ bounds next (.tail _ included))]
        exact (congrArg (fun t => planBytePre t post rest after.locations.MapAt) backbone).to_iff.trans
          (planBytePre_replaceLocations tree after.locations post rest after.locations.MapAt)
      _ ↔ _ := by
        rw [← access.toAccess.wp_bytePre_iff tree access.finish access.kind formed checkedEnd bound,
          TreeOverlapWP.wp_access_byteObservation_iff _ _ _ _ _ _ _ _ formed checkedEnd bound]
        rfl

attribute [miri_initial_wp] TreeOverlapWP.wp_access_byteObservation_iff
  TreeOverlapWP.accessPre_byteObservation_iff wp_plan_bytes_iff

macro "miri_tree_range_wp" &"observe" : tactic =>
  `(tactic| simp (disch := assumption) only [wp_plan_bytes_iff,
    TreeOverlapWP.wp_access_byteObservation_iff, TreeOverlapWP.accessPre_byteObservation_iff,
    wp_readWriteObserve_iff])

end Miri.Verification.TreeObservationWP

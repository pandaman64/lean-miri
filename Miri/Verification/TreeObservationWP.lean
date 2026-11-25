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

private theorem wp_bind_iff {E S A B : Type} (first : EStateM E S A) (next : A → EStateM E S B)
    (post : B → S → Prop) (failure : E → S → Prop) (before : S) :
    wp (first >>= next) post failure before ↔
      wp first (fun value after => wp (next value) post failure after) failure before := by
  simp only [wp, WP.wpTrans, bind, Bind.bind, EStateM.bind]
  cases first before <;> rfl

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
    have checkedEnd := ends access (.head _)
    have bound := bounds access (.head _)
    simp only [runPlan, wp_bind_iff]
    rw [access.toAccess.wp_bytePre_iff tree access.finish access.kind formed checkedEnd bound]
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

private theorem wp_pure_iff {E S A : Type} (value : A) (post : A → S → Prop)
    (failure : E → S → Prop) (before : S) :
    wp (pure value : EStateM E S A) post failure before ↔ post value before := Iff.rfl

private def planAccessPre (post : ByteLocations → Prop) :
    List PlannedAccess → BorrowTree → Prop
  | [], before => post before.locations.MapAt
  | step :: rest, before =>
    TreeBorrowsWP.accessPre before step.provenance step.offset step.length step.kind step.tags step.mode
      (fun after _ => planAccessPre post rest after) (fun _ _ _ => False)

private theorem wp_plan_accessPre_iff (plan : List PlannedAccess)
    (post : ByteLocations → Prop) (tree : BorrowTree) :
    wp (runPlan plan) (fun _ final => post final.locations.MapAt) (fun _ _ => False) tree ↔
      planAccessPre post plan tree := by
  induction plan generalizing tree with
  | nil => rfl
  | cons step rest ih =>
    simp only [runPlan, wp_bind_iff, wp_access_outcomePre_iff, planAccessPre, ih]

private theorem planAccessPre_bytes_iff (tree : BorrowTree) (plan : List PlannedAccess)
    (formed : tree.locations.WellFormed)
    (ends : ∀ access ∈ plan, access.offset.add access.length = .ok access.finish)
    (bounds : ∀ access ∈ plan, access.finish.bytes ≤ tree.locations.size.bytes)
    (post : ByteLocations → Prop) :
    planAccessPre post plan tree ↔ planBytePre tree post plan tree.locations.MapAt :=
  (wp_plan_accessPre_iff plan post tree).symm.trans (wp_plan_bytes_iff tree plan formed ends bounds post)

open Lean Meta Elab Tactic in
/-- Recognize linear access continuations with a byte-only postcondition.
Checked endpoints come from local facts. Definitional equality verifies the
whole reified plan before the byte-fold equivalence is applied. -/
elab "miri_observe_linear_accesses" : tactic => withMainContext do
  evalTactic (← `(tactic| first | simp only [wp_bind_iff, wp_pure_iff, wp_access_outcomePre_iff] | skip))
  withMainContext do
    let goal ← getMainGoal
    let mut current := (← instantiateMVars (← goal.getType)).consumeMData
    unless current.getAppFn.isConstOf ``TreeBorrowsWP.accessPre do
      throwError "expected a linear Tree Borrows access continuation"
    let some before := current.getAppArgs[0]?
      | throwError "missing initial borrow tree"
    let mut accesses := #[]
    let mut finalPost := none
    repeat
      let args := current.getAppArgs
      let #[_, provenance, offset, length, kind, tags, mode, success, failure] := args
        | throwError "expected a complete Tree Borrows access"
      let .lam _ _ (.lam _ _ (.lam _ _ fail _) _) _ := failure.consumeMData
        | throwError "expected a failure continuation that rejects every error"
      unless fail.consumeMData.isConstOf ``False do
        throwError "the byte fold is for failure-rejecting continuations"
      unless !(#[provenance, offset, length, kind, tags, mode].any Expr.hasLooseBVars) do
        throwError "an access depends on an earlier state or trace"
      let finish ← mkFreshExprMVar (some (mkConst ``Size))
      let ending ← mkAppM ``Size.add #[offset, length]
      let successfulEnd ← mkAppOptM ``Except.ok #[some (mkConst ``SizeError), some (mkConst ``Size), some finish]
      let some _ ← findLocalDeclWithType? (← mkEq ending successfulEnd)
        | throwError "missing checked endpoint for offset {offset} and length {length}"
      let finish ← instantiateMVars finish
      let access ← mkAppM ``Access.mk #[provenance, offset, length, tags, mode]
      accesses := accesses.push (← mkAppM ``PlannedAccess.mk #[access, kind, finish])
      let .lam _ _ (.lam _ _ body _) _ := success.consumeMData
        | throwError "expected a state and trace continuation"
      let body := body.consumeMData
      if body.getAppFn.isConstOf ``TreeBorrowsWP.accessPre then
        current := body
      else
        finalPost ← lambdaTelescope success fun args body => do
          let #[after, trace] := args | throwError "expected the final state and trace"
          let locations ← mkAppM ``BorrowTree.locations #[after]
          let mapAt ← mkAppM ``DedupRangeMap.MapAt #[locations]
          let post := mkLambda `locations BinderInfo.default (mkConst ``ByteLocations) (← kabstract body mapAt)
          if post.hasLooseBVars || post.containsFVar after.fvarId! || post.containsFVar trace.fvarId! then
            throwError "the final continuation must inspect only the byte map"
          pure (some post)
        break
    let some post := finalPost | throwError "missing final byte observation"
    let plan ← mkListLit (mkConst ``PlannedAccess) accesses.toList
    let goal ← goal.change (← mkAppM ``planAccessPre #[post, plan, before])
    let rule := mkApp2 (mkConst ``planAccessPre_bytes_iff) before plan
    let (prerequisites, _, _) ← forallMetaTelescopeReducing (← inferType rule) (some 3)
    let law := mkAppN rule (prerequisites.push post)
    let result ← goal.apply (← mkAppM ``Iff.mpr #[law])
    replaceMainGoal (prerequisites.toList.map Expr.mvarId! ++ result)
    evalTactic (← `(tactic| (
      · assumption
      · simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
        repeat' apply And.intro
        all_goals first | assumption | exact List.forall_mem_nil _
      · simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
        repeat' apply And.intro
        all_goals first | assumption | exact List.forall_mem_nil _)))

attribute [miri_initial_wp] TreeOverlapWP.wp_access_byteObservation_iff
  TreeOverlapWP.accessPre_byteObservation_iff wp_plan_bytes_iff

macro "miri_tree_range_wp" &"observe" : tactic =>
  `(tactic| first
    | miri_observe_linear_accesses
    | simp (disch := assumption) only [wp_plan_bytes_iff, TreeOverlapWP.wp_access_byteObservation_iff,
        TreeOverlapWP.accessPre_byteObservation_iff, wp_readWriteObserve_iff,
        wp_bind_iff, wp_pure_iff, wp_access_outcomePre_iff])

end Miri.Verification.TreeObservationWP

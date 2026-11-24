import VerifyCanonicalSafety
import duplicate_prefix.RootGuardRelevance
import duplicate_prefix.PhysicalMachineWrite
import duplicate_prefix.GeneralBorrowProjection
import Miri.Input.InitialMachine

open Miri Miri.ABI Miri.Interpreter Miri.Input Miri.Memory Miri.MIR Miri.TreeBorrows
open Miri.Concurrency Miri.Memory.AllocAddresses Miri.Verification
open DuplicatePrefix

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

namespace DuplicatePrefix.PreparedCallWitness

abbrev State := MachineHooks.State MiriMemoryKind Machine.RootUser
def srcId : AllocId := ⟨1, by decide⟩
def srcTag : BorTag := ⟨1, by decide⟩
def host : Machine.MinimalHost := ⟨⟨0,0,0,.virtual 0,0,false⟩,#[]⟩
def storage : MachineGCRoots.Storage Unit Unit Unit Unit Unit Unit Unit where
  threads := {affinity:=none}
  tls := ⟨ThreadTlsData.initial,#[],#[]⟩
  errnoPlaces := #[]
  unwindPayloads := .empty
  extras := {allocations:=#[(srcId,{weakMemory:=none})]}
  environment := .uninit
  directories := {}
  descriptors := {}
  ownership := {}
  entry := ⟨none,none,none,none⟩
  externStatics := {}
def world : EvalWorld.World Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost where
  runtime := storage
  main := none
  types := {PreparedReflection.actual.types with entries:=#[]}
  functions := ⟨#[],#[]⟩
  vtables := ⟨#[]⟩
  choices := {inputs:=#[]}
  backend := .none
  host := host
def addresses : GlobalAddressState where
  intToPtrMap := #[⟨4096,srcId⟩]
  baseAddr := #[⟨srcId,4096⟩]
  provenanceMode := .permissive
  addressMode := .managed
  generation := some ⟨⟨12288,9223372036854775807⟩,⟨0,0,#[]⟩⟩
def limits : ExecutionMachine.Limits := ⟨1024,1024,1024,1024⟩
def options := Machine.exampleOptions limits 1024 1024 1024 1024 .Shallow ⟨false,false⟩
def srcPointer : Pointer (Option Provenance) :=
  Pointer.new (some (.concrete srcId srcTag)) (Size.ofBytes 4096)
def destination : MPlaceTy Provenance :=
  ⟨⟨Pointer.new (some (.concrete srcId srcTag)) (Size.ofBytes 4096), .none, none⟩,
    RootCompilerFacts.boolLayout⟩


open CanonicalCallDomain SourceDomain PreparedArguments
open Miri.DataStructures Miri.TreeBorrows.Tree
open BorrowRangeAccess

private theorem caseIndex (index : UniIndex) (b : index.toNat < 2) :
    index = ⟨0⟩ ∨ index = ⟨1⟩ := by
  have finite : index.toNat = 0 ∨ index.toNat = 1 := by omega
  rcases finite with n | n
  · exact .inl (Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
      ((congrArg UniIndex.ofNat? n).trans rfl)))
  · exact .inr (Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
      ((congrArg UniIndex.ofNat? n).trans rfl)))

private theorem nodeCases (root child : BorTag) (rows : DedupRangeMap LocationTree) (index : UniIndex)
    (node : TreeNode) (found : (canonicalChildTree root child rows).nodeAt index = some node) :
    index = ⟨0⟩ ∨ index = ⟨1⟩ := by
  by_cases valid : index.toNat < 2
  · exact caseIndex index valid
  · have size : index.toNat ≥ (canonicalChildTree root child rows).nodes.data.size := by
      change 2 ≤ index.toNat
      omega
    have missing := Array.getElem?_eq_none (xs := (canonicalChildTree root child rows).nodes.data) size
    simp [BorrowTree.nodeAt, UniValMap.get, missing] at found

/-- The simple two-node physical slot used by the production witness has
coherent topology for any well-formed location map. -/
private theorem canonicalChildCoherent (root child : BorTag) (rows : DedupRangeMap LocationTree)
    (ranges : rows.WellFormed) : CoherentForest (canonicalChildTree root child rows) := by
  let tree := canonicalChildTree root child rows
  refine ⟨ranges, by change 2 ≤ 2^32; decide, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro index member
    have rootIndex : index = ⟨0⟩ := by simpa [tree, canonicalChildTree] using member
    subst index
    exact ⟨_, rfl⟩
  · refine ⟨UniIndex.toNat, ?_, ?_⟩
    · intro index node found
      rcases nodeCases root child rows index node found with rfl | rfl
      · change 0 ≤ 2; decide
      · change 1 ≤ 2; decide
    · intro index node parent found relation
      rcases nodeCases root child rows index node found with rfl | rfl
      · change some _ = some node at found
        cases found
        contradiction
      · change some _ = some node at found
        cases found
        change some ⟨0⟩ = some parent at relation
        cases relation
        decide
  · intro index node found
    rcases nodeCases root child rows index node found with rfl | rfl <;>
      change some _ = some node at found <;> cases found
    · change (none : Option UniIndex) = none ↔ (⟨0⟩ : UniIndex) ∈ #[⟨0⟩]
      simp
    · change some (⟨0⟩ : UniIndex) = none ↔ (⟨1⟩ : UniIndex) ∈ #[⟨0⟩]
      have different : (⟨1⟩ : UniIndex) ≠ ⟨0⟩ := by decide
      simp [different]
  · intro index node found
    rcases nodeCases root child rows index node found with head | tail
    · subst index
      change some _ = some node at found
      cases found
      refine ⟨by simp, ?_, ?_⟩
      · intro listed member
        have equal : listed = ⟨1⟩ := by simpa using member
        subst listed
        exact ⟨_, rfl, rfl⟩
      · intro query data lookup edge
        rcases nodeCases root child rows query data lookup with rfl | rfl
        · change some _ = some data at lookup
          cases lookup
          contradiction
        · change (⟨1⟩ : UniIndex) ∈ #[⟨1⟩]
          simp
    · subst index
      change some _ = some node at found
      cases found
      refine ⟨by simp, ?_, ?_⟩
      · intro child member
        simp at member
      · intro query data lookup edge
        rcases nodeCases root child rows query data lookup with rfl | rfl <;>
          change some _ = some data at lookup <;> cases lookup
        · contradiction
        · change some (⟨0⟩ : UniIndex) = some ⟨1⟩ at edge
          have different : (⟨0⟩ : UniIndex) ≠ ⟨1⟩ := by decide
          exact (different (Option.some.inj edge)).elim
  · intro index node parent found edge
    rcases nodeCases root child rows index node found with rfl | rfl
    · change some _ = some node at found
      cases found
      contradiction
    · change some _ = some node at found
      cases found
      change some ⟨0⟩ = some parent at edge
      cases edge
      exact ⟨_, rfl⟩

private theorem fixtureDenseReady (root child : BorTag) :
    RetagInsertionCapacity.Ready (PhysicalMachineWrite.slotTree root child 2 false) := by
  let tree := PhysicalMachineWrite.slotTree root child 2 false
  refine ⟨?_, ?_, by simp, rfl, by change 2 < 2^32; decide, ?_⟩
  · intro key member
    change key ∈ #[(root, ⟨0⟩), (child, ⟨1⟩)] at member
    have cases : key = (root, ⟨0⟩) ∨ key = (child, ⟨1⟩) := by simpa using member
    rcases cases with rfl | rfl <;> exact ⟨_, rfl, rfl⟩
  · intro index member
    change index ∈ #[] at member
    simp at member
  · intro index absent position inside
    have large : 2 ≤ index.toNat := by
      by_cases large : 2 ≤ index.toNat
      · exact large
      · exfalso
        have finite : index.toNat = 0 ∨ index.toNat = 1 := by omega
        rcases finite with zero | one
        · have indexZero : index = ⟨0⟩ := Option.some.inj
            ((GeneralBorrowProjection.index_self index).symm.trans ((congrArg UniIndex.ofNat? zero).trans rfl))
          subst index
          change some _ = none at absent
          contradiction
        · have indexOne : index = ⟨1⟩ := Option.some.inj
            ((GeneralBorrowProjection.index_self index).symm.trans ((congrArg UniIndex.ofNat? one).trans rfl))
          subst index
          change some _ = none at absent
          contradiction
    have oneRow : tree.locations.entries.size = 1 := rfl
    have only : position = 0 := by
      change position < tree.locations.entries.size at inside
      omega
    subst position
    change (childLocation false).perms.get index = none
    unfold UniValMap.get
    have absentPerm := Array.getElem?_eq_none (xs := (childLocation false).perms.data)
      (by change 2 ≤ index.toNat; exact large)
    rw [absentPerm]

def heldTag : BorTag := ⟨32, by decide⟩
def borrowTracker : MachineHooks.BorrowState :=
  ⟨{nextPointerTag := ⟨33,by decide⟩, rootPointerTags := #[(srcId,srcTag)],
    protectedTags := ({} : ProtectedTags).insert heldTag .StrongProtector},.Default⟩

def owner : FrameState := {protectedTags := #[(srcId,heldTag)]}
def pointer : Pointer (Option Provenance) :=
  Pointer.new (some (.concrete srcId heldTag)) (Size.ofBytes 4096)

def allocation : Allocation Provenance Unit :=
  match e : Allocation.fromBytes (Prov := Provenance) #[11,22] Align.ONE .Mut with
  | .ok bytes => bytes
  | .error _ => False.elim (by
    have impossible : (Allocation.fromBytes (Prov := Provenance) #[11,22] Align.ONE .Mut).isOk = true := by decide
    rw [e] at impossible
    cases impossible)

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  ⟨.stack, allocation.withExtra (PhysicalMachineWrite.slotTree srcTag heldTag 2 false)⟩

abbrev ActualFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra
abbrev Slot := LocalState Provenance LocalLayout

def boolSlot : Slot := ⟨.live (.immediate (.scalar (.fromBool false))), some RootCompilerFacts.boolLayout⟩
def sliceBuffer : Immediate Provenance :=
  (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
    (Pointer.new (.concrete srcId heldTag) (Size.ofBytes 4096)) 2 RootCompilerFacts.sliceLayout).imm

theorem sliceBuffer_eq : Immediate.newSlice pointer 2 PreparedReflection.actual.runtime.target.base = .ok sliceBuffer :=
  RootZeroShallowReturn.concreteSliceImmediate pointer srcId heldTag 4096 0 2 rfl rfl

def slots (index : Nat) : Slot :=
  if index = 0 then ⟨.live (.immediate .uninit),none⟩
  else if index = 1 then ⟨.live (.immediate sliceBuffer),some RootCompilerFacts.sliceLayout⟩
  else if index = 2 then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 1)))),some RootCompilerFacts.usizeLayout⟩
  else ⟨(if #[6,13,14].contains index then .live (.immediate .uninit) else .dead),none⟩

def caller (program : BodyVCGen.LoadedProgram) : ActualFrame :=
  let frame : ActualFrame := Frame.create program.root program.rootInstance
    { userRelevance := 255, borrowTracker := some {}, catchUnwind := none, dataRace := none }
    (.stop true) (.memory destination) PreparedReflection.actual.dummySpan (.ofAllocationToken 0)
  {frame with location := .mir ⟨0,0⟩, locals := Array.ofFn (fun i : Fin 25 => if i.val = 0 then boolSlot else ⟨.dead,none⟩)}

def root (program : BodyVCGen.LoadedProgram) : ActualFrame :=
  let frame : ActualFrame := Frame.create program.root program.rootInstance
    { userRelevance := 255, borrowTracker := some owner, catchUnwind := none, dataRace := none }
    (.goto (some 1) .Continue) (.frameLocal 0 0 none RootCompilerFacts.boolLayout (caller program).localsIdentity)
    PreparedReflection.actual.dummySpan (.ofAllocationToken 1)
  {frame with location := .mir ⟨0,0⟩, locals := Array.ofFn (fun index : Fin 25 => slots index.val)}

def machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let mem : MemoryState Provenance BorrowTree MiriMemoryKind := MemoryState.empty.setIssuedIds #[srcId]
  let threads := ThreadManager.initial true
  let rows := threads.threads.set 0
    { ThreadRecord.initial none none with originSpanToken := PreparedReflection.actual.dummySpan.id, topUserRelevantFrame := some 1 }
  { memory := {mem with live := mem.live.insert srcId entry, nextAllocId := 2}
    borrowTracker := some borrowTracker, dataRace := none
    threads := {threads with threads := rows}
    raceAllocations := {}, allocationSpans := #[]
    user := ⟨addresses,
      ⟨⟨⟨ThreadId.MAIN_THREAD,#[]⟩,⟨2⟩,world⟩,.Shallow,.Int,false,#[]⟩,#[]⟩ }

def before (program : BodyVCGen.LoadedProgram) : State :=
  Storage.withCurrent #[caller program] (root program) machine

private theorem onlyAllocation (id : AllocId) (saved : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (lookup : machine.memory.live[id]? = some saved) : id = srcId ∧ saved = entry := by
  change (((∅ : Std.ExtTreeMap AllocId (LocalAllocation Provenance BorrowTree MiriMemoryKind)).insert srcId entry)[id]?
    = some saved) at lookup
  rw [Std.ExtTreeMap.getElem?_insert] at lookup
  split at lookup
  · rename_i key
    exact ⟨(Std.LawfulEqCmp.eq_of_compare key).symm, (Option.some.inj lookup).symm⟩
  · simp at lookup

private theorem lookupSource : machine.memory.live[srcId]? = some entry := by rfl

def storageRegion (program : BodyVCGen.LoadedProgram) : InitializedRegion (before program) 2 :=
  ⟨srcId, Size.ZERO, entry, lookupSource, rfl, rfl, by decide, fun _ => rfl⟩

theorem available : CopySourceResources entry := {
  keys := fixtureDenseReady srcTag heldTag
  room := by decide
  maskLength := rfl
  mask := True.intro
  provenance := by
    change ProvenanceCopy.WellFormed (ProvenanceMap.new (Prov := Provenance)) 2
    constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
  storageBound := by decide }

private theorem storedNode (index : UniIndex) (node : TreeNode)
    (found : entry.allocation.extra.nodeAt index = some node) : index = ⟨0⟩ ∨ index = ⟨1⟩ := by
  obtain ⟨n, actual⟩ : ∃ n, index.toNat = n ∧ n < 2 := by
    refine ⟨index.toNat,rfl,?_⟩
    by_cases small : index.toNat < 2
    · exact small
    exfalso
    have outside : 2 ≤ index.toNat := by omega
    have missing := Array.getElem?_eq_none (xs := entry.allocation.extra.nodes.data) (by change 2 ≤ index.toNat; exact outside)
    simp [BorrowTree.nodeAt,UniValMap.get,missing] at found
  have small : n = 0 ∨ n = 1 := by omega
  rcases small with rfl | rfl
  · exact .inl (Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
      ((congrArg UniIndex.ofNat? actual.1).trans rfl)))
  · exact .inr (Option.some.inj ((GeneralBorrowProjection.index_self index).symm.trans
      ((congrArg UniIndex.ofNat? actual.1).trans rfl)))

def sourceRights (program : BodyVCGen.LoadedProgram) :
    ExclusiveRegion (before program) 2 (storageRegion program) heldTag := by
  let tree := entry.allocation.extra
  refine ⟨borrowTracker,rfl,canonicalChildCoherent srcTag heldTag _
    (DedupRangeMap.new_wellFormed _ _),⟨1⟩,rfl,⟨_,rfl,rfl⟩,?_,?_⟩
  · intro distance smaller
    refine ⟨⟨⟨0,2⟩,childLocation false⟩, ?_, ?_, ?_⟩
    · change (⟨⟨0,2⟩,childLocation false⟩ : RangeMapSegment LocationTree) ∈ #[⟨⟨0,2⟩,childLocation false⟩]
      simp
    · change 0 ≤ 0 + distance
      omega
    · change 0 + distance < 2
      change distance < 2 at smaller
      simpa using smaller
  · intro distance smaller segment listed _ _ index node found
    have row : segment = ⟨⟨0,2⟩,childLocation false⟩ := by
      change segment ∈ #[⟨⟨0,2⟩,childLocation false⟩] at listed
      simpa using listed
    subst segment
    have path : Ancestor tree ⟨0⟩ ⟨1⟩ := .parent (.self _) _ rfl rfl
    rcases storedNode index node found with rfl | rfl
    · exact ⟨⟨.Unique,true,.None⟩,rfl,fun _ => ⟨rfl,trivial⟩,fun impossible => (impossible path).elim⟩
    · exact ⟨⟨.ReservedFrz false,true,.None⟩,rfl,fun _ => ⟨rfl,trivial⟩,fun impossible => (impossible (.self _)).elim⟩

theorem scope : ReleaseRange entry.allocation.extra ⟨1⟩ Size.ZERO 2 := by
  refine ⟨fun _ => ⟨⟨0⟩,rfl⟩, by decide, ?_, ?_⟩
  · intro segment listed _
    have row : segment = ⟨⟨0,2⟩,childLocation false⟩ := by
      change segment ∈ #[⟨⟨0,2⟩,childLocation false⟩] at listed
      simpa using listed
    subst segment
    decide
  · intro index absent segment listed
    obtain ⟨position, valid, rfl⟩ := Array.mem_iff_getElem.mp listed
    exact available.keys.rowVacant index absent position valid

#print axioms sourceRights

private theorem currentThread (program : BodyVCGen.LoadedProgram) :
    ∃ thread, (before program).machine.threads.activeThread? = some thread ∧
      thread.topUserRelevantFrame = some 1 := ⟨_,rfl,rfl⟩

private theorem liveAt {program : BodyVCGen.LoadedProgram} {index : Nat} {slot : Slot}
    (lookup : (root program).locals[index]? = some slot) : slot = slots index := by
  obtain ⟨inside, found⟩ := Array.getElem?_eq_some_iff.mp lookup
  rw [show (root program).locals[index] = slots index by simp [root]] at found
  exact found.symm

theorem compilerControl (program : BodyVCGen.LoadedProgram) :
    InitialCompilerControl (before program) (root program) := by
  refine ⟨rfl,rfl,currentThread program,?_⟩
  intro i slot after lookup
  rw [liveAt lookup]
  have not0 : i ≠ 0 := fun eq => (by decide : ¬ 3 ≤ 0) (eq ▸ after)
  have not1 : i ≠ 1 := fun eq => (by decide : ¬ 3 ≤ 1) (eq ▸ after)
  have not2 : i ≠ 2 := fun eq => (by decide : ¬ 3 ≤ 2) (eq ▸ after)
  simp [slots,not0,not1,not2]

theorem shape (program : BodyVCGen.LoadedProgram)
    (size : program.root.body.locals.size = 25)
    (temps : CallMachine.alwaysLiveVarsAndTemps program.root.body = .ok #[6,13,14])
    (target : 1 < program.root.body.basicBlocks.size) :
    PreparedFrameShape (before program) (root program) := by
  refine ⟨rfl,?_,⟨#[6,13,14],temps,?_⟩,rfl,?_,?_,?_⟩
  · change 25 = program.root.body.locals.size
    exact size.symm
  · intro i slot after lookup
    change 3 ≤ i at after
    rw [liveAt lookup]
    have not0 : i ≠ 0 := fun eq => (by decide : ¬ 3 ≤ 0) (eq ▸ after)
    have not1 : i ≠ 1 := fun eq => (by decide : ¬ 3 ≤ 1) (eq ▸ after)
    have not2 : i ≠ 2 := fun eq => (by decide : ¬ 3 ≤ 2) (eq ▸ after)
    simp [slots,not0,not1,not2]
  · exact .localSlot (caller program) 0 RootCompilerFacts.boolLayout boolSlot rfl rfl rfl rfl ⟨_,rfl⟩
  · exact ⟨caller program,rfl,target⟩
  · intro tracker held
    change some borrowTracker = some tracker at held
    have same : tracker = borrowTracker := (Option.some.inj held).symm
    subst tracker
    refine ⟨owner,rfl,?_⟩
    intro key tag member
    have same : (key,tag) = (srcId,heldTag) := by simpa [owner] using member
    cases same
    exact ⟨rfl,entry,lookupSource,rfl⟩

theorem selectedDestination (program : BodyVCGen.LoadedProgram)
    (returnTy : program.root.body.locals[0]? = some RootCompilerFacts.boolLayout.ty)
    (target : 1 < program.root.body.basicBlocks.size) : Destination (before program) (root program) pointer 2 := by
  refine .cachedCaller ⟨#[],caller program,0,1,.Continue,boolSlot,_,rfl,rfl,target,rfl,returnTy,rfl,rfl,rfl,rfl⟩ ⟨owner,rfl,rfl⟩

theorem allocationProfile (program : BodyVCGen.LoadedProgram) :
    AllocationProfile (before program) (root program) preparedTagHeadroom := by
  refine ⟨rfl,by change ([srcId] : List AllocId).Nodup; simp,?_,?_,borrowTracker,owner,rfl,rfl,by decide,by decide,?_,?_,?_⟩
  · intro row member saved known
    change row ∈ #[⟨srcId,4096⟩] at member
    have same : row = ⟨srcId,4096⟩ := by simpa using member
    subst row
    obtain ⟨_,rfl⟩ := onlyAllocation _ saved known
    decide
  · intro key live
    have present := Std.ExtTreeMap.contains_eq_isSome_getElem? (t := machine.memory.live) (a := key)
    change machine.memory.live.contains key = true at live
    rw [live] at present
    cases h : machine.memory.live[key]? with
    | none => simp [h] at present
    | some e =>
      obtain ⟨rfl,_⟩ := onlyAllocation key e h
      exact ⟨_,rfl,rfl,rfl⟩
  · intro row member
    change row ∈ #[(heldTag,.StrongProtector)] at member
    have same : row = (heldTag,.StrongProtector) := by simpa using member
    subst row
    decide
  · intro key tag member
    have same : (key,tag) = (srcId,heldTag) := by simpa [owner] using member
    cases same
    exact ⟨rfl,entry,⟨1⟩,_,lookupSource,rfl,rfl,rfl⟩
  · intro key saved index node lookup nodeAt
    obtain ⟨rfl,rfl⟩ := onlyAllocation key saved lookup
    rcases storedNode index node nodeAt with rfl | rfl <;>
      change some _ = some node at nodeAt <;> cases nodeAt <;> decide

theorem syntaxDomain (program : BodyVCGen.LoadedProgram) :
    PreparedConcreteSlice program (·.addresses) (before program) PreparedReflection.actual.runtime.target.base pointer 2 1 := by
  refine ⟨⟨root program,sliceBuffer,rfl,rfl,rfl,rfl,sliceBuffer_eq,rfl,rfl⟩,rfl,by decide,by decide,?_⟩
  intro _
  exact ⟨storageRegion program,heldTag,4096,rfl,rfl,by change 4096 + 2 < 2^64; decide,rfl,⟨sourceRights program⟩⟩

theorem profile (program : BodyVCGen.LoadedProgram) (span : PreparedContracts.FixedSpanQuery) :
    Profile options 1025 span (before program) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,?_,?_,rfl,rfl,borrowTracker,rfl,rfl⟩
  · with_unfolding_all rfl
  · rw [(CanonicalConfigFacts.actual_fields options () 1026 span).terminators]
    rfl
  · rw [(CanonicalConfigFacts.actual_fields options () 1026 span).terminators]
    rfl

theorem admitted (program : BodyVCGen.LoadedProgram) (span : PreparedContracts.FixedSpanQuery)
    (size : program.root.body.locals.size = 25)
    (temps : CallMachine.alwaysLiveVarsAndTemps program.root.body = .ok #[6,13,14])
    (returnTy : program.root.body.locals[0]? = some RootCompilerFacts.boolLayout.ty)
    (target : 1 < program.root.body.basicBlocks.size) :
    Admitted program options 1025 preparedTagHeadroom span (before program) (root program) pointer 2 1 := by
  refine ⟨profile program span,shape program size temps target,?_,allocationProfile program,
    syntaxDomain program,rfl,?_,fun invalid => (by decide : (2 : UInt64) ≠ 0) invalid |>.elim,
    selectedDestination program returnTy target,rfl,rfl,rfl,?_⟩
  · obtain ⟨thread,equal,relevance⟩ := currentThread program
    refine ⟨rfl,rfl,thread,equal,?_⟩
    intro i saved
    rw [relevance] at saved
    have same := Option.some.inj saved
    subst i
    change 1 < 2
    decide
  · intro _
    exact ⟨storageRegion program,heldTag,4096,sourceRights program,owner,(by with_unfolding_all rfl),rfl,rfl,rfl,by simp [owner,storageRegion],
      rfl,⟨_,rfl,rfl⟩,scope⟩
  · intro slot member mem indirect
    obtain ⟨index, inside, found⟩ := Array.mem_iff_getElem.mp member
    have old := liveAt ((Array.getElem?_eq_getElem inside).trans (congrArg some found))
    rw [old] at indirect
    by_cases zero : index = 0
    · simp [slots,zero] at indirect
    by_cases one : index = 1
    · simp [slots,one] at indirect
    by_cases two : index = 2
    · simp [slots,two] at indirect
    simp only [slots,ite_eq_right zero,ite_eq_right one,ite_eq_right two] at indirect
    split at indirect <;> cases indirect


#print axioms admitted


theorem sourceResource (program : BodyVCGen.LoadedProgram) (id : AllocId) (tag : BorTag)
    (_ : pointer.provenance = some (.concrete id tag)) (saved : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : (before program).machine.memory.live[id]? = some saved) : CopySourceResources saved := by
  obtain ⟨_,rfl⟩ := onlyAllocation id saved present
  exact available

/-- The admitted two-byte concrete call satisfies the generated VC by the
all-count theorem. It enters the accepted copy path with count one. -/
theorem witnessSafety (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (span : PreparedContracts.FixedSpanQuery)
    (size : program.root.body.locals.size = 25)
    (temps : CallMachine.alwaysLiveVarsAndTemps program.root.body = .ok #[6,13,14])
    (returnTy : program.root.body.locals[0]? = some RootCompilerFacts.boolLayout.ty)
    (target : 1 < program.root.body.basicBlocks.size) :
    GeneratedBodySafety.requiredForEveryChoiceAt (PreparedContracts.actualConfig options () 1026 span) limits
      (before program) := by
  have outer : LanguageZeroEntryFacts.rank options.userRelevantCrates < (root program).extra.userRelevance := by
    change LanguageZeroEntryFacts.rank #[] < 255
    rw [RootGuardRelevance.stock.1]
    decide
  have inner : RuntimeZeroEntryFacts.rank options.userRelevantCrates < (root program).extra.userRelevance := by
    change RuntimeZeroEntryFacts.rank #[] < 255
    rw [RootGuardRelevance.stock.2]
    decide
  exact safetyForPreparedCall program loaded options limits 1025 1023 1023 1023 span rfl rfl rfl rfl
    (before program) (root program) pointer 2 1 (admitted program span size temps returnTy target)
    (compilerControl program) outer inner (fun _ => sourceResource program)
    (fun bad _ => ((by decide : (2 : UInt64) ≠ 0) bad).elim)

def Witness (program : BodyVCGen.LoadedProgram) : Prop :=
  ∃ span : PreparedContracts.FixedSpanQuery,
    Admitted program options 1025 preparedTagHeadroom span (before program) (root program) pointer 2 1 ∧
    InitialCompilerControl (before program) (root program) ∧
    CopySourceResources entry ∧
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () 1026 span) limits (before program)

set_option cbv.maxSteps 5000000 in
private theorem stockSpan : CompilerContextSpan.rootSpan PreparedReflection.actual.program =
    .ok PreparedReflection.actual.dummySpan := by
  cbv

/-- The full prepared-call contract and its emitted safety VC are jointly
inhabited by an initialized two-byte input with an accepted count of one. -/
theorem existsSafePreparedCall :
    ∃ program, GeneratedBodySafety.loaded = .ok program ∧ Witness program := by
  have catalog : GeneratedBodySafety.loaded.map (·.root) = .ok RootBody.reflected.body :=
    RootBody.generated_catalog_root
  cases loaded : GeneratedBodySafety.loaded with
  | error error =>
    rw [loaded] at catalog
    cases catalog
  | ok program =>
    let span : PreparedContracts.FixedSpanQuery := ⟨stockSpan⟩
    have rootBody := loadedRoot_eq loaded
    have size : program.root.body.locals.size = 25 := by rw [rootBody]; rfl
    have temps : CallMachine.alwaysLiveVarsAndTemps program.root.body = .ok #[6,13,14] := by
      rw [rootBody]
      cbv
    have returnTy : program.root.body.locals[0]? = some RootCompilerFacts.boolLayout.ty := by rw [rootBody]; rfl
    have target : 1 < program.root.body.basicBlocks.size := by rw [rootBody]; decide
    exact ⟨program,rfl,span,admitted program span size temps returnTy target,
      compilerControl program,available,witnessSafety program loaded span size temps returnTy target⟩

#print axioms existsSafePreparedCall
end DuplicatePrefix.PreparedCallWitness

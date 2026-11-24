import SameAllocationWitnessTree
import VerifyCanonicalPreparedReturn
import duplicate_prefix.RootGuardRelevance
import Miri.Input.InitialMachine

open Miri Miri.ABI Miri.Interpreter Miri.Input Miri.Memory Miri.MIR Miri.TreeBorrows
open Miri.Concurrency Miri.Memory.AllocAddresses Miri.Verification
open DuplicatePrefix

set_option maxHeartbeats 250000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

namespace DuplicatePrefix.SameAllocationPhysicalWitness

abbrev State := MachineHooks.State MiriMemoryKind Machine.RootUser
abbrev srcId := DuplicatePrefix.PreparedCallWitness.srcId
abbrev srcTag := DuplicatePrefix.PreparedCallWitness.srcTag
abbrev addresses := DuplicatePrefix.PreparedCallWitness.addresses
abbrev world := DuplicatePrefix.PreparedCallWitness.world
abbrev limits := DuplicatePrefix.PreparedCallWitness.limits
abbrev options := DuplicatePrefix.PreparedCallWitness.options

open CanonicalCallDomain SourceDomain PreparedArguments
open Miri.DataStructures Miri.TreeBorrows.Tree

open SameAllocationWitness

abbrev heldTag := sliceTag

def borrowTracker : MachineHooks.BorrowState :=
  ⟨{ nextPointerTag := ⟨34, by decide⟩, rootPointerTags := #[(srcId,srcTag)],
     protectedTags := (({} : ProtectedTags).insert heldTag .StrongProtector).insert outputTag .StrongProtector },
    .Default⟩

def owner : FrameState := {protectedTags := #[(srcId,heldTag), (srcId,outputTag)]}
def pointer : Pointer (Option Provenance) := PreparedCallWitness.pointer

def allocation : Allocation Provenance Unit :=
  match e : Allocation.fromBytes (Prov := Provenance) #[11,22,0] Align.ONE .Mut with
  | .ok bytes => bytes
  | .error _ => False.elim (by
      have impossible : (Allocation.fromBytes (Prov := Provenance) #[11,22,0] Align.ONE .Mut).isOk = true := by decide
      rw [e] at impossible
      cases impossible)

def entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
  ⟨.stack, allocation.withExtra tree⟩

def destination : MPlaceTy Provenance :=
  ⟨⟨Pointer.new (some (.concrete srcId srcTag)) (Size.ofBytes 4098), .none, none⟩,
    RootCompilerFacts.boolLayout⟩

abbrev ActualFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra
abbrev Slot := LocalState Provenance LocalLayout

abbrev sliceBuffer := PreparedCallWitness.sliceBuffer

theorem sliceBuffer_eq : Immediate.newSlice pointer 2 PreparedReflection.actual.runtime.target.base = .ok sliceBuffer :=
  PreparedCallWitness.sliceBuffer_eq

def slots (count : UInt64) (index : Nat) : Slot :=
  if index = 0 then ⟨.live (.immediate .uninit),none⟩
  else if index = 1 then ⟨.live (.immediate sliceBuffer),some RootCompilerFacts.sliceLayout⟩
  else if index = 2 then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  else ⟨(if #[6,13,14].contains index then .live (.immediate .uninit) else .dead),none⟩

def root (program : BodyVCGen.LoadedProgram) (count : UInt64) : ActualFrame :=
  let frame : ActualFrame := Frame.create program.root program.rootInstance
    {userRelevance := 255, borrowTracker := some owner, catchUnwind := none, dataRace := none}
    (.stop true) (.memory destination) PreparedReflection.actual.dummySpan (.ofAllocationToken 1)
  {frame with location := .mir ⟨0,0⟩, locals := Array.ofFn (fun index : Fin 25 => slots count index.val)}

def machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser :=
  let mem : MemoryState Provenance BorrowTree MiriMemoryKind := MemoryState.empty.setIssuedIds #[srcId]
  let threads := ThreadManager.initial true
  let rows := threads.threads.set 0
    { ThreadRecord.initial none none with originSpanToken := PreparedReflection.actual.dummySpan.id, topUserRelevantFrame := some 0 }
  { memory := {mem with live := mem.live.insert srcId entry, nextAllocId := 2}
    borrowTracker := some borrowTracker, dataRace := none
    threads := {threads with threads := rows}
    raceAllocations := {}, allocationSpans := #[]
    user := ⟨addresses,
      ⟨⟨⟨ThreadId.MAIN_THREAD,#[]⟩,⟨2⟩,world⟩,.Shallow,.Int,false,#[]⟩,#[]⟩ }

def before (program : BodyVCGen.LoadedProgram) (count : UInt64) : State :=
  Storage.withCurrent #[] (root program count) machine

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

def storageRegion (program : BodyVCGen.LoadedProgram) (count : UInt64) : InitializedRegion (before program count) 2 :=
  ⟨srcId, Size.ZERO, entry, lookupSource, rfl, rfl, by decide, fun _ => rfl⟩

theorem available : CopySourceResources entry := {
  keys := availableKeys
  room := by decide
  maskLength := rfl
  mask := True.intro
  provenance := by
    change ProvenanceCopy.WellFormed (ProvenanceMap.new (Prov := Provenance)) 3
    constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]
  storageBound := by decide }

def sourceRights (program : BodyVCGen.LoadedProgram) (count : UInt64) :
    ExclusiveRegion (before program count) 2 (storageRegion program count) heldTag := by
  refine ⟨borrowTracker,rfl,coherent,sliceIndex,rfl,⟨child heldTag,rfl,rfl⟩,?_,?_⟩
  · intro distance smaller
    refine ⟨sourceRow, ?_, ?_, ?_⟩
    · change sourceRow ∈ #[sourceRow,outputRow]
      simp
    · change 0 ≤ 0+distance
      omega
    · change 0+distance < 2
      change distance < 2 at smaller
      omega
  · intro distance smaller row member lower upper index node found
    rcases rowCases member with rfl | rfl
    · exact sourcePermission found borrowTracker.global.protectedTags
    · change 2 ≤ 0+distance at lower
      change distance < 2 at smaller
      omega

private theorem currentThread (program : BodyVCGen.LoadedProgram) (count : UInt64) :
    ∃ thread, (before program count).machine.threads.activeThread? = some thread ∧
      thread.topUserRelevantFrame = some 0 := ⟨_,rfl,rfl⟩

private theorem liveAt {program : BodyVCGen.LoadedProgram} {count : UInt64} {index : Nat} {slot : Slot}
    (lookup : (root program count).locals[index]? = some slot) : slot = slots count index := by
  obtain ⟨inside, found⟩ := Array.getElem?_eq_some_iff.mp lookup
  rw [show (root program count).locals[index] = slots count index by simp [root]] at found
  exact found.symm

theorem compilerControl (program : BodyVCGen.LoadedProgram) (count : UInt64) :
    InitialCompilerControl (before program count) (root program count) := by
  refine ⟨rfl,rfl,currentThread program count,?_⟩
  intro i slot after lookup
  rw [liveAt lookup]
  have not0 : i ≠ 0 := fun eq => (by decide : ¬ 3 ≤ 0) (eq ▸ after)
  have not1 : i ≠ 1 := fun eq => (by decide : ¬ 3 ≤ 1) (eq ▸ after)
  have not2 : i ≠ 2 := fun eq => (by decide : ¬ 3 ≤ 2) (eq ▸ after)
  simp [slots,not0,not1,not2]

theorem shape (program : BodyVCGen.LoadedProgram) (count : UInt64)
    (size : program.root.body.locals.size = 25)
    (temps : CallMachine.alwaysLiveVarsAndTemps program.root.body = .ok #[6,13,14]) :
    PreparedFrameShape (before program count) (root program count) := by
  refine ⟨rfl,?_,⟨#[6,13,14],temps,?_⟩,rfl,?_,?_,?_⟩
  · have countLocals : (root program count).locals.size = 25 := by simp [root]
    have rootBody : (root program count).body = program.root.body := rfl
    rw [countLocals,rootBody,size]
  · intro i slot after lookup
    change 3 ≤ i at after
    rw [liveAt lookup]
    have not0 : i ≠ 0 := fun eq => (by decide : ¬ 3 ≤ 0) (eq ▸ after)
    have not1 : i ≠ 1 := fun eq => (by decide : ¬ 3 ≤ 1) (eq ▸ after)
    have not2 : i ≠ 2 := fun eq => (by decide : ¬ 3 ≤ 2) (eq ▸ after)
    simp [slots,not0,not1,not2]
  · have ready : ReturnDestinationShape (before program count) (.memory destination) :=
      .memorySlot destination srcId srcTag entry rfl rfl lookupSource rfl rfl
    exact ready
  · rfl
  · intro tracker held
    change some borrowTracker = some tracker at held
    have same : tracker = borrowTracker := (Option.some.inj held).symm
    subst tracker
    refine ⟨owner,rfl,?_⟩
    intro key tag member
    change (key,tag) ∈ #[(srcId,heldTag),(srcId,outputTag)] at member
    have parts : (key,tag) = (srcId,heldTag) ∨ (key,tag) = (srcId,outputTag) := by simpa using member
    rcases parts with same | same <;> cases same <;> exact ⟨rfl,entry,lookupSource,rfl⟩

theorem allocationProfile (program : BodyVCGen.LoadedProgram) (count : UInt64) :
    AllocationProfile (before program count) (root program count) preparedTagHeadroom := by
  refine ⟨rfl,by change ([srcId] : List AllocId).Nodup; simp,?_,?_,borrowTracker,owner,rfl,rfl,?_,by decide,?_,?_,?_⟩
  rotate_left 2
  · change ([heldTag,outputTag] : List BorTag).Nodup
    simp [(by decide : heldTag ≠ outputTag)]
  rotate_right 2
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
    change row ∈ #[(heldTag,.StrongProtector),(outputTag,.StrongProtector)] at member
    have cases : row = (heldTag,.StrongProtector) ∨ row = (outputTag,.StrongProtector) := by simpa using member
    rcases cases with rfl | rfl <;> decide
  · intro key tag member
    change (key,tag) ∈ #[(srcId,heldTag),(srcId,outputTag)] at member
    have parts : (key,tag) = (srcId,heldTag) ∨ (key,tag) = (srcId,outputTag) := by simpa using member
    rcases parts with same | same
    · cases same
      exact ⟨rfl,entry,sliceIndex,_,lookupSource,rfl,rfl,rfl⟩
    · cases same
      exact ⟨rfl,entry,outputIndex,_,lookupSource,rfl,rfl,rfl⟩
  · intro key saved index node lookup nodeAt
    obtain ⟨rfl,rfl⟩ := onlyAllocation key saved lookup
    rcases SameAllocationWitness.lookupCases nodeAt with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

theorem syntaxDomain (program : BodyVCGen.LoadedProgram) (count : UInt64) :
    PreparedConcreteSlice program (·.addresses) (before program count) PreparedReflection.actual.runtime.target.base pointer 2 count := by
  refine ⟨?_, rfl, by decide, by decide, ?_⟩
  · refine ⟨⟨root program count, sliceBuffer, rfl, rfl, rfl, rfl, sliceBuffer_eq, ?_, ?_⟩⟩
    · simp [root, slots]
    · simp [root, slots]
  · intro _
    refine ⟨storageRegion program count, heldTag, 4096, rfl, rfl, ?_, rfl, ?_⟩
    · change 4096 + 3 < 2 ^ 64
      decide
    · exact ⟨sourceRights program count⟩

theorem profile (program : BodyVCGen.LoadedProgram) (count : UInt64) (span : PreparedContracts.FixedSpanQuery) :
    Profile options 1025 span (before program count) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,?_,?_,rfl,rfl,borrowTracker,rfl,rfl⟩
  · with_unfolding_all rfl
  · rw [(CanonicalConfigFacts.actual_fields options () 1026 span).terminators]
    rfl
  · rw [(CanonicalConfigFacts.actual_fields options () 1026 span).terminators]
    rfl


theorem currentWriteGrant : ByteWriteGrant tree 2 outputIndex borrowTracker.global.protectedTags := by
  intro row member lower upper index node found
  rcases rowCases member with rfl | rfl
  · exact False.elim ((by decide : ¬ (2 : UInt64) < 2) upper)
  · exact outputPermission found borrowTracker.global.protectedTags

private theorem rootAncestor {index target : UniIndex} (path : Ancestor tree index target)
    (atRoot : target = rootIndex) : index = rootIndex := by
  induction path with
  | self _ => exact atRoot
  | @parent _ index parent path node found edge ih =>
    have equal := ih atRoot
    subst index
    change some rootNode = some node at found
    cases found
    cases edge

theorem savedWriteGrant : ByteWriteGrant tree 2 rootIndex
    (borrowTracker.global.endCall owner).protectedTags := by
  intro row member lower upper index node found
  rcases rowCases member with rfl | rfl
  · exact False.elim ((by decide : ¬ (2 : UInt64) < 2) upper)
  · rcases SameAllocationWitness.lookupCases found with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨parentPermission,rfl,fun _ => ⟨rfl,trivial⟩,
        fun absent => (absent (.self _)).elim⟩
    · exact ⟨dormantSlicePermission, rfl,
        fun path => (by decide : sliceIndex ≠ rootIndex) (rootAncestor path rfl) |>.elim,
        fun _ => ⟨rfl, Or.inl rfl⟩⟩
    · exact ⟨childPermission,rfl,fun _ => ⟨rfl,trivial⟩,fun _ => ⟨rfl,Or.inl rfl⟩⟩

theorem physicalDestination (program : BodyVCGen.LoadedProgram) (count : UInt64) :
    PhysicalBoolDestination (before program count) (root program count) pointer 2 true := by
  refine ⟨destination, srcId, entry, Size.ofBytes 2, srcTag, 4096,
    borrowTracker, owner, rootIndex, outputTag, outputIndex,
    rfl,rfl,rfl,lookupSource,rfl,rfl,available.mask,available.maskLength,available.provenance,
    by decide,rfl,by decide,rfl,by decide,rfl,rfl,rfl,rfl,rfl,coherent,rfl,⟨rootNode,rfl,rfl⟩,
    rfl,⟨child outputTag,rfl,rfl,rfl,rfl⟩,outputRelease,currentWriteGrant,?_,?_⟩
  · exact ⟨outputRow,by change outputRow ∈ #[sourceRow,outputRow]; simp,by decide,by decide,fun _ _ found =>
      savedWriteGrant outputRow (by change outputRow ∈ #[sourceRow,outputRow]; simp) (by decide) (by decide) _ _ found⟩
  · intro _ sourceId tag concrete
    have equal : (.concrete srcId heldTag : Provenance) = .concrete sourceId tag :=
      Option.some.inj concrete
    have sameTag := (Provenance.concrete.inj equal).2
    subst tag
    refine Or.inr ⟨Or.inr (by decide), ?_⟩
    intro holder selected path
    change some sliceIndex = some holder at selected
    have current := (Option.some.inj selected).symm
    subst holder
    rcases leafAncestor (tag := heldTag) rfl path with other | other
    · exact (by decide : outputIndex ≠ sliceIndex) other
    · exact (by decide : outputIndex ≠ rootIndex) other

theorem admitted (program : BodyVCGen.LoadedProgram) (count : UInt64)
    (span : PreparedContracts.FixedSpanQuery)
    (size : program.root.body.locals.size = 25)
    (temps : CallMachine.alwaysLiveVarsAndTemps program.root.body = .ok #[6,13,14]) :
    Admitted program options 1025 preparedTagHeadroom span (before program count) (root program count) pointer 2 count true := by
  refine ⟨profile program count span,shape program count size temps,?_,allocationProfile program count,
    syntaxDomain program count,rfl,?_,fun invalid => (by decide : (2 : UInt64) ≠ 0) invalid |>.elim,
    .physicalRoot rfl rfl (physicalDestination program count), ?_, ?_, ?_, ?_⟩
  · obtain ⟨thread,equal,relevance⟩ := currentThread program count
    refine ⟨rfl,rfl,thread,equal,?_⟩
    intro i saved
    rw [relevance] at saved
    have same := Option.some.inj saved
    subst i
    change 0 < 1
    decide
  · intro _
    refine ⟨storageRegion program count, heldTag, 4096, sourceRights program count, owner,
      rfl, rfl, rfl, rfl, ?_, rfl, ⟨child heldTag, rfl, rfl⟩, sliceRelease⟩
    change (srcId, heldTag) ∈ #[(srcId, heldTag), (srcId, outputTag)]
    simp
  · simp [root, slots]
  · simp [root, slots]
  · simp [root, slots]
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

theorem sourceResource (_program : BodyVCGen.LoadedProgram) (_count : UInt64) (id : AllocId) (tag : BorTag)
    (_ : pointer.provenance = some (.concrete id tag)) (saved : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : machine.memory.live[id]? = some saved) : CopySourceResources saved := by
  obtain ⟨_,rfl⟩ := onlyAllocation id saved present
  exact available

theorem witnessSafety
    (program : BodyVCGen.LoadedProgram) (loaded : GeneratedBodySafety.loaded = .ok program)
    (count : UInt64) (span : PreparedContracts.FixedSpanQuery)
    (size : program.root.body.locals.size = 25)
    (temps : CallMachine.alwaysLiveVarsAndTemps program.root.body = .ok #[6, 13, 14]) :
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () 1026 span) limits (before program count) := by
  have outer : LanguageZeroEntryFacts.rank options.userRelevantCrates < (root program count).extra.userRelevance := by
    change LanguageZeroEntryFacts.rank #[] < 255
    rw [RootGuardRelevance.stock.1]
    decide
  have inner : RuntimeZeroEntryFacts.rank options.userRelevantCrates < (root program count).extra.userRelevance := by
    change RuntimeZeroEntryFacts.rank #[] < 255
    rw [RootGuardRelevance.stock.2]
    decide
  exact safetyForPreparedReturn program loaded options limits 1025 1023 1023 1023 span rfl rfl rfl rfl
    (before program count) (root program count) pointer 2 count
    (.physical (admitted program count span size temps) (by decide) rfl rfl
      (physicalDestination program count) ⟨srcId, heldTag, destination, srcTag, rfl, rfl, rfl⟩)
    (compilerControl program count) outer inner (fun _ => sourceResource program count)
    (fun impossible _ => ((by decide : (2 : UInt64) ≠ 0) impossible).elim)

#print axioms admitted
#print axioms physicalDestination
#print axioms currentWriteGrant
#print axioms savedWriteGrant
#print axioms allocationProfile
#print axioms syntaxDomain
def Witness (program : BodyVCGen.LoadedProgram) : Prop :=
  ∃ span : PreparedContracts.FixedSpanQuery, ∀ count : UInt64,
    Admitted program options 1025 preparedTagHeadroom span (before program count)
      (root program count) pointer 2 count true ∧
    InitialCompilerControl (before program count) (root program count) ∧
    CopySourceResources entry ∧
    pointer.provenance = some (.concrete srcId heldTag) ∧
    destination.mplace.ptr.provenance = some (.concrete srcId srcTag) ∧
    DisjointResultByte destination.mplace.ptr.offset.bytes.toNat pointer.offset.bytes.toNat 2 ∧
    outputRow.data.perms.get sliceIndex = some dormantSlicePermission ∧
    GeneratedBodySafety.requiredForEveryChoiceAt
      (PreparedContracts.actualConfig options () 1026 span) limits (before program count)

set_option cbv.maxSteps 5000000 in
private theorem stockSpan : CompilerContextSpan.rootSpan PreparedReflection.actual.program =
    .ok PreparedReflection.actual.dummySpan := by
  cbv

/-- The same three-byte allocation satisfies the prepared-call contract and
its exact generated safety condition for every count. The argument occupies
the first two bytes and the saved return byte is the third. Each has its own
call-owned child protector. -/
theorem existsSafePreparedCall : ∃ program, GeneratedBodySafety.loaded = .ok program ∧ Witness program := by
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
    refine ⟨program,rfl,span,fun count => ?_⟩
    exact ⟨admitted program count span size temps, compilerControl program count,
      available, rfl, rfl, Or.inr (by decide), rfl, witnessSafety program loaded count span size temps⟩

#print axioms existsSafePreparedCall
end DuplicatePrefix.SameAllocationPhysicalWitness

import SourceDomain
import Miri.Verification.RangeModifyLaw
import duplicate_prefix.InitMaskCopy
import duplicate_prefix.ProvenanceCopy
import duplicate_prefix.PreparedContracts
import duplicate_prefix.RootCompilerFacts

/-! Initial-state facts for an admitted prepared call in the current source
profile. The domain does not constrain the count or assume an execution
prefix, an access result, or a successful return. -/
namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR
open Miri.TreeBorrows Miri.Verification
open DuplicatePrefix.PreparedArguments DuplicatePrefix.SourceDomain

local notation "State" => MachineHooks.State MiriMemoryKind Machine.RootUser
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- The current compiler-derived configuration with one typed core choice.
The concrete machine state still carries its environmental input tape. -/
structure Profile (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : State) : Prop where
  debugOff : options.place.debugAssertions = false
  shallow : before.machine.user.payload.validation = .Shallow
  ghostOff : before.machine.user.payload.ghost = false
  raceOff : before.machine.dataRace = none
  backendOff : before.machine.user.payload.payload.user.backend = .none
  compilerRuntime : (EvalProjectionMachine.arrays.get before).metadata = PreparedReflection.actual.runtime
  noSyntheticSliceCache : (EvalProjectionMachine.arrays.get before).entries.any (·.value.ty == 2) = false
  fixed : before.machine.threads.fixedScheduling = true
  noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
    before.machine.user).gcInterval = 0
  unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
    before.machine.user).checkedArithmetic = false
  implicitWritesOff : options.retag.implicitWrites = false
  preciseInteriorMutOff : options.retag.preciseInteriorMut = false
  mode : ∃ tracker, before.machine.borrowTracker = some tracker ∧ tracker.retagMode = .Default

/-- Before the function executes, its single-thread relevance cache agrees
with the live stack. The callee carries no local race state or varargs. -/
structure StackProfile (before : State) (frame : Frame) : Prop where
  calleeClocksOff : frame.extra.dataRace = none
  noVarargs : frame.vaList = #[]
  active : ∃ thread, before.machine.threads.activeThread? = some thread ∧
    ∀ index, thread.topUserRelevantFrame = some index → index < before.stack.frames.size

/-- A concrete prepared argument contributes a protector even when its
slice is empty. An empty integer-address argument contributes no ledger row. -/
def argumentLedger (pointer : Pointer (Option Provenance)) : Array (AllocId × BorTag) :=
  match pointer.provenance with
  | some (.concrete id tag) => #[(id, tag)]
  | _ => #[]

/-- Initial range-map shape of a call-owned tag. A nonempty release may
visit bytes and uses the single-root access proof. A dormant zero-length
tag can be released in any coherent forest. -/
structure ReleaseRange (tree : BorrowTree) (holder : UniIndex) (start : Size)
    (length : UInt64) : Prop where
  root : length ≠ 0 → ∃ onlyRoot, tree.roots = #[onlyRoot]
  extent : start.bytes.toNat + length.toNat ≤ tree.locations.size.bytes.toNat
  materialized : ∀ segment ∈ tree.locations.entries,
    (segment.data.perms.get holder).isSome = true →
      start.bytes.toNat ≤ segment.range.start.toNat ∧
      segment.range.stop.toNat ≤ start.bytes.toNat + length.toNat
  vacant : ∀ index, tree.nodeAt index = none → ∀ segment ∈ tree.locations.entries,
    segment.data.perms.get index = none

theorem ReleaseRange.materializedWithin {tree holder start length}
    (ready : ReleaseRange tree holder start length) :
    RangeModifyLaw.EachByte tree.locations fun point row =>
      ∀ state, row.perms.get holder = some state →
        start.bytes.toNat ≤ point.toNat ∧ point.toNat < (start.bytes + length).toNat := by
  intro point position inside lower upper state found
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  obtain ⟨starts, stops⟩ := ready.materialized segment member (by simp [segment, found])
  have lowerNat := UInt64.le_iff_toNat_le.mp lower
  have upperNat := UInt64.lt_iff_toNat_lt.mp upper
  have fits : start.bytes.toNat + length.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt ready.extent tree.locations.size.bytes.toNat_lt
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  exact ⟨Nat.le_trans starts lowerNat, Nat.lt_of_lt_of_le upperNat stops⟩

theorem ReleaseRange.vacantAt {tree holder start length} (ready : ReleaseRange tree holder start length)
    {index : UniIndex} (absent : tree.nodeAt index = none)
    {position : Nat} (inside : position < tree.locations.entries.size) :
    tree.locations.entries[position].data.perms.get index = none :=
  ready.vacant index absent _ (Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩)

theorem ReleaseRange.noEmptyMaterialization {tree holder start}
    (ready : ReleaseRange tree holder start 0) (formed : tree.locations.WellFormed)
    {position : Nat} (inside : position < tree.locations.entries.size) :
    tree.locations.entries[position].data.perms.get holder = none := by
  have nonempty : tree.locations.entries.size ≠ 0 := by omega
  simp only [DedupRangeMap.WellFormed, nonempty, ↓reduceDIte] at formed
  let segment := tree.locations.entries[position]
  have member : segment ∈ tree.locations.entries := Array.mem_iff_getElem.mpr ⟨position, inside, rfl⟩
  cases found : segment.data.perms.get holder with
  | none => rfl
  | some _ =>
    obtain ⟨lower, upper⟩ := ready.materialized segment member (by simp [found])
    have span := UInt64.lt_iff_toNat_lt.mp (formed.2.1 position inside)
    change segment.range.start.toNat < segment.range.stop.toNat at span
    simp only [UInt64.toNat_zero, Nat.add_zero] at upper
    omega

/-- The selected tag can write this byte while the given protection set is
still installed. Only location rows that cover this byte are relevant. -/
def ByteWriteGrant (tree : BorrowTree) (point : UInt64) (source : UniIndex)
    (protections : ProtectedTags) : Prop :=
  ∀ segment ∈ tree.locations.entries, segment.range.start ≤ point → point < segment.range.stop →
    ∀ index node, tree.nodeAt index = some node →
      ∃ current, tree.locationStateAt segment.data index = some current ∧
        (Ancestor tree index source → localOwns current (protections.contains node.tag)) ∧
        (¬ Ancestor tree index source → foreignCompatible current (protections.contains node.tag))

/-- Before execution, a physical Boolean return destination resolves to one
in-bounds byte of live mutable storage. The byte may be uninitialized. Its
grant is separate from the slice's grant. The call-owned return protector
has a grant with all current protections installed for its release
traversal. The saved return pointer's tag has an independent grant with
the protections retained after ending this frame. -/
structure PhysicalBoolDestination (before : State) (frame : Frame)
    (pointer : Pointer (Option Provenance)) (length : UInt64) : Prop where
  storage : ∃ (place : MPlaceTy Provenance) (id : AllocId)
    (slot : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (relative : Size) (tag : BorTag) (base : UInt64)
    (tracker : MachineHooks.BorrowState) (owned : FrameState) (source : UniIndex)
    (returnTag : BorTag) (returnIndex : UniIndex),
      frame.returnPlace = .memory place ∧
      place.layout = RootCompilerFacts.boolLayout ∧
      place.mplace.misaligned = none ∧
      before.machine.memory.live[id]? = some slot ∧
      slot.allocation.mutability = .Mut ∧
      slot.allocation.len = slot.allocation.byteSize.bytes.toNat ∧
      DuplicatePrefix.InitMaskCopy.WellFormed slot.allocation.initializationMask ∧
      slot.allocation.initializationMask.len = slot.allocation.byteSize ∧
      DuplicatePrefix.ProvenanceCopy.WellFormed slot.allocation.provenanceMap slot.allocation.len ∧
      relative.bytes < slot.allocation.byteSize.bytes ∧
      place.mplace.ptr.provenance = some (.concrete id tag) ∧
      place.mplace.ptr.offset.bytes ≠ 0 ∧
      place.mplace.ptr.offset.bytes.toNat = base.toNat + relative.bytes.toNat ∧
      base.toNat + slot.allocation.byteSize.bytes.toNat < 2 ^ 64 ∧
      (before.machine.user.addresses.baseAddr.find? (·.allocId == id)) = some ⟨id, base⟩ ∧
      before.machine.borrowTracker = some tracker ∧
      frame.extra.borrowTracker = some owned ∧
      owned.protectedTags = (argumentLedger pointer).push (id, returnTag) ∧
      tracker.global.protectedTags.get returnTag = some .StrongProtector ∧
      CoherentForest slot.allocation.extra ∧
      slot.allocation.extra.indexOfTag tag = some source ∧
      (∃ node, slot.allocation.extra.nodeAt source = some node ∧ node.tag = tag) ∧
      slot.allocation.extra.indexOfTag returnTag = some returnIndex ∧
      (∃ node, slot.allocation.extra.nodeAt returnIndex = some node ∧ node.tag = returnTag ∧
        node.parent = some source ∧ node.isExposed = false) ∧
      ReleaseRange slot.allocation.extra returnIndex relative 1 ∧
      ByteWriteGrant slot.allocation.extra relative.bytes returnIndex tracker.global.protectedTags ∧
      (∃ segment ∈ slot.allocation.extra.locations.entries,
        segment.range.start ≤ relative.bytes ∧ relative.bytes < segment.range.stop ∧
        ∀ index node, slot.allocation.extra.nodeAt index = some node →
          ∃ current, slot.allocation.extra.locationStateAt segment.data index = some current ∧
            (Ancestor slot.allocation.extra index source →
              localOwns current ((tracker.global.endCall owned).protectedTags.contains node.tag)) ∧
            (¬ Ancestor slot.allocation.extra index source →
              foreignCompatible current ((tracker.global.endCall owned).protectedTags.contains node.tag))) ∧
      (length ≠ 0 → ∀ sourceId srcTag,
        pointer.provenance = some (.concrete sourceId srcTag) → sourceId ≠ id)

/-- The cached Boolean slot belongs to the suspended caller at its actual
stack index. The continuation identifies an existing basic block. -/
structure CachedBoolDestination (before : State) (frame : Frame) : Prop where
  localSlot : ∃ (older : Array Frame) (caller : Frame) (index : MIR.LocalId)
    (target : BasicBlockId) (unwind : UnwindAction) (slot : LocalState Provenance LocalLayout)
    (value : Immediate Provenance),
      before.stack.frames = (older.push caller).push frame ∧
      frame.returnContinuation = .goto (some target) unwind ∧ target < caller.body.basicBlocks.size ∧
      frame.returnPlace =
        .frameLocal older.size index none RootCompilerFacts.boolLayout caller.localsIdentity ∧
      caller.body.locals[index]? = some RootCompilerFacts.boolLayout.ty ∧
      caller.locals[index]? = some slot ∧
      slot.layout = some RootCompilerFacts.boolLayout ∧ slot.value = .live (.immediate value) ∧
      caller.extra.dataRace = none

/-- These are the two return carriers supported by this prepared-call
profile. The root form has no suspended caller. -/
inductive Destination (before : State) (frame : Frame)
    (pointer : Pointer (Option Provenance)) (length : UInt64) : Prop where
  | physicalRoot (stack : before.stack.frames = #[frame])
      (continuation : frame.returnContinuation = .stop true)
      (destination : PhysicalBoolDestination before frame pointer length)
  | cachedCaller (destination : CachedBoolDestination before frame)
      (ledger : ∃ owned, frame.extra.borrowTracker = some owned ∧
        owned.protectedTags = argumentLedger pointer)

/-- Initial bookkeeping for allocation identity, protector ownership, and tag
freshness. The headroom parameters describe resource availability without
predicting a provider outcome or an allocation result. A successful trace
proof must separately show that its chosen headroom suffices. -/
structure AllocationProfile (before : State) (frame : Frame) (tagHeadroom : Nat) : Prop where
  managed : before.machine.user.addresses.addressMode = .managed
  uniqueAddresses : (before.machine.user.addresses.baseAddr.toList.map (·.allocId)).Nodup
  regionAddresses : ∀ row ∈ before.machine.user.addresses.baseAddr,
    ∀ entry, before.machine.memory.live[row.allocId]? = some entry →
      row.address.toNat + entry.allocation.byteSize.bytes.toNat < 2 ^ 64
  extras : ∀ id, before.machine.memory.live.contains id = true →
    ∃ extra, (before.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (·.1 == id)) = some (id, extra) ∧ extra.weakMemory = none ∧ extra.sync = #[]
  ledger : ∃ tracker owned,
    before.machine.borrowTracker = some tracker ∧ frame.extra.borrowTracker = some owned ∧
    (owned.protectedTags.toList.map Prod.snd).Nodup ∧
    tracker.global.nextPointerTag.value.toNat + tagHeadroom < 2 ^ 64 ∧
    (∀ tagEntry ∈ tracker.global.protectedTags.entries,
      tagEntry.1.value < tracker.global.nextPointerTag.value) ∧
    (∀ id tag, (id, tag) ∈ owned.protectedTags →
      tracker.global.protectedTags.contains tag = true ∧
        ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (source : UniIndex) (node : TreeNode),
          before.machine.memory.live[id]? = some entry ∧
          entry.allocation.extra.indexOfTag tag = some source ∧
          entry.allocation.extra.nodeAt source = some node ∧ node.tag = tag) ∧
    (∀ (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (index : UniIndex) (node : TreeNode), before.machine.memory.live[id]? = some entry →
      entry.allocation.extra.nodeAt index = some node →
      node.tag.value < tracker.global.nextPointerTag.value)

/-- This domain describes the prepared imported frame, slice permission,
runtime profile and saved destination. It is independent of the generated
safety VC and quantifies over the full `UInt64` count space. -/
structure Admitted
    (program : BodyVCGen.LoadedProgram)
    (options : EvalConfigurationCore.Options) (remaining tagHeadroom : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : State)
    (frame : Frame) (pointer : Pointer (Option Provenance)) (length count : UInt64) : Prop where
  profile : Profile options remaining span before
  shape : PreparedFrameShape before frame
  stack : StackProfile before frame
  allocations : AllocationProfile before frame tagHeadroom
  slice : PreparedConcreteSlice program (·.addresses) before
    PreparedReflection.actual.runtime.target.base pointer length count
  identity : frame.functionInstance = program.rootInstance
  sliceProtector : length ≠ 0 →
    ∃ (storage : InitializedRegion before length) (tag : BorTag) (base : UInt64)
      (region : ExclusiveRegion before length storage tag) (owned : FrameState),
      pointer.provenance = some (.concrete storage.id tag) ∧
      pointer.offset.bytes.toNat = base.toNat + storage.relativeStart.bytes.toNat ∧
      (before.machine.user.addresses.baseAddr.find? (·.allocId == storage.id)) = some ⟨storage.id, base⟩ ∧
      frame.extra.borrowTracker = some owned ∧
      (storage.id, tag) ∈ owned.protectedTags ∧
      region.tracker.global.protectedTags.get tag = some .StrongProtector ∧
      (∃ node, storage.entry.allocation.extra.nodeAt region.source = some node ∧ node.isExposed = false) ∧
      ReleaseRange storage.entry.allocation.extra region.source storage.relativeStart length
  emptyProtector : length = 0 →
    match pointer.provenance with
    | some (.concrete id tag) =>
      ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
        (holder : UniIndex) (node : TreeNode) (tracker : MachineHooks.BorrowState)
        (base : UInt64) (start : Size),
        before.machine.memory.live[id]? = some entry ∧
        before.machine.borrowTracker = some tracker ∧
        tracker.global.protectedTags.get tag = some .StrongProtector ∧
        entry.allocation.extra.indexOfTag tag = some holder ∧
        entry.allocation.extra.nodeAt holder = some node ∧ node.isExposed = false ∧
        CoherentForest entry.allocation.extra ∧
        (before.machine.user.addresses.baseAddr.find? (·.allocId == id)) = some ⟨id, base⟩ ∧
        pointer.offset.bytes.toNat = base.toNat + start.bytes.toNat ∧
        ReleaseRange entry.allocation.extra holder start 0
    | _ => True
  destination : Destination before frame pointer length
  argLayout : (frame.locals[1]?.bind (·.layout)) = some RootCompilerFacts.sliceLayout
  countLayout : (frame.locals[2]?.bind (·.layout)) = some RootCompilerFacts.usizeLayout
  resultSlot : frame.locals[0]? = some ⟨.live (.immediate .uninit), none⟩
  immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory)

theorem Admitted.entered {program options remaining tagHeadroom span before frame pointer length count}
    (admitted : Admitted program options remaining tagHeadroom span before frame pointer length count) :
    WholeBodyWP.entryMatchesLoaded program.root before :=
  admitted.slice.entered

/-- The frame named in the domain is the same frame that supplies the
emitted program's arguments and entry position. -/
theorem Admitted.boundArguments {program options remaining tagHeadroom span before frame pointer length count}
    (admitted : Admitted program options remaining tagHeadroom span before frame pointer length count) :
    ∃ buffer, frame.bodyIdentity = program.root.identity ∧
      frame.body = program.root.body ∧ frame.location = .mir ⟨0, 0⟩ ∧
      Immediate.newSlice pointer length PreparedReflection.actual.runtime.target.base = .ok buffer ∧
      (frame.locals[1]?.map (·.value)) = some (.live (.immediate buffer)) ∧
      (frame.locals[2]?.map (·.value)) =
        some (.live (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 count))))) := by
  obtain ⟨current, buffer, active, rest⟩ := admitted.slice.arguments.bound
  have same : current = frame := Option.some.inj (active.symm.trans admitted.shape.current)
  subst current
  exact ⟨buffer, rest⟩

/-- Stack depth is determined by the actual return carrier. -/
theorem Destination.callDepth {before frame pointer length}
    (destination : Destination before frame pointer length) :
    before.stack.frames.size = 1 ∨ 2 ≤ before.stack.frames.size := by
  cases destination with
  | physicalRoot stack _ _ => simp [stack]
  | cachedCaller target _ =>
    obtain ⟨older, caller, index, target, unwind, slot, value, stack, _⟩ := target.localSlot
    simp only [stack, Array.size_push]
    omega

/-- The prepared entry reserves capacity for the two length-side reborrows
and two positive-copy-side reborrows. Root preparation uses separate capacity
for the argument and physical return-place protectors. -/
def preparedTagHeadroom : Nat := 4

/-- Target for an all-count proof under the fixed profile and its runtime
limits. All typed choices are admitted and the condition starts at the
prepared entry, after root preparation has used its own tag capacity. -/
def SafetyGoal (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) : Prop :=
  ∀ program, GeneratedBodySafety.loaded = .ok program →
    ∀ (before : State) (frame : Frame) (pointer : Pointer (Option Provenance)) (length count : UInt64),
      Admitted program options remaining preparedTagHeadroom span before frame pointer length count →
      GeneratedBodySafety.requiredForEveryChoiceAt
        (PreparedContracts.actualConfig options () (remaining + 1) span) limits before

#print axioms Admitted.entered
#print axioms Admitted.boundArguments
#print axioms Destination.callDepth
#print axioms ReleaseRange.materializedWithin
#print axioms ReleaseRange.vacantAt
#print axioms ReleaseRange.noEmptyMaterialization

end DuplicatePrefix.CanonicalCallDomain

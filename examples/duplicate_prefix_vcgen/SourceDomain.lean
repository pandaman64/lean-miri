import PreparedArguments

namespace DuplicatePrefix.SourceDomain

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.MIR
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Verification
open DuplicatePrefix.PreparedArguments

variable {K U : Type}
local notation "State" => MachineHooks.State K U

/-- Source lineage is read from the allocation's parent edges. -/
inductive Ancestor (tree : BorrowTree) : UniIndex → UniIndex → Prop where
  | self (index : UniIndex) : Ancestor tree index index
  | parent {index child parent : UniIndex}
      (path : Ancestor tree child index)
      (node : TreeNode) (found : tree.nodeAt child = some node)
      (edge : node.parent = some parent) : Ancestor tree parent index

def localOwns (location : LocationState) (held : Bool) : Prop :=
  location.possible = true ∧
    match location.permission with
    | .Cell | .Unique | .ReservedFrz false => True
    | .ReservedIM | .ReservedFrz true => held = false
    | .Frozen | .Disabled => False

def foreignCompatible (location : LocationState) (held : Bool) : Prop :=
  location.possible = true ∧
    (held = false ∨ location.permission = .Cell ∨
      (location.accessed = false ∧ location.permission ≠ .ReservedIM))

/-- Coherence of the existing forest and range map. Parent depth makes
root traversal finite independently of the operations being verified. -/
structure CoherentForest (tree : BorrowTree) : Prop where
  ranges : tree.locations.WellFormed
  indexFits : tree.nodes.data.size ≤ 2 ^ 32
  rootsDistinct : tree.roots.toList.Nodup
  rootsPresent : ∀ root ∈ tree.roots, ∃ node, tree.nodeAt root = some node
  parentDepth : ∃ depth : UniIndex → Nat,
    (∀ index node, tree.nodeAt index = some node → depth index ≤ tree.nodes.size) ∧
    (∀ index node parent,
      tree.nodeAt index = some node → node.parent = some parent → depth parent < depth index)
  rootEdges : ∀ index node, tree.nodeAt index = some node →
    (node.parent = none ↔ index ∈ tree.roots)
  childEdges : ∀ index node, tree.nodeAt index = some node →
    node.children.toList.Nodup ∧
      (∀ child ∈ node.children, ∃ data, tree.nodeAt child = some data ∧ data.parent = some index) ∧
      (∀ child data, tree.nodeAt child = some data → data.parent = some index → child ∈ node.children)
  parentPresent : ∀ index node parent, tree.nodeAt index = some node →
    node.parent = some parent → ∃ data, tree.nodeAt parent = some data

/-- Independent ownership facts for a concrete-provenance slice region.
The conditions describe the existing tag, topology and protected sibling
permissions byte by byte, without referring to MIR execution outcomes. -/
structure ExclusiveRegion (before : State) (length : UInt64)
    (storage : InitializedRegion before length) (tag : BorTag) where
  tracker : MachineHooks.BorrowState
  tracked : before.machine.borrowTracker = some tracker
  coherent : CoherentForest storage.entry.allocation.extra
  source : UniIndex
  tagKnown : storage.entry.allocation.extra.indexOfTag tag = some source
  sourcePresent : ∃ node, storage.entry.allocation.extra.nodeAt source = some node ∧ node.tag = tag
  covers : ∀ distance < length.toNat,
    ∃ segment ∈ storage.entry.allocation.extra.locations.entries,
      segment.range.start.toNat ≤ storage.relativeStart.bytes.toNat + distance ∧
      storage.relativeStart.bytes.toNat + distance < segment.range.stop.toNat
  exclusive : ∀ distance < length.toNat,
    ∀ segment ∈ storage.entry.allocation.extra.locations.entries,
      segment.range.start.toNat ≤ storage.relativeStart.bytes.toNat + distance →
      storage.relativeStart.bytes.toNat + distance < segment.range.stop.toNat →
      ∀ index node, storage.entry.allocation.extra.nodeAt index = some node →
        ∃ location, storage.entry.allocation.extra.locationStateAt segment.data index = some location ∧
          (Ancestor storage.entry.allocation.extra index source →
            localOwns location (tracker.global.protectedTags.contains node.tag)) ∧
          (¬ Ancestor storage.entry.allocation.extra index source →
            foreignCompatible location (tracker.global.protectedTags.contains node.tag))

/-- Caller-facing representation for concrete initialized slices on the
pinned 64-bit target. The empty case does not require an allocation. This
contract has no bounded count and no precondition on a successful replay. -/
structure PreparedConcreteSlice
    (program : BodyVCGen.LoadedProgram) (addresses : U → AllocAddresses.GlobalAddressState)
    (before : State) (target : TargetDataLayout)
    (pointer : Pointer (Option Provenance)) (length count : UInt64) : Prop where
  arguments : EntryArguments program before target pointer length count
  width : target.pointerWidth = .w64
  nonnull : pointer.offset.bytes ≠ 0
  addressable : length.toNat < 2 ^ 63
  region : length ≠ 0 →
    ∃ (storage : InitializedRegion before length) (tag : BorTag) (base : UInt64),
      pointer.provenance = some (.concrete storage.id tag) ∧
      pointer.offset.bytes.toNat = base.toNat + storage.relativeStart.bytes.toNat ∧
      base.toNat + storage.entry.allocation.byteSize.bytes.toNat < 2 ^ 64 ∧
      ((addresses before.machine.user).baseAddr.find? (·.allocId == storage.id)) =
        some ⟨storage.id, base⟩ ∧
      Nonempty (ExclusiveRegion before length storage tag)

/-- The saved destination is represented in caller coordinates. Memory
destinations may be uninitialized before the call. -/
inductive ReturnDestinationShape (before : State) (destination : RuntimeStackPlace Provenance) : Prop where
  | localSlot (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
      (index : LocalId) (layout : LocalLayout) (slot : LocalState Provenance LocalLayout)
      (current : before.stack.frames.pop.back? = some caller)
      (saved : destination = .frameLocal (before.stack.frames.size - 2) index none
        layout caller.localsIdentity)
      (lookup : caller.locals[index]? = some slot)
      (cached : slot.layout = some layout)
      (immediate : ∃ value, slot.value = .live (.immediate value)) :
      ReturnDestinationShape before destination
  | memorySlot (place : MPlaceTy Provenance) (id : AllocId) (tag : BorTag)
      (entry : LocalAllocation Provenance BorrowTree K)
      (saved : destination = .memory place)
      (provenance : place.mplace.ptr.provenance = some (.concrete id tag))
      (live : before.machine.memory.live[id]? = some entry)
      (writable : entry.allocation.mutability = .Mut)
      (tagKnown : (entry.allocation.extra.indexOfTag tag).isSome = true) :
      ReturnDestinationShape before destination

/-- Common representation conditions to be derived from production frame
preparation. These supplement the input-region predicate independently of
step outcomes. -/
structure PreparedFrameShape (before : State)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) : Prop where
  current : before.stack.currentFrame? = some frame
  localsAligned : frame.locals.size = frame.body.locals.size
  localsUntouched : ∀ index slot, 3 ≤ index →
    frame.locals[index]? = some slot → slot.value = .dead
  noVarargs : frame.vaList = #[]
  destination : ReturnDestinationShape before frame.returnPlace
  continuation : match frame.returnContinuation with
    | .goto (some target) _ =>
      ∃ caller, before.stack.frames.pop.back? = some caller ∧ target < caller.body.basicBlocks.size
    | .goto none _ => False
    | .stop _ => before.stack.frames.size = 1
  releaseLedger : ∀ tracker, before.machine.borrowTracker = some tracker →
    ∃ frameTracker, frame.extra.borrowTracker = some frameTracker ∧
      ∀ id tag, (id, tag) ∈ frameTracker.protectedTags →
        tracker.global.protectedTags.contains tag = true ∧
          ∃ entry : LocalAllocation Provenance BorrowTree K,
            before.machine.memory.live[id]? = some entry ∧
              (entry.allocation.extra.indexOfTag tag).isSome = true

theorem PreparedConcreteSlice.entered
    {program : BodyVCGen.LoadedProgram} {addresses : U → AllocAddresses.GlobalAddressState}
    {before : State} {target : TargetDataLayout} {pointer : Pointer (Option Provenance)}
    {length count : UInt64} (admitted : PreparedConcreteSlice program addresses before target pointer length count) :
    WholeBodyWP.entryMatchesLoaded program.root before :=
  admitted.arguments.entered

end DuplicatePrefix.SourceDomain

#print axioms DuplicatePrefix.SourceDomain.PreparedConcreteSlice.entered

import duplicate_prefix.CurrentLenFnEntry

namespace DuplicatePrefix.CurrentLenFnEntry

open Miri.ABI Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open ArchiveForestProjection GeneralRangeMapOrigins RetagSharedChild SourceDomain

/-- The physical heap lookup identifies a single tree and selected slot for the
read grant and release footprint exported by the protected receiver setup. -/
theorem releaseCertificates
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (parentTag tag : BorTag) (parent root : UniIndex) (offset len : UInt64)
    (tags : ProtectedTags)
    (readable : CurrentSharedRetag.ReadGrant machine entry id tag root offset len tags)
    (framed : FrameGrant machine entry id parentTag tag parent offset len tags) :
    let read := entry.allocation.extra.performNormalAccessRange parentTag (Size.ofBytes offset)
      (Size.ofBytes len) .Read tags .VisitChildrenOfAccessed
    let inside := DedupRangeMap.new (Size.ofBytes len) sharedState
    let child := (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag inside .Frozen true).tree
    ∃ index,
      machine.memory.live[id]? = some {entry with allocation := entry.allocation.setExtra child} ∧
      CoherentForest child ∧ child.roots = #[root] ∧ child.locations.size = entry.allocation.extra.locations.size ∧
      child.indexOfTag tag = some index ∧
      (∃ node, child.nodeAt index = some node ∧ node.tag = tag ∧ node.defaultInitialPermission = .Frozen) ∧
      SharedChildFrame entry.allocation.extra read.tree child parent index tag (Size.ofBytes offset)
        (Size.ofBytes len) inside ∧
      ∀ point : UInt64, offset.toNat ≤ point.toNat → point.toNat < (offset+len).toNat →
        ∀ row, ValueAt child.locations point row → LocationAccessRights child row tags index .Read := by
  intro read inside child
  obtain ⟨position, actualLookup, actualKey, attached⟩ := framed
  obtain ⟨tree, index, selectedLookup, coherent, roots, size, selectedKey, node, owned⟩ := readable
  have sameAllocation := Option.some.inj (selectedLookup.symm.trans actualLookup)
  have sameTree : tree = child :=
    congrArg (fun stored : LocalAllocation Provenance BorrowTree MiriMemoryKind => stored.allocation.extra) sameAllocation
  have selected : child.indexOfTag tag = some index := sameTree ▸ selectedKey
  have sameSlot : index = position := Option.some.inj (selected.symm.trans actualKey)
  subst tree
  subst index
  exact ⟨position, actualLookup, coherent, roots, size, actualKey, node, attached, owned⟩

#print axioms releaseCertificates
end DuplicatePrefix.CurrentLenFnEntry

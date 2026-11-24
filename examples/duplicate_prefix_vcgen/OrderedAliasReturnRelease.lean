import PhysicalActiveEndCall
import ReleaseRetainsWatch
import RetainedSlice

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open SourceDomain ArchiveForestProjection ScopedPhysicalRelease RetagReleaseFootprint RetagReleaseRights
open GeneralRangeMapOrigins

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- The actual frame ledger first releases the source protector and then
re-reads the same heap key to release the output protector on that updated
allocation. Both releases run with the original global protection set. -/
theorem orderedAliasReturnRelease
    {machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    (source : RootZeroShallowReturn.RetainedSlice machine)
    (owned : FrameState) (outputTag : BorTag) (output parent : UniIndex)
    (ledger : owned.protectedTags = #[(source.id,source.tag),(source.id,outputTag)])
    (node : TreeNode)
    (tagAt : source.entry.allocation.extra.indexOfTag outputTag = some output)
    (nodeAt : source.entry.allocation.extra.nodeAt output = some node)
    (which : node.tag = outputTag) (edge : node.parent = some parent) (hidden : node.isExposed = false)
    (foreign : ¬ Ancestor source.entry.allocation.extra output source.source)
    (coherent : CoherentForest source.entry.allocation.extra)
    (lower upper : UInt64) (start : Size)
    (outside : start.bytes.toNat < lower.toNat ∨ upper.toNat ≤ start.bytes.toNat)
    (visited : VisitsWithin source.entry.allocation.extra source.source lower.toNat upper.toNat)
    (vacant : VacantRows source.entry.allocation.extra)
    (owner : OwnedOn (fun row => LocationRights source.entry.allocation.extra row
      source.tracker.global.protectedTags source.source) lower upper source.entry.allocation.extra.locations)
    (outputRange : ReleaseRange source.entry.allocation.extra output start 1 true)
    (outputRights : OwnedOn (fun row => LocationRights source.entry.allocation.extra row
      source.tracker.global.protectedTags output) start.bytes (start.bytes+1) source.entry.allocation.extra.locations) :
    ∃ tree final,
      StackPopRelease.Plan source.tracker.global.protectedTags owned.protectedTags.toList machine.memory final ∧
      final.live[source.id]? = some {source.entry with allocation := source.entry.allocation.setExtra tree} ∧
      tree = {source.entry.allocation.extra with locations := tree.locations} ∧
      CoherentForest tree ∧ tree.locations.size = source.entry.allocation.extra.locations.size ∧
      OwnedOn (fun row => LocationRights tree row (source.tracker.global.endCall owned).protectedTags parent)
        start.bytes (start.bytes+1) tree.locations := by
  let original := source.entry.allocation.extra
  let tags := source.tracker.global.protectedTags
  obtain ⟨middle, releaseSource, middleShape, good, size, outsideRows, clean, outputScope⟩ :=
    releasePreservesWatch original source.tag source.source source.root output tags
      source.indexed coherent source.roots source.node node source.found source.unexposed nodeAt foreign
      lower upper visited vacant owner _ _ outputRange.accessedWithin
  obtain ⟨sameLength,kept⟩ := outsideRows
  have unitFits : start.bytes.toNat + 1 ≤ original.locations.size.bytes.toNat := by
    simpa using outputRange.extent
  have stop : (start.bytes+1).toNat = start.bytes.toNat+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt unitFits original.locations.size.bytes.toNat_lt)
  have middleRights : OwnedOn (fun row => LocationRights middle row tags output)
      start.bytes (start.bytes+1) middle.locations := by
    intro position valid nonempty lo hi
    have oldBound : position < original.locations.entries.size := sameLength ▸ valid
    obtain ⟨geometry,data⟩ := kept position valid
    rw [geometry] at lo hi
    have atPoint : original.locations.entries[position].range.start ≤ start.bytes :=
      UInt64.le_iff_toNat_le.mpr (by omega)
    have beforeEnd : start.bytes < original.locations.entries[position].range.stop := UInt64.lt_iff_toNat_lt.mpr hi
    have sameRow := data start.bytes atPoint beforeEnd outside
    rw [sameRow]
    change LocationRights middle original.locations.entries[position].data tags output
    have localRight := rights_table original middle.locations _ tags output (outputRights position oldBound nonempty lo hi)
    exact (congrArg (fun t => LocationRights t original.locations.entries[position].data tags output) middleShape) ▸ localRight
  have scope : ReleaseRange middle output start 1 true := by
    refine ReleaseRange.ofActiveByteScope good ?_ ⟨source.root,?_⟩ outputScope clean
    · rw [size]; exact unitFits
    · rw [middleShape]; exact source.roots
  have middleKey : middle.indexOfTag outputTag = some output := by rw [middleShape]; exact tagAt
  have middleNode : middle.nodeAt output = some node := by rw [middleShape]; exact nodeAt
  have listed : outputTag ∈ owned.protectedTags.toList.map Prod.snd := by simp [ledger]
  obtain ⟨after, releaseOutput, shape, formed, sameSize, retained⟩ :=
    physicalActiveReleasePreservesParent middle source.tracker.global owned outputTag output parent node start
      middleKey middleNode which edge hidden good scope listed middleRights
  let first := StackPopRelease.commitTree machine.memory source.id source.entry middle
  let updated := {source.entry with allocation := source.entry.allocation.setExtra middle}
  let final := StackPopRelease.commitTree first source.id updated after
  have midLookup : first.live[source.id]? = some updated :=
    StackPopRelease.lookup_commit_same machine.memory source.id source.entry middle
  have tail : StackPopRelease.Plan tags [(source.id,outputTag)] first final :=
    .live source.id outputTag updated after [] first final midLookup releaseOutput (.nil final)
  have plan : StackPopRelease.Plan tags [(source.id,source.tag),(source.id,outputTag)] machine.memory final :=
    .live source.id source.tag source.entry middle [(source.id,outputTag)] machine.memory final source.present releaseSource tail
  have finalLookup := StackPopRelease.lookup_commit_same first source.id updated after
  refine ⟨after,final,by simpa [ledger] using plan,?_,?_,formed,sameSize.trans size,retained⟩
  · exact finalLookup
  · exact shape.trans (congrArg (fun tree : BorrowTree => {tree with locations := after.locations}) middleShape)

#print axioms orderedAliasReturnRelease
end DuplicatePrefix.CanonicalCallDomain

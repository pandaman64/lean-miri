import ActiveReleaseRangeOfCall
import PhysicalSlotActiveRelease
import duplicate_prefix.StackPopRelease

namespace DuplicatePrefix.CanonicalCallDomain

open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows
open SourceDomain ArchiveForestProjection RetagReleaseRights RetagReleaseFootprint
open GeneralRangeMapOrigins

private theorem localGrantAfterRemovingMore (state : Tree.LocationState) (held remaining : Bool)
    (subset : remaining = true → held = true) (owns : localOwns state held) :
    localOwns state remaining := by
  cases held <;> cases remaining <;> simp_all [localOwns]
  cases permission : state.permission <;> simp_all
  rename_i interiorMutable
  cases interiorMutable <;> simp_all

private theorem foreignGrantAfterRemovingMore (state : Tree.LocationState) (held remaining : Bool)
    (subset : remaining = true → held = true) (owns : foreignCompatible state held) :
    foreignCompatible state remaining := by
  cases held <;> cases remaining <;> simp_all [foreignCompatible]

/-- The physical output protector is released using the pre-pop tag set.
The saved parent retains byte write rights after all tags owned by the
frame are removed by the actual `endCall` operation. -/
theorem physicalActiveReleasePreservesParent
    (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (tag : BorTag)
    (holder parent : UniIndex) (node : TreeNode) (start : Size)
    (known : tree.indexOfTag tag = some holder)
    (found : tree.nodeAt holder = some node) (tagMatches : node.tag = tag)
    (edge : node.parent = some parent) (unexposed : node.isExposed = false)
    (coherent : CoherentForest tree) (extent : ReleaseRange tree holder start 1 true)
    (owned : tag ∈ frame.protectedTags.toList.map Prod.snd)
    (rights : OwnedOn (fun row => LocationRights tree row global.protectedTags holder)
      start.bytes (start.bytes + 1) tree.locations) :
    ∃ after, tree.releaseProtector tag global.protectedTags = ⟨after, .Released⟩ ∧
      after = {tree with locations := after.locations} ∧ CoherentForest after ∧
      after.locations.size = tree.locations.size ∧
      OwnedOn (fun row => LocationRights after row (global.endCall frame).protectedTags parent)
        start.bytes (start.bytes + 1) after.locations := by
  obtain ⟨root, roots⟩ := extent.root (by decide)
  have endpoint : (start.bytes+1).toNat = start.bytes.toNat+1 := by
    rw [UInt64.toNat_add,UInt64.toNat_one]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt extent.extent tree.locations.size.bytes.toNat_lt)
  obtain ⟨after, release, shape, afterCoherent, size, parentRights⟩ :=
    PhysicalSlotActiveRelease.release tree global.protectedTags tag holder parent root node found tagMatches
      edge unexposed known coherent roots start.bytes (start.bytes + 1) (by rw [endpoint]; exact extent.visitsWithin)
      (fun _ missing _ inside => extent.vacant _ missing _ (Array.mem_iff_getElem.mpr ⟨_,inside,rfl⟩)) rights
  have subset : ∀ query, (global.endCall frame).protectedTags.contains query = true →
      (global.protectedTags.remove tag).contains query = true := by
    intro query current
    have distinct : query ≠ tag := by
      intro same
      simp [same, StackPopRelease.end_call_contains, owned] at current
    rw [contains_remove_other _ _ _ distinct]
    rw [StackPopRelease.end_call_contains] at current
    split at current
    · contradiction
    · exact current
  refine ⟨after, release, shape, afterCoherent, size, ?_⟩
  intro position valid low first last index current atIndex
  obtain ⟨state, knownState, localRight, foreignRight⟩ :=
    parentRights position valid low first last index current atIndex
  exact ⟨state, knownState,
    fun related => localGrantAfterRemovingMore _ _ _ (subset current.tag) (localRight related),
    fun unrelated => foreignGrantAfterRemovingMore _ _ _ (subset current.tag) (foreignRight unrelated)⟩

#print axioms physicalActiveReleasePreservesParent

end DuplicatePrefix.CanonicalCallDomain

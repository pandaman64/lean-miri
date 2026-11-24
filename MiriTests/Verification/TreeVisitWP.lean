import Miri.Verification.TreeVisitWP

namespace MiriTests.Verification.TreeVisitWP

open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Verification.TreeVisitWP

set_option maxRecDepth 65536
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-- Distinct scheduled nodes generate independent permission obligations on
the original location, even when their local/foreign relationships differ. -/
example (tree : NormalTreeState) (root first second : Nat) (kind : AccessKind)
    (distinct : first ≠ second) :
    (tree.processEvents root kind [⟨first, .LocalAccess⟩, ⟨second, .ForeignAccess⟩]).status =
      .Completed ↔ EventAllowed tree kind ⟨first, .LocalAccess⟩ ∧
        EventAllowed tree kind ⟨second, .ForeignAccess⟩ := by
  rw [events_complete_iff _ _ _ _ (by simp [distinct])]
  simp

private def fork : TraversalTree := ⟨#[⟨none, [1, 2]⟩, ⟨some 0, []⟩,
  ⟨some 0, [3]⟩, ⟨some 2, []⟩]⟩

/-- When the access is through 1, 3 is visited as foreign exactly when both
its own pruning check and the branch's check permit the visit. -/
example (skip : Nat → Bool) :
    (⟨3, .ForeignAccess⟩ : TraversalEvent) ∈
      (fork.traverseWithSkip 1 .SkipChildrenOfAccessed skip).2 ↔
    skip 2 = false ∧ skip 3 = false := by
  have branch : fork.ForeignBranch .SkipChildrenOfAccessed (fork.ancestorPath 1) none true 2 := by
    have path : fork.ancestorPath 1 = [1, 0] := by cbv
    rw [path]
    exact .above (.here (by decide) (by decide +kernel) (by decide))
  rw [TraversalTree.foreign_visit_iff]
  constructor
  · rintro ⟨root, chosen, reaches⟩
    have path : fork.ancestorPath 1 = [1, 0] := by cbv
    rw [path] at chosen
    have rootIs : root = 2 := by
      cases chosen with
      | here enter => contradiction
      | above higher =>
        cases higher with
        | here _ child offPath =>
          have child' : root ∈ [1, 2] := child
          simp at child'
          rcases child' with same | answer
          · subst root
            contradiction
          · exact answer
        | above impossible => cases impossible
    subst root
    cases reaches with
    | child enter edge reaches =>
      have single : _ ∈ [3] := edge
      simp at single
      subst_vars
      cases reaches with
      | here finish => exact ⟨enter, finish⟩
      | child _ empty => contradiction
  · rintro ⟨enter, finish⟩
    exact ⟨2, branch, .child enter (by decide +kernel) (.here finish)⟩

private def p : BorTag := ⟨2, by decide⟩
private def q : BorTag := ⟨3, by decide⟩
private def bytes := Size.ofBytes 1
private def permissions := DedupRangeMap.new bytes (⟨.ReservedFrz false, false, .None⟩ : LocationState)
private def protectors := (({} : ProtectedTags).insert p .StrongProtector).insert q .StrongProtector
private def parent := (BorrowTree.new BorTag.one bytes).newChild Size.ZERO (.concrete BorTag.one)
  p permissions (.ReservedFrz false) true
private def child := parent.tree.newChild Size.ZERO (.concrete p) q permissions (.ReservedFrz false) true
private def initial := (child.tree.locations.entries[0]?.map (·.data)).getD default
private def read := child.tree.performNormalAccessAt initial ⟨1⟩ .Read protectors .VisitChildrenOfAccessed

/-- The actual normal read on the parent visits its descendant as foreign.
A later write through the descendant visits the original source as local. -/
example :
    (⟨2, .ForeignAccess⟩ : TraversalEvent) ∈ read.access.visited ∧
      TagVisit child.tree read.location protectors q p .Write .VisitChildrenOfAccessed .LocalAccess := by
  have pAt : child.tree.indexOfTag p = some ⟨1⟩ := by cbv
  have qAt : child.tree.indexOfTag q = some ⟨2⟩ := by cbv
  constructor
  · have complete : read.access.status = .Completed := by cbv
    apply (tag_visit_iff_completed_normal child.tree initial protectors p q .Read .VisitChildrenOfAccessed
      .ForeignAccess ⟨1⟩ ⟨2⟩ pAt qAt complete).mp
    apply (tag_foreign_iff child.tree initial protectors p q .Read .VisitChildrenOfAccessed
      ⟨1⟩ ⟨2⟩ pAt qAt).mpr
    have path : (child.tree.normalView initial protectors).topology.ancestorPath 1 = [1, 0] := by cbv
    dsimp only
    rw [show (⟨1⟩ : UniIndex).toNat = 1 by rfl, path]
    refine ⟨2, .here (by decide) ?_ (by decide), ?_⟩
    · cbv
      exact .head _
    · have size : (child.tree.normalView initial protectors).topology.nodes.size = 3 := by cbv
      rw [size, show (⟨2⟩ : UniIndex).toNat = 2 by rfl]
      exact .here (by cbv)
  · apply (tag_local_snapshot_iff child.tree initial read.location protectors protectors q p
      .VisitChildrenOfAccessed .VisitChildrenOfAccessed).mpr
    apply (tag_local_iff child.tree initial protectors q p .Read .VisitChildrenOfAccessed
      ⟨2⟩ ⟨1⟩ qAt pAt).mpr
    cbv
    exact .tail _ (.head _)

end MiriTests.Verification.TreeVisitWP

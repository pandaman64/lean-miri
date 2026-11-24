import duplicate_prefix.RootAcceptedAsMut
import duplicate_prefix.AsMutDisjointByte

namespace DuplicatePrefix.RootAcceptedAsMutAlias

open Miri Miri.ABI Miri.Concurrency Miri.DataStructures Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open Miri.Verification.RangeModifyLaw
open CanonicalConfigFacts PreparedArguments SourceDomain ArchiveForestProjection NonemptyReturnWatch AsMutHolderScope

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

/-- Source and raw branch ownership retained by the actual mutable helper. -/
structure ActiveImage (tree : BorrowTree) (tags : ProtectedTags) (holder raw : UniIndex)
    (oldTag : BorTag) (lo hi : UInt64) : Prop where
  key : tree.indexOfTag oldTag = some holder
  hidden : (tree.nodeAt holder).map TreeNode.isExposed = some false
  path : BetweenTags tree tags holder raw
  footprint : AccessedCopyHolderRights.Footprint tree tags raw holder lo hi

/-- A physical writer and its call-owned protector share the source's
allocation but refer to a distinct byte. -/
structure ReturnWatch (tree : BorrowTree) (actor : UniIndex) (start stop : UInt64) where
  holder : UniIndex
  writer : UniIndex
  holderNode : TreeNode
  writerNode : TreeNode
  holderAt : tree.nodeAt holder = some holderNode
  writerAt : tree.nodeAt writer = some writerNode
  foreign : ¬ Ancestor tree holder actor
  byte : UInt64
  scope : AccessedWithin tree holder byte (byte+1)
  allows : UniIndex → ProtectedTags → Prop
  writerReady : ∀ index tags, allows index tags → ∃ node, tree.nodeAt index = some node
  rights : ∀ index tags, allows index tags →
    EachByte tree.locations (fun point row => (point.toNat < start.toNat ∨ stop.toNat ≤ point.toNat) →
      point = byte → LocationRights tree row tags index)

structure ReturnWatch.After {tree : BorrowTree} {actor : UniIndex} {start stop : UInt64}
    (before : ReturnWatch tree actor start stop) (next : BorrowTree) (raw : UniIndex)
    (reservation rawTag : BorTag) : Prop where
  active : AccessedWithin next before.holder before.byte (before.byte+1)
  foreign : ¬ Ancestor next before.holder raw
  keys : ∀ old, old ≠ reservation → old ≠ rawTag → next.indexOfTag old = tree.indexOfTag old
  holderAt : ∃ node, next.nodeAt before.holder = some node ∧
    node.tag = before.holderNode.tag ∧ node.parent = before.holderNode.parent ∧ node.isExposed = before.holderNode.isExposed
  writerAt : ∃ node, next.nodeAt before.writer = some node ∧
    node.tag = before.writerNode.tag ∧ node.parent = before.writerNode.parent ∧ node.isExposed = before.writerNode.isExposed
  rights : ∀ index tags, before.allows index tags →
    EachByte next.locations (fun point row => (point.toNat < start.toNat ∨ stop.toNat ≤ point.toNat) →
      point = before.byte → LocationRights next row tags index)

theorem ReturnWatch.preserve
    {tree middle installed : BorrowTree} {global : TreeBorrows.GlobalState} {inputTag : BorTag}
    {parent root reservation raw : UniIndex} {start len : Size}
    (before : ReturnWatch tree parent start.bytes (start.bytes+len.bytes))
    (stage : AsMutDisjointByte.Stages tree middle installed global inputTag parent root reservation raw start len)
    (data : FrozenReborrowInputs.StageData tree global.protectedTags inputTag global.nextPointerTag parent root
      start len (AsMutDisjointByte.firstRows len) false) :
    before.After ((installed.releaseProtector (AsMutDisjointByte.rawTag global) (AsMutDisjointByte.mask global)).tree)
      raw global.nextPointerTag (AsMutDisjointByte.rawTag global) := by
  have stable := stage.output data before.holder before.writer before.holderNode before.writerNode
    before.holderAt before.writerAt before.foreign global.protectedTags before.byte (before.byte+1)
    before.scope (fun _ => False) (fun _ _ _ _ _ _ impossible => impossible.elim)
  refine ⟨stable.1,stable.2.1,stable.2.2.1,stable.2.2.2.1,stable.2.2.2.2.1,?_⟩
  intro writer tags allowed
  obtain ⟨node,atWriter⟩ := before.writerReady writer tags allowed
  exact (stage.output data before.holder writer before.holderNode node before.holderAt atWriter
    before.foreign tags before.byte (before.byte+1) before.scope (· = before.byte)
    (before.rights writer tags allowed)).2.2.2.2.2

/-- Exact post-release proof data for the machine wrapper, before relating
the selected raw index to its runtime witness. -/
structure CarrierImage {tree : BorrowTree} {global : TreeBorrows.GlobalState} {inputTag : BorTag}
    {parent : UniIndex} {start len : Size}
    (watch : ReturnWatch tree parent start.bytes (start.bytes+len.bytes)) (raw : UniIndex) : Prop where
  rawKey : (AsMutDisjointByte.released tree global inputTag start len).indexOfTag
    (AsMutDisjointByte.rawTag global) = some raw
  tagAbsent : global.protectedTags.contains (AsMutDisjointByte.rawTag global) = false
  size : (AsMutDisjointByte.released tree global inputTag start len).locations.size = tree.locations.size
  active : ActiveImage (AsMutDisjointByte.released tree global inputTag start len)
    global.protectedTags parent raw inputTag start.bytes (start.bytes+len.bytes)
  output : watch.After (AsMutDisjointByte.released tree global inputTag start len)
    raw global.nextPointerTag (AsMutDisjointByte.rawTag global)

theorem carrierImage
    (tree : BorrowTree) (global : TreeBorrows.GlobalState) (inputTag : BorTag)
    (parent root : UniIndex) (start len : Size)
    (watch : ReturnWatch tree parent start.bytes (start.bytes+len.bytes))
    (data : FrozenReborrowInputs.StageData tree global.protectedTags inputTag global.nextPointerTag parent root
      start len (AsMutDisjointByte.firstRows len) false)
    (capacity : RetagInsertionCapacity.Ready tree) (space : tree.nodes.size+1 < 2^32)
    (age : ∀ i node, tree.nodeAt i = some node → node.tag.value.toNat < global.nextPointerTag.value.toNat)
    (protectorAge : ∀ tag, global.protectedTags.contains tag = true → tag.value.toNat < global.nextPointerTag.value.toNat)
    (tagRoom : global.nextPointerTag.value.toNat+2 < 2^64)
    (sourceNode : TreeNode) (sourceAt : tree.nodeAt parent = some sourceNode)
    (hidden : sourceNode.isExposed = false)
    (sourceScope : AccessedWithin tree parent start.bytes (start.bytes+len.bytes)) :
    ∃ raw, CarrierImage (global := global) (inputTag := inputTag) watch raw := by
  obtain ⟨middle,raw,stages⟩ := AsMutDisjointByte.stages tree global
    inputTag parent root start len data capacity space age protectorAge tagRoom
  obtain ⟨key,unexposed,rawKey,path,footprint,size⟩ :=
    stages.activeHolder data sourceNode sourceAt hidden sourceScope
  refine ⟨raw,?_⟩
  refine {rawKey := ?_, tagAbsent := stages.absentRaw, size := ?_, active := ?_, output := ?_}
  · unfold AsMutDisjointByte.released
    exact rawKey
  · unfold AsMutDisjointByte.released
    exact size
  · unfold AsMutDisjointByte.released
    exact ⟨key,unexposed,path,footprint⟩
  · unfold AsMutDisjointByte.released
    exact watch.preserve stages data

end DuplicatePrefix.RootAcceptedAsMutAlias

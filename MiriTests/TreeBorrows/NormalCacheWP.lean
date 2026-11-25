import Miri.TreeBorrows.TreeState

open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows

private def root : UniIndex := ⟨0⟩
private def first : UniIndex := ⟨1⟩
private def last : UniIndex := ⟨2⟩
private def missing : UniIndex := ⟨3⟩
private def bytes : ByteRange := ⟨0, 1⟩

private def exposedChild (tag : BorTag) (parent : UniIndex) : TreeNode :=
  { tag, parent := some parent, isExposed := true,
    defaultInitialPermission := .Unique, defaultInitialSifa := .None }

private def fixture (firstParent : UniIndex) : BorrowTree × LocationTree :=
  let tree := BorrowTree.new BorTag.one (Size.ofBytes 1)
  let base : TreeNode :=
    { tag := BorTag.one, parent := none, children := #[last, first],
      defaultInitialPermission := .Disabled, defaultInitialSifa := .None }
  let nodes := ((tree.nodes.insert root base).insert first
    (exposedChild ⟨2, by decide⟩ firstParent)).insert last
    (exposedChild ⟨3, by decide⟩ root)
  let location : LocationTree :=
    { perms := ({} : UniValMap Tree.LocationState).insert root ⟨.Unique, true, .None⟩
      exposedCache := ⟨((({} : UniValMap ExposedCacheNode).insert root ⟨2, 2⟩).insert
        first ⟨1, 1⟩).insert last ⟨1, 1⟩⟩ }
  ({ tree with nodes }, location)

private def visit (firstParent : UniIndex) : BorrowTree.TreeLocationAccessAtResult :=
  let (tree, location) := fixture firstParent
  tree.performTreeAccessAt location (some root) .Write {} .VisitChildrenOfAccessed bytes

-- Each foreign child loses its exposure, and each delta reaches the root.
#eval show IO Unit from do
  let after := visit root
  unless decide (after.status = none ∧
      after.location.exposedCache.nodes.get root = some ⟨0, 0⟩ ∧
      after.location.exposedCache.nodes.get first = some ⟨0, 0⟩ ∧
      after.location.exposedCache.nodes.get last = some ⟨0, 0⟩) do
    throw (IO.userError "The normal visit did not propagate both exposure deltas to the root")

-- The first child's cache delta is visible on failure. The second child's
-- cache remains at its initial value, even though its permission is written.
#eval show IO Unit from do
  let after := visit missing
  unless decide (after.status = some (.CacheFailure bytes (.MissingNode missing)) ∧
      after.location.exposedCache.nodes.get root = some ⟨2, 2⟩ ∧
      after.location.exposedCache.nodes.get first = some ⟨0, 0⟩ ∧
      after.location.exposedCache.nodes.get last = some ⟨1, 1⟩ ∧
      (after.location.perms.get last).map Tree.LocationState.permission = some .Disabled) do
    throw (IO.userError "The failed cache visit did not preserve the partial location")

-- The cycle is reported after the two permitted visits to a size-one map.
example :
    ({} : ExposedCache).updateExposurePre
      (({} : UniValMap TreeNode).insert root (exposedChild BorTag.one root)) root
      .None .Write (fun _ => False)
      (fun error after => error = .ParentCycle root ∧ after.nodes.get root = some ⟨2, 2⟩) := by
  simp [ExposedCache.updateExposurePre, ExposedCache.exposureChainPre, ExposedCache.exposureDelta,
    UniValMap.insert, UniValMap.size, UniValMap.get, UniValMap.extendTo,
    root, exposedChild, UniIndex.toNat, Id.run, pure, Pure.pure] <;> decide

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
out="$PWD/scratch/duplicate-prefix-vcgen"
source="$PWD/examples/duplicate_prefix_vcgen/duplicate_prefix.rs"
harness="$PWD/examples/duplicate_prefix_vcgen/runtime.rs"
mkdir -p "$out"
export LEAN_NUM_THREADS=1
export LEAN_PATH="$out:${LEAN_PATH:-$PWD/.lake/build/lib/lean}"
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output "$out/harness.json" --root miri_start --root duplicate_prefix::duplicate_prefix -- \
  "$harness" --crate-type=bin --crate-name duplicate_prefix_vcgen \
  -C debug-assertions=no -C overflow-checks=no -C panic=abort -Zmir-opt-level=0

tools/body-vc safety "$source" \
  --output "$out/Representative.lean" --no-build --no-check
lean -j1 -o "$out/Representative.olean" "$out/Representative.lean"
lean -j1 examples/duplicate_prefix_vcgen/VerifyGenerated.lean
lean -j1 examples/duplicate_prefix_vcgen/ScopedSafetyTransfer.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/PreparedArguments.olean" examples/duplicate_prefix_vcgen/PreparedArguments.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/SourceDomain.olean" examples/duplicate_prefix_vcgen/SourceDomain.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/MutableSliceRights.olean" examples/duplicate_prefix_vcgen/MutableSliceRights.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/MutableSliceRetag.olean" examples/duplicate_prefix_vcgen/MutableSliceRetag.lean
lean -j1 examples/duplicate_prefix_vcgen/SymbolicCopyAccess.lean
lean -j1 examples/duplicate_prefix_vcgen/RootMutableReborrow.lean
lean -j1 examples/duplicate_prefix_vcgen/ZeroProtector.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/ZeroTail.olean" examples/duplicate_prefix_vcgen/ZeroTail.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/ZeroBoolean.olean" examples/duplicate_prefix_vcgen/ZeroBoolean.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/ZeroAssignment.olean" examples/duplicate_prefix_vcgen/ZeroAssignment.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/ZeroNodes.olean" examples/duplicate_prefix_vcgen/ZeroNodes.lean
lean -j1 examples/duplicate_prefix_vcgen/ZeroSuffix.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/ZeroReturnDriver.olean" examples/duplicate_prefix_vcgen/ZeroReturnDriver.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/ZeroReturn.olean" examples/duplicate_prefix_vcgen/ZeroReturn.lean
mkdir -p "$out/empty_function"
lean -j1 --root=examples -o "$out/empty_function/FrameExit.olean" examples/empty_function/FrameExit.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/LanguageGuardStack.olean" examples/duplicate_prefix_vcgen/LanguageGuardStack.lean
lean -j1 examples/duplicate_prefix_vcgen/LanguageGuardCall.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/LanguageGuardValidity.olean" examples/duplicate_prefix_vcgen/LanguageGuardValidity.lean
lean -j1 examples/duplicate_prefix_vcgen/LanguageGuardAssignment.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/LanguageGuardPrepare.olean" examples/duplicate_prefix_vcgen/LanguageGuardPrepare.lean
lean -j1 examples/duplicate_prefix_vcgen/GuardReturnCopy.lean
lean -j1 examples/duplicate_prefix_vcgen/GuardPointerSwitch.lean
lean -j1 examples/duplicate_prefix_vcgen/GuardRuntimeReturn.lean
lean -j1 examples/duplicate_prefix_vcgen/LanguageGuardReturn.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/NestedGuardDriver.olean" examples/duplicate_prefix_vcgen/NestedGuardDriver.lean

"${BODY_VC_RUNNER:-$PWD/.lake/build/bin/native_runner}" "$out/harness.json" \
  --ui-source "$harness" --ui-flags '["-Zmiri-tree-borrows"]' \
  --profile --check-body-vc-input "$out/Representative.mir.json" 0 >"$out/proof.log" 2>&1
proof='body_vc: outcome=Except.ok (Miri.Verification.WholeBodyWP.Exit.scopeExit); normal=true; stopped=false; impossible=false; no_ub=true'
test "$(rg -c -x -F "$proof" "$out/proof.log")" = 7
test "$(rg -c '^body_vc:' "$out/proof.log")" = 7
rg '^body_vc\.proof_replay took' "$out/proof.log"
rg 'upstream_result: .*"detail":"0".*"kind":"exit"' "$out/proof.log"

adversarial="$PWD/examples/duplicate_prefix_vcgen/runtime_adversarial.rs"
for case in zero positive; do
  cfg=()
  if [[ "$case" == positive ]]; then
    cfg=(--cfg positive)
  fi
  LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
    --output "$out/adversarial-$case.json" --root miri_start --root duplicate_prefix::duplicate_prefix -- \
    "$adversarial" --crate-type=bin --crate-name small_root \
    -C debug-assertions=no -C overflow-checks=no -C panic=abort -Zmir-opt-level=0 "${cfg[@]}"
  "${BODY_VC_RUNNER:-$PWD/.lake/build/bin/native_runner}" "$out/adversarial-$case.json" \
    --ui-source "$adversarial" --ui-flags '["-Zmiri-tree-borrows"]' \
    --check-body-vc-input "$out/Representative.mir.json" 0 >"$out/adversarial-$case.log" 2>&1
  test "$(rg -c '^body_vc:' "$out/adversarial-$case.log")" = 1
done

rg -x -F "$proof" "$out/adversarial-zero.log"
rg '^run: finalized_exit code=0;' "$out/adversarial-zero.log"
rg '^body_vc: outcome=Except.error .*Tree Borrows write access: .*start := 1, stop := 2.*ProtectedDisabled.*Frozen.*no_ub=false$' \
  "$out/adversarial-positive.log"
rg '^run: undefined_behavior' "$out/adversarial-positive.log"

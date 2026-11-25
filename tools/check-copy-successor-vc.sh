#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
out="$PWD/scratch/copy-successor-vc"
fixture="$PWD/examples/duplicate_prefix_vcgen/runtime_copy_successor.rs"
mkdir -p "$out"
export LEAN_NUM_THREADS=1
export LEAN_PATH="$out:$PWD/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  Miri.Frontend.ImportBodyVC MiriTests.Verification.CopySuccessorObservation

for case in accepted rejected; do
  cfg=()
  if [[ "$case" == rejected ]]; then
    cfg=(--cfg rejected)
  fi
  LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
    --output "$out/$case.json" --root miri_start --root copy_then_load -- \
    "$fixture" --crate-type=bin --crate-name copy_successor \
    -C debug-assertions=no -C overflow-checks=no -C panic=abort -Zmir-opt-level=0 "${cfg[@]}"
done

tools/body-vc safety "$fixture" --root copy_then_load \
  --output "$out/SuccessorGenerated.lean" --no-build --no-check
lean -j1 --root="$out" -o "$out/SuccessorGenerated.olean" "$out/SuccessorGenerated.lean"
lean -j1 examples/duplicate_prefix_vcgen/CopySuccessorVC.lean

# Independent stock-runner checks of the accepted and rejected inputs against
# the same saved copy_then_load body. The Rust caller checks the returned byte.
for case in accepted rejected; do
  "${BODY_VC_RUNNER:-$PWD/.lake/build/bin/native_runner}" "$out/$case.json" \
    --ui-source "$fixture" --ui-flags '["-Zmiri-tree-borrows"]' \
    --check-body-vc-input "$out/SuccessorGenerated.mir.json" 0 >"$out/$case.log" 2>&1
  test "$(rg -c '^body_vc:' "$out/$case.log")" = 1
done
normal='body_vc: outcome=Except.ok (Miri.Verification.WholeBodyWP.Exit.scopeExit);'
rg -x -F "$normal normal=true; stopped=false; impossible=false; no_ub=true" "$out/accepted.log"
rg '^run: finalized_exit code=0;' "$out/accepted.log"
failure='^body_vc: outcome=Except.error .*Tree Borrows read access:'
rg "$failure .*start := 1, stop := 2.*ChildAccessForbidden.*Disabled.*no_ub=false$" "$out/rejected.log"
rg '^run: undefined_behavior' "$out/rejected.log"

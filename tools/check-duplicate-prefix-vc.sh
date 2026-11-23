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

"${BODY_VC_RUNNER:-$PWD/.lake/build/bin/native_runner}" "$out/harness.json" \
  --ui-source "$harness" --ui-flags '["-Zmiri-tree-borrows"]' \
  --profile --check-body-vc-input "$out/Representative.mir.json" 0 >"$out/proof.log" 2>&1
proof='body_vc: outcome=Except.ok (Miri.Verification.WholeBodyWP.Exit.scopeExit); normal=true; stopped=false; impossible=false; no_ub=true'
test "$(rg -c -x -F "$proof" "$out/proof.log")" = 7
test "$(rg -c '^body_vc:' "$out/proof.log")" = 7
rg '^body_vc\.proof_replay took' "$out/proof.log"
rg 'upstream_result: .*"detail":"0".*"kind":"exit"' "$out/proof.log"

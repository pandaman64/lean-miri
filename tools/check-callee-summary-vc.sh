#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
out="$PWD/scratch/callee-summary-vc"
fixture="$PWD/examples/callee_summary_vcgen/runtime.rs"
runner="${BODY_VC_RUNNER:-$PWD/.lake/build/bin/native_runner}"
mkdir -p "$out/lib/empty_function" "$out/lib/pointer_observation_vcgen"

export LEAN_NUM_THREADS=1
export LEAN_PATH="$out:$out/lib:$PWD/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build   Miri.Frontend.ImportBodyVC Miri.Verification.CalleeSummaryWP Miri.Verification.PointerFormationWP

LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh   --output "$out/runtime.json" --root miri_start -- "$fixture"   --crate-type=bin --crate-name callee_summary -C debug-assertions=no   -C overflow-checks=no -C panic=abort -Zmir-opt-level=0
tools/body-vc safety "$out/runtime.json" --root miri_start   --output "$out/Generated.lean" --no-build --no-check
lean -j1 --root="$out" -o "$out/Generated.olean" "$out/Generated.lean"
lean -j1 --root=examples -o "$out/lib/empty_function/Configuration.olean" \
  examples/empty_function/Configuration.lean
lean -j1 --root=examples -o "$out/lib/pointer_observation_vcgen/Fixture.olean" \
  examples/pointer_observation_vcgen/Fixture.lean
lean -j1 --root=examples/callee_summary_vcgen -o "$out/CallEntry.olean" \
  examples/callee_summary_vcgen/CallEntry.lean
cp examples/callee_summary_vcgen/CallCompilerData.lean "$out/CallCompilerData.lean"
lean -j1 --root="$out" -o "$out/CallCompilerData.olean" "$out/CallCompilerData.lean"
for module in ReflectedCallEntry CallAbiLiteral CallFrameEntry; do
  lean -j1 --root=examples/callee_summary_vcgen -o "$out/$module.olean" \
    "examples/callee_summary_vcgen/$module.lean"
done
lean -j1 --root=examples/callee_summary_vcgen -o "$out/CalleeBody.olean" \
  examples/callee_summary_vcgen/CalleeBody.lean
lean -j1 examples/callee_summary_vcgen/CallerObservation.lean
lean -j1 examples/callee_summary_vcgen/Verify.lean
lean -j1 examples/callee_summary_vcgen/ProtectorCleanup.lean
lean -j1 examples/callee_summary_vcgen/AssignResult.lean

"$runner" "$out/runtime.json" --ui-source "$fixture" --ui-flags '["-Zmiri-tree-borrows"]'   --check-body-vc-input "$out/Generated.mir.json" 0 >"$out/runtime.log" 2>&1
rg -x -F 'body_vc: outcome=Except.ok (Miri.Verification.WholeBodyWP.Exit.scopeExit); normal=true; stopped=false; impossible=false; no_ub=true'   "$out/runtime.log"
rg '^run: finalized_exit code=0;' "$out/runtime.log"

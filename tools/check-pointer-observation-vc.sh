#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

out="$PWD/scratch/pointer-observation-vc"
fixture="$PWD/examples/pointer_observation_vcgen"
saved="${1:-$PWD/scratch/copy-successor-vc/SuccessorGenerated.mir.json}"
mkdir -p "$out/lib/empty_function" "$out/lib/pointer_observation_vcgen"
export LEAN_NUM_THREADS=1
export LEAN_PATH="$out/lib:$PWD/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  Miri.Frontend.ImportBodyVC Miri.Input.EvalConfigurationCore Miri.Input.InitialMachine

if [[ -f "$saved" ]]; then
  cp "$saved" "$out/copy.mir.json"
elif [[ $# -eq 0 ]]; then
  LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
    --output "$out/copy.mir.json" --root copy_then_load -- \
    examples/duplicate_prefix_vcgen/runtime_copy_successor.rs --crate-type=lib --crate-name copy_successor \
    -C debug-assertions=no -C overflow-checks=no -C panic=abort -Zmir-opt-level=0
else
  printf 'Saved copy MIR is missing at %s\n' "$saved" >&2
  exit 1
fi

LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output "$out/pointers.mir.json" --root shared_read --root mutable_write --root raw_write -- \
  "$fixture/pointer_observation.rs" --crate-type=lib --crate-name pointer_observation \
  -C debug-assertions=no -C overflow-checks=no -C panic=abort -Zmir-opt-level=0

lean -j1 --root=examples -o "$out/lib/empty_function/Configuration.olean" \
  examples/empty_function/Configuration.lean
lean -j1 --root=examples -o "$out/lib/pointer_observation_vcgen/Fixture.olean" "$fixture/Fixture.lean"
for case in Copy Pointer; do
  cp "$fixture/$case.lean" "$out/$case.lean"
  lean -j1 --root="$out" -o "$out/lib/$case.olean" "$out/$case.lean" | tee "$out/$case.log"
  if rg 'sorryAx|native_decide' "$out/$case.log"; then
    exit 1
  fi
done

tools/body-vc safety "$out/copy.mir.json" --no-build --no-check --output "$out/GeneratedCopyRows.lean"
lean -j1 --root="$out" -o "$out/lib/GeneratedCopyRows.olean" "$out/GeneratedCopyRows.lean"
lean -j1 "$fixture/GeneratedCopy.lean" | tee "$out/GeneratedCopy.log"
if rg 'sorryAx|native_decide' "$out/GeneratedCopy.log"; then
  exit 1
fi

tools/body-vc safety "$out/pointers.mir.json" --root shared_read --no-build --no-check \
  --output "$out/GeneratedPointerRows.lean"
lean -j1 --root="$out" -o "$out/lib/GeneratedPointerRows.olean" "$out/GeneratedPointerRows.lean"
lean -j1 "$fixture/CheckGeneratedPointerRows.lean"

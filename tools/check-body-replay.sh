#!/usr/bin/env bash
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
runner="${BODY_REPLAY_RUNNER:-$root/.lake/build/bin/native_runner}"
output="${BODY_REPLAY_OUTPUT:-$root/scratch/body-replay-regression}"
source="$root/examples/body_vcgen/runtime.rs"
flags='["-Zmiri-tree-borrows"]'
mkdir -p "$output"

for scenario in positive negative; do
  rust_args=()
  if [[ "$scenario" == negative ]]; then
    rust_args+=(--cfg negative)
  fi
  LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
    --output "$output/$scenario.json" --root miri_start -- "$source" \
    --crate-type=bin --crate-name vc_audit -C debug-assertions=no \
    -C overflow-checks=no -C panic=abort -Zmir-opt-level=0 -A deref_nullptr "${rust_args[@]}"
  "$runner" "$output/$scenario.json" --ui-source "$source" --ui-flags "$flags" \
    >"$output/$scenario.ordinary.log" 2>&1
  "$runner" "$output/$scenario.json" --ui-source "$source" --ui-flags "$flags" --check-body-vc \
    >"$output/$scenario.checked.log" 2>&1
  grep '^upstream_result:' "$output/$scenario.ordinary.log" >"$output/$scenario.ordinary.result"
  grep '^upstream_result:' "$output/$scenario.checked.log" >"$output/$scenario.checked.result"
  cmp "$output/$scenario.ordinary.result" "$output/$scenario.checked.result"
  if grep -q '^body_vc:' "$output/$scenario.ordinary.log"; then
    echo "Unexpected body VC output in ordinary run ($scenario)" >&2
    exit 1
  fi
  test "$(grep -c '^body_vc:' "$output/$scenario.checked.log")" = 1
done

grep '^body_vc: outcome=.*; normal=true; stopped=false; impossible=false; no_ub=true$' \
  "$output/positive.checked.log"
grep '^body_vc: outcome=.*undefinedBehavior.*; normal=false; stopped=false; impossible=false; no_ub=false$' \
  "$output/negative.checked.log"
grep -Eq '^upstream_result: .*"detail":"0".*"kind":"exit"' "$output/positive.ordinary.result"
grep -Eq '^upstream_result: .*"kind":"ub"' "$output/negative.ordinary.result"

#!/usr/bin/env bash
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
source="${BODY_VC_PROJECT_SOURCE:-$root/examples/body_vcgen/control.rs}"
output="${BODY_VC_PROJECT_OUTPUT:-$root/scratch/body-vc-project}"
rm -rf "$output"

# Generation runs the project's lake build, including the sorry-bearing Safety module.
tools/body-vc safety "$source" --project "$output"
for file in lakefile.toml lean-toolchain Generated.lean Generated.mir.json Safety.lean; do
  test -f "$output/$file"
done
cmp lean-toolchain "$output/lean-toolchain"

# The derived theorems may depend on `safe`, but on no other sorry or axiom.
python3 - "$output/Safety.lean" "$output/AxiomCheck.lean" <<'EOF'
import re
import sys

source = open(sys.argv[1]).read()
checked, count = re.subn(
    r"theorem safe (.*?) := by\n  sorry -- Fill in to prove safety\.\n",
    lambda match: f"axiom safe {match.group(1)}\n", source, flags=re.S)
if count != 1:
    raise SystemExit("Safety.lean does not contain the generated `safe` placeholder")
checked = checked.replace("\nend Safety\n", """
open Lean Elab Command in
run_cmd do
  let allowed := [``propext, ``Quot.sound, ``Classical.choice, ``Safety.safe]
  for name in [``Safety.safeExecution, ``Safety.safeFromRoot, ``Safety.safeFromRoot'] do
    let axioms ← collectAxioms name
    unless axioms.contains ``Safety.safe do
      throwError "{name} does not use Safety.safe"
    for dependency in axioms do
      unless allowed.contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

end Safety
""")
open(sys.argv[2], "w").write(checked)
EOF
(cd "$output" && lake env lean -j1 AxiomCheck.lean)

# Regeneration keeps an edited Safety.lean unless --force is given.
printf -- '-- edited\n' >>"$output/Safety.lean"
tools/body-vc safety "$source" --project "$output" --no-build --no-check
grep -qx -- '-- edited' "$output/Safety.lean"
tools/body-vc safety "$source" --project "$output" --no-build --no-check --force
if grep -qx -- '-- edited' "$output/Safety.lean"; then
  echo "--force did not overwrite Safety.lean" >&2
  exit 1
fi
echo "Body VC project check passed: $output"

# Whole-body VC generation for imported Rust MIR

`control.rs` exports `count_up`, which has a conditional, a loop and a call
to the separately compiled `increment` function. [Verify.lean](Verify.lean)
imports the pinned compiler output and uses `BodyVCGen.loadProgram input 0`
to resolve the root and its available canonical callees. The example checks the
inferred graph, including the two edges into the shared return block, the
back edge to the loop header and the callee's separate equation table.

From the repository root, run the example with the pinned Lean toolchain.

```bash
flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  Miri.Frontend.ImportMIR Miri.Verification.BodyVCGen
lake env lean -j1 examples/body_vcgen/Verify.lean
```

Use `vcgen` on a `Triple (BodyVCGen.runProgram config limits program allowed)`
goal. Supply the initial-state predicate and any success and failure
postconditions. Use `BodyVCGen.prepareRoot` to prepare the selected compiler
instance on an initialized machine with typed arguments and a return
destination. The entry guard checks the current frame's body identity, MIR
and starting PC. Then use `miri_program` to inspect one layer of the VC.
Forward substitution is restricted to rank-decreasing successors. Other
successors use the same shared condition. A successful call selects the
equation for the frame actually entered. The call's advertised MIR target
describes its return continuation.

`BodyVCGen.generateProgram` exposes the graph and the equations for each known
body identity. To prove a cyclic VC with predicates indexed by body identity
and location, use `miri_program_with atPC, fallback` after `vcgen`. It generates
entry, exit, equation-preservation and residual obligations. The residual
obligation uses the canonical step rule for states outside the compiled tables.
The example checks these proof interfaces with arbitrary postconditions and
symbolic machine hooks. A program safety theorem still needs to discharge
the resulting obligations for the chosen hooks and admitted inputs.

`BodyVCGen.ProgramNoUB` supplies the interpreter's diagnostic UB predicate.
It permits non-UB errors such as resource cutoffs as finite stops. An explicit
triple can constrain success and error outcomes. Both forms are partial
correctness conditions and permit infinite execution.

Use `BodyVCGen.prepareRoot` to enter the selected imported root through the
interpreter's root-call setup. Supply the initialized machine, typed immediate
arguments, and an allocated return destination for a non-unit result.
`preparedProgramPre` includes preparation and passes the resulting state into
the generated program VC. [Replay.lean](Replay.lean) specializes this path to
`count_up(1, 3, true)` and shows how checked deterministic replays establish a
matching success post, reject an impossible success post, and witness UB
under a policy that permits the replay's choices. The replay budget limits
certificate search. Whole-body semantics still quantify over every permitted
finite exit.

```bash
flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  Miri.Frontend.ImportMIR MiriTests.Verification.WholeBodyReplay
lake env lean -j1 examples/body_vcgen/Replay.lean
```

[runtime.rs](runtime.rs) exercises the same certificate adapter against the
native source runner's initialized machine and canonical call resolver. It
imports a loop with a local call and runs it with Tree Borrows enabled. The
positive run accepts a scope exit and rejects a stopped outcome. The negative
run reaches UB at a typed null-pointer dereference and rejects the no-UB VC.
The script compares the runner's ordinary terminal result with the result
reported when certificate checking is enabled and keeps both logs.

With the pinned exporter and MIR-enabled sysroot installed, run:

```bash
flock --no-fork /tmp/lean-miri-lake-build.lock lake build native_runner
bash tools/check-body-replay.sh
```

The source runner initializes a fixed runtime world and supplies a `Unit`
choice at the core boundary. [ProveReplayGenerated.lean](ProveReplayGenerated.lean)
checks that the certificate's verdict is equivalent to the saved safety VC
with every core choice admitted in that world. The Rust inputs, seed and host
state are fixed by the runtime run.

```bash
tools/body-vc safety scratch/body-replay-regression/positive.json --root miri_start \
  --output scratch/runtime-vc/Generated.lean
lean_path="$(lake env printenv LEAN_PATH)"
LEAN_PATH="$PWD/scratch/runtime-vc:$lean_path" \
  lean --root="$PWD/scratch/runtime-vc" -o scratch/runtime-vc/Generated.olean \
    scratch/runtime-vc/Generated.lean
time env LEAN_PATH="$PWD/scratch/runtime-vc:$lean_path" \
  lean -j1 examples/body_vcgen/ProveReplayGenerated.lean
```

To refresh the compiler input, build the pinned exporter and run the following
command with the pinned Miri sysroot.

```bash
bash tools/export-mir.sh --output examples/body_vcgen/input.json \
  --root count_up -- examples/body_vcgen/control.rs \
  --crate-type=lib --crate-name=body_vcgen
```

## Check the VC emitted from the bare Rust source

The `count_up` example also works with the command-line generator. A
separate harness calls the unchanged function with both values of the
branch condition. The runner checks the exact emitted MIR against the
prepared callee frame before replaying its certificate.

```bash
mkdir -p scratch/count-up-source-exact
tools/body-vc safety examples/body_vcgen/control.rs \
  --output scratch/count-up-source-exact/CountUp.lean
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output scratch/count-up-source-exact/harness.json \
  --root miri_start --root control::count_up -- \
  examples/body_vcgen/control-runtime.rs \
  --crate-type=bin --crate-name count_up_replay -Cpanic=abort -Zmir-opt-level=0
.lake/build/bin/native_runner scratch/count-up-source-exact/harness.json \
  --ui-source examples/body_vcgen/control-runtime.rs \
  --ui-flags '["-Zmiri-tree-borrows"]' --profile \
  --check-body-vc-input scratch/count-up-source-exact/CountUp.mir.json 0
```

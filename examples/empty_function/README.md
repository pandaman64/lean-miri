# Empty-function UB freedom

`ActualNoUBFinal.target` proves `TotalCallGoal.Target s`: actual initialization
and every finite execution prefix of `pub fn empty_function() {}` report no undefined
behavior while this call remains in scope. `ActualNoUBFinal.noUB` is the
per-caller theorem; neither entry point takes remaining family or stage proofs.

The target admits exactly the following premises:

```lean
(Nonempty (Metadata s)) → Profile s →
  ∀ p, RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p) →
    CallLevelNoUB.NoUB s p
```

Allocator/generator coherence for projected backing is required only when
its raw runtime and enabled-source counters are active. Zero/wrapped counters
and exhaustion flags remain admitted; when allocation is attempted, its
actual checked error is observed. Reserving the final MAX ID itself is also admitted.
`AllocatorActive` is a guard on coherence fields, not a caller premise, and
the allocator implementation is unchanged.

There is no numeric resource reserve, supported-choice/`ChoiceFits` condition,
successful-return premise, or remaining family/stage proof in this target.
Both actual initialization errors and actual in-call errors are observed with
their failed states. Checked non-UB stops, including resource exhaustion, are
allowed. This is a UB-freedom result; it does not promise normal return for
all resource supplies. The normal-return/NoErrors and eleven-clause
preservation theorems are conditional intermediate results.

`CurrentInputDraft` describes the admitted raw machine states: caller/local
bindings and representations, pointer/source metadata, live allocation and
Tree Borrows coherence, address/ID tables, and the runtime dictionaries used
by the actual call. Other caller state is arbitrary within those premises.
The agreed pure compiler metadata properties are assumed as `Metadata`, not
introduced as Lean axioms. A theorem mapping every Rust-valid caller state to
this explicit domain has not been proved. Compiler/exporter correctness and
correspondence between the interpreter and Rust remain trusted boundaries.

`Profile` and `RuntimeProfile` retain the exact switches in
`Specification.lean`: fixed scheduling, absent race clocks/weak backend,
shallow validation, and the specified debug, retag, and control configuration.
The observer ends after returning to the caller; arbitrary scheduler
interleavings and later caller execution are outside this theorem.

The fixed configuration keeps allocation-backtrace diagnostics disabled.
`Configuration.proofOptions` overrides only the new `collectLeakBacktraces`
field; every pre-existing option remains a caller input with its existing
profile constraints. Every diagnostic-off option record embeds unchanged
(`proofOptions_of_disabled`). Raw option records requesting diagnostic collection
are normalized to this explicit profile; the theorem does not establish safety
or normal completion for the opt-in collector. The Rust source, concrete MIR and
final target's caller premises are unchanged; the pinned compiler input uses the
source-material format.

Miri source additions expose proof-only APIs; the interpreter implementation
is unchanged by this example. The fixed Rust/input hashes are recorded in
`SHA256SUMS`. The schema-16 input contains the concrete body, evaluated constants
and finite type/declaration, ABI and allocation-identity material. It contains no
layout or FnAbi answer tables; the production Lean providers compute those values.
Generic function MIR is absent. Metadata premises remain explicit pure-query
facts and span bounds. The proof-only reflected MIR block is `noncomputable` to avoid
a Lean native-code-generation boxing panic; no native executable validation
of that block is claimed.

Run `bash tools/check-empty-function.sh` to check the actual fixture's source
ABI/layout/Freeze/inhabited/validity providers, then compile the committed root
and its source closure, check the final target type, and audit imported EmptyFunction/Miri declarations
(including private/generated declarations) for transitive axioms. Only
`propext`, `Quot.sound`, and `Classical.choice` are permitted. The executable
provider assertions are finite checks; they neither supply theorem premises nor
establish the full caller domain or general compiler-query correctness.
See [STATUS.md](../../STATUS.md#empty-function-caller-domain-transport).

## Continuous integration

[The proof workflow](../../.github/workflows/empty-function-proof.yml) runs the full
`Check` closure on `main` pushes and by manual dispatch. It checks fixed-input hashes and transitive axioms. Only the
Lean toolchain and library build artifacts are cached; example proofs are
checked again on every run. Diagnostic logs are retained as workflow artifacts.

## Generated body verification condition

[GeneratedBodySafety.lean](GeneratedBodySafety.lean) connects the same
Rust body to `BodyVCGen.generateProgram`.
`EmptyFunction.GeneratedBodySafety.localImmediate` proves the generated
no-UB condition for every admitted caller with a local immediate return
destination, including projected destinations. It checks initialization
errors and every permitted in-call execution. The proof uses the canonical
initializer to identify the entry frame and actual call depth.

```bash
bash tools/check-empty-function.sh GeneratedBodySafety
```

To emit the saved VC and check the proof that uses its named condition, run
these commands from the repository root. Set `proof_deps` to the frozen
output directory printed as `Frozen … roots/dependencies` above.

```bash
tools/body-vc safety examples/empty_function/empty_function.rs \
  --output scratch/empty-function-vc/Generated.lean
lean_path="$(lake env printenv LEAN_PATH)"
LEAN_PATH="$PWD/scratch/empty-function-vc:$proof_deps:$lean_path" \
  lean --root="$PWD/scratch/empty-function-vc" -o scratch/empty-function-vc/Generated.olean \
    scratch/empty-function-vc/Generated.lean
time env LEAN_PATH="$PWD/scratch/empty-function-vc:$proof_deps:$lean_path" \
  lean -j1 examples/empty_function/ProveGenerated.lean
```

For a concrete call under the source runner's initialized world,
[runtime.rs](runtime.rs) calls the same Rust function. Admit every typed core
choice in that fixed world and time its checked replay separately.

```bash
mkdir -p scratch/empty-runtime
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output scratch/empty-runtime/input.json --root miri_start --root fixture::empty_function -- \
  examples/empty_function/runtime.rs --crate-type=bin --crate-name small_root \
  -C debug-assertions=no -C overflow-checks=no -C panic=abort -Zmir-opt-level=0
tools/body-vc safety scratch/empty-runtime/input.json --root fixture::empty_function \
  --output scratch/empty-runtime/Generated.lean
.lake/build/bin/native_runner scratch/empty-runtime/Generated.mir.json \
  --ui-source examples/empty_function/runtime.rs --ui-flags '["-Zmiri-tree-borrows"]' \
  --profile --check-body-vc-root 1
```

To check the standalone VC from the bare Rust file at the same prepared
entry, pass its emitted MIR to the runner. The standalone export has its
own root index, zero.

```bash
.lake/build/bin/native_runner scratch/empty-runtime/input.json \
  --ui-source examples/empty_function/runtime.rs --ui-flags '["-Zmiri-tree-borrows"]' \
  --profile --check-body-vc-input scratch/empty-function-vc/Generated.mir.json 0
```

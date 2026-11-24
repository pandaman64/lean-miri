# Generated safety VC for duplicate_prefix

The Rust function in [duplicate_prefix.rs](duplicate_prefix.rs) is the
archived implementation using `copy_nonoverlapping`. The CLI generates a
Lean safety VC from this standalone Rust file. The stock runner uses the
separate [runtime harness](runtime.rs) to prepare actual call states with
Tree Borrows enabled.

With the pinned MIR-enabled sysroot in `MIRI_SYSROOT`, build `native_runner`,
`Miri.Verification.TreeRangeAccess`, `Miri.Verification.MutableTypedRetag`,
and the Lean libraries. Then run the check.

```sh
tools/check-duplicate-prefix-vc.sh
```

The script typechecks [VerifyGenerated.lean](VerifyGenerated.lean) against
the emitted Lean file and checks the symbolic components below.
The runner loads the saved standalone MIR and the same root with the same
loader as the generated Lean file. Each certificate checks that the standalone
root's lowered body and identity equal those of the live prepared frame.
A missing certificate fails the test. The proofs cover these seven entries
under the concrete runtime input tape and every typed core choice (`Unit`).
The profile reports certificate replay time separately from generation and
Lean typechecking.

| Slice length | Count | Result |
| --- | --- | --- |
| 8 | 0 | Accept |
| 8 | 2 | Copy two bytes |
| 8 | 4 | Copy four bytes |
| 8 | 5 | Reject |
| 8 | `usize::MAX` | Reject |
| 0 | 0 | Accept |
| 0 | 1 | Reject |

The harness independently checks each return value and all eight bytes after
each nonempty call. Certificate search has a finite budget. A successful
search yields a proof of `GeneratedBodySafety.requiredAt` for that entry,
using the exact finite-outcome semantics of the generated VC.

### Mutable slice call boundary

[The adversarial caller](runtime_adversarial.rs) uses unsafe raw-pointer
dereferences to create a mutable slice while its enclosing frame still holds
a protected shared slice over the same two bytes. The borrow checker rejects
the analogous overlap constructed with ordinary shared and mutable borrows.
The replay enters the same typed `duplicate_prefix` body with either count.
Count zero returns normally. Count one reaches the copy and fails on the
destination byte at offset one, where the write would disable a protected
Frozen tag. The script checks both outcomes against the standalone generated
safety condition.

[VerifyGenerated.lean](VerifyGenerated.lean) turns a rejected replay
certificate into a proof of the negated emitted condition at that prepared
frame. Its permission lemma explains why successful entry is weaker than
write authority. When implicit writes are disabled, the mutable slice retag
requires a read and installs a protected reservation. A reusable mutable
slice contract therefore needs read and write authority over the referent in
its calling context, including compatibility with the permissions and active
protectors at the bytes it can touch. Layout, initialization, and the slice
descriptor can all agree while that authority differs.

### Symbolic proof components

[PreparedArguments.lean](PreparedArguments.lean) identifies argument slots
and branch instructions in the emitted MIR. It also checks the current
compiler helper for the language UB guard and the switch on its result.
[SymbolicCopyAccess.lean](SymbolicCopyAccess.lean) proves copy access through
the canonical diagnostic, race, Tree Borrows, synchronization and allocation
cache transitions, given their local premises. Its range proof extends
authorized location slots to a complete access across the specified range.
[ZeroProtector.lean](ZeroProtector.lean) proves release of a dormant,
unexposed protector and the corresponding allocation and ownership-ledger
updates. [ZeroTail.lean](ZeroTail.lean) verifies the three steps from the
prepared zero-branch cleanup position through the jump to the return slot.
The whole-function proof still needs to establish the prepared ownership
states from lawful call entry and compose the helper and return paths.

[LanguageGuardStack.lean](LanguageGuardStack.lean) checks the actual helper's
false-result assignment, local destination copy, and canonical stack return
under its explicit frame and call-policy premises.

[LanguageGuardCall.lean](LanguageGuardCall.lean) connects the actual
resolved helper to canonical call entry. [LanguageGuardValidity.lean](LanguageGuardValidity.lean)
handles the guard's Boolean validity check.
[LanguageGuardAssignment.lean](LanguageGuardAssignment.lean) proves the
constant operand and uncached place evaluation for the guard assignment.
[NestedGuardDriver.lean](NestedGuardDriver.lean) links the canonical step
to the checked before-terminator path under fixed scheduling.
[ZeroBoolean.lean](ZeroBoolean.lean)
checks the selected zero-branch write and read of the actual return value.
[ZeroAssignment.lean](ZeroAssignment.lean) links the assignment to the
canonical step. [ZeroNodes.lean](ZeroNodes.lean) checks the generated
assignment and return instructions. [ZeroReturnDriver.lean](ZeroReturnDriver.lean)
connects the selected return to its before-terminator step.
[ZeroReturn.lean](ZeroReturn.lean) checks writing back to the caller and
resuming its continuation, given the exact stack pop.

[SourceDomain.lean](SourceDomain.lean) states bytewise ownership and
forest coherence for a prepared concrete slice. [MutableSliceRights.lean](MutableSliceRights.lean)
uses those facts to preserve the local and foreign permissions of a fresh
mutable child, given the concrete retag footprint.
[MutableSliceRetag.lean](MutableSliceRetag.lean) derives the child attachment
from the actual Tree Borrows insertion.

[ScopedSafetyTransfer.lean](ScopedSafetyTransfer.lean) connects separately
proved scoped error safety and successful root preparation to the generated
VC at the entry state.

[CanonicalCallDomain.lean](CanonicalCallDomain.lean) specifies the prepared
frame, caller storage, and Tree Borrows rights for the stated all-count goal.
[CanonicalSourceControl.lean](CanonicalSourceControl.lean) adds the pinned
compiler's relevance and local layout cache conditions.
[CanonicalCallRelease.lean](CanonicalCallRelease.lean) derives the release
plan for an empty argument's dormant protector, and
[GeneralPhysicalRelease.lean](GeneralPhysicalRelease.lean) derives the
physical return-slot release from bytewise ownership. These release lemmas
supply individual cases of the all-count argument.

### Safety for both prepared return destinations

[VerifyCanonicalSafety.lean](VerifyCanonicalSafety.lean) proves
`DuplicatePrefix.CanonicalCallDomain.safetyForPreparedCall` for all `UInt64`
counts and either admitted Boolean return destination. For a nonempty
initialized slice it uses `CopySourceResources` for the source allocation.
The permission proof covers both appended and recycled Tree Borrows keys.
For a nonzero count on an empty slice it covers a non-null integer-address
pointer without provenance. The proof uses the pinned compiler profile,
resource budgets, and Shallow fixed-scheduling configuration in the
theorem statement. It proves the exact generated obligation without
requiring a trace or execution result.

Use `--client VerifyCanonicalSafety` in the checker command below to
rebuild this proof. The unresolved wildcard and backed empty cases with
nonzero counts have separate proof obligations.

### Zero count with either return destination

[VerifyZeroPhysicalCanonical.lean](VerifyZeroPhysicalCanonical.lean) proves
`DuplicatePrefix.CanonicalCallDomain.zeroCount` for every admitted slice
length, with either a root physical Boolean destination or a nested cached
Boolean destination. The proof starts from the prepared caller rights and
uses the actual protector release and return. It also needs the pinned
compiler control profile and the validation budget in the theorem statement.
Use `--client VerifyZeroPhysicalCanonical` in the checker command below to
rebuild this proof.

### All counts for a nonempty slice with a cached Boolean return

[VerifyAllCountCanonical.lean](VerifyAllCountCanonical.lean) proves
`DuplicatePrefix.RootZeroShallowReturn.allCountsFromCanonicalAdmitted`.
For any `UInt64` count, it discharges the generated safety condition from a
prepared nonempty initialized slice and a nested cached Boolean destination.
The theorem also requires the pinned compiler control profile, room for
four fresh tags and their occupied or recycled key slots, and the checked Shallow,
fixed-scheduling, no-GC, no-race configuration. The proof derives the actual
zero-count, rejecting, or copying execution and its return from those
initial conditions.

Generate the standalone obligation and check the proof closure with the
pinned Lean executable on `PATH` and the repository library built.

```sh
out="$PWD/scratch/duplicate-prefix-vcgen"
mkdir -p "$out"
tools/body-vc safety examples/duplicate_prefix_vcgen/duplicate_prefix.rs \
  --output "$out/Representative.lean" --no-check
python3 tools/check-duplicate-prefix-archive.py "$out/Representative.mir.json" \
  --generated "$out/Representative.lean" --client VerifyAllCountCanonical \
  --output "$PWD/scratch/duplicate-prefix-all-count"
```

### Recheck migrated archive components

The archive overlay imports the current standalone MIR and rebuilds its proof
modules against the current interpreter. It pins the old source revision and
applies [ArchiveMigration.patch](ArchiveMigration.patch) only in a fresh
output directory. Its default target set covers the typed compiler metadata,
the root's exact ABI and declaration spans, canonical frame initialization
queries, and selected allocation, retagging and copy bridges. The optional
client target above recompiles the proof for nonempty slices and a cached
Boolean return.

```sh
git fetch origin 7950c01b18013969c360df535b8b888dd6181dff
python3 tools/check-duplicate-prefix-archive.py \
  scratch/duplicate-prefix-vcgen/Representative.mir.json \
  --output scratch/duplicate-prefix-archive-check
```

The checker uses prebuilt Lean library artifacts. Its logs and rebuilt
proofs stay in the output directory. The active protector release and
canonical stack-pop composition are included in the default targets.
[ZeroReturnOwnership.lean](ZeroReturnOwnership.lean) uses that composition
to check normal return from the owned protector profile.
The optional `ActiveStackReleaseExclusive` target checks protector release
and stack pop while preserving the raw-pointer access rights described by
its ownership premises.

```sh
LEAN_PATH="$PWD/scratch/duplicate-prefix-vcgen:$PWD/scratch/duplicate-prefix-archive-check:$PWD/.lake/build/lib/lean" \
  lean -j1 examples/duplicate_prefix_vcgen/ZeroReturnOwnership.lean
```

`--target ArchiveTraceToVC` checks the bridge from a separately proved
returning trace to the current VC.
`--target RootZeroCompletePrefix` checks the current zero-count root from
entry through the selected `Return` under its stated canonical Shallow machine
premises, with any surrounding frame array.
`--target RootZeroComplete` checks the whole zero-count root call with a
physical Boolean destination and the stated release profile, down to the
actual memory update and root stop. [RootZeroPhysicalVC.lean](RootZeroPhysicalVC.lean)
applies the checked physical-root proof to the exact emitted `requiredAt`
for every allowed `Unit` choice policy, under the same machine premises.

```sh
out="$PWD/scratch/duplicate-prefix-vcgen"
archive="$PWD/scratch/duplicate-prefix-physical-zero"
python3 tools/check-duplicate-prefix-archive.py "$out/Representative.mir.json" \
  --output "$archive" --target RootZeroComplete \
  --target ArchiveCatalogRoot --target ArchiveTraceToVC
LEAN_PATH="$out:$archive:$PWD/.lake/build/lib/lean" \
  lean -j1 examples/duplicate_prefix_vcgen/RootZeroPhysicalVC.lean
```

[VerifyZeroGenerated.lean](VerifyZeroGenerated.lean) proves the emitted condition
for a nested zero-count call with an admitted local Boolean destination. Its
trace includes actual active protector release, the caller's Boolean result
update, and the saved continuation. The theorem states the Shallow machine,
frame, and ownership premises.

```sh
out="$PWD/scratch/duplicate-prefix-vcgen"
archive="$PWD/scratch/duplicate-prefix-nested-zero"
python3 tools/check-duplicate-prefix-archive.py "$out/Representative.mir.json" \
  --output "$archive" --target RootZeroCompletePrefix \
  --target ActiveStackRelease --target ArchiveCatalogRoot --target ArchiveTraceToVC \
  --target RootRejectedPrefix
export LEAN_PATH="$out:$archive:$PWD/.lake/build/lib/lean"
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/ReturnPreOfEffects.olean" examples/duplicate_prefix_vcgen/ReturnPreOfEffects.lean
lean -j1 --root=examples/duplicate_prefix_vcgen \
  -o "$out/RootZeroShallowReturn.olean" examples/duplicate_prefix_vcgen/RootZeroShallowReturn.lean
lean -j1 examples/duplicate_prefix_vcgen/VerifyZeroGenerated.lean
lean -j1 examples/duplicate_prefix_vcgen/RootRejectedAfterLen.lean
```

`--target RootLenPrefix` checks the root's nonzero-count path from basic
block 2 to the shared-slice length preparation, preserving the live pointer
and machine state. `--target RootCurrentDecision` checks the downstream
comparison and branch from its prepared live length and count locals.
`--target RootMutPreparation` checks the statements that lead to mutable
slice preparation on the accepted path. `AsMutRootRoundtrip` checks the
actual root call to `as_mut_ptr` and return to the caller's pointer slot,
deriving the retained raw-pointer rights under its structural premises. `--target PtrMetadataExecution`
checks the retained pointer-metadata helper's local copy and metadata write.
`SliceLenPrefix`, `PtrMetadataComplete`, and `LenReturn` separately check
the length helper's preparation, actual metadata result, and return under
their stated premises. `SliceLenCompleteCurrent` connects the nested
metadata call and exact length return, deriving the active protector release
from its independent ownership premises.

`--target RootRejectedPrefix` checks the too-large-count path after the
length call, including the division guard, comparison, false result, and
selection of `Return`, for any surrounding frames under its stated premises.
[RootRejectedAfterLen.lean](RootRejectedAfterLen.lean) continues through
the active protector release and writes `false` to the caller's local
Boolean destination.
`RejectionFromEnteredLength.lean` starts at the entered length helper and
checks length, protector release, and the root rejection return.
`VerifyRejectionGenerated.lean` links a checked root-to-post-length trace
to the emitted safety VC.

[RootRejectionPrepared.lean](RootRejectionPrepared.lean) proves the emitted VC
from the prepared entry for a nonempty slice and every count above half its
length, under the stated nested cached Boolean destination and dense
Tree Borrows tag-table conditions. Its trace includes the shared reborrow,
actual length call, false return, and protector release.
[VerifyRejectedCanonical.lean](VerifyRejectedCanonical.lean) applies that
proof to the canonical profile with the same supplements.

After generating the client artifacts as above, use a fresh overlay to check
this complete rejection branch.

```sh
out="$PWD/scratch/duplicate-prefix-vcgen"
archive="$PWD/scratch/duplicate-prefix-rejection"
LEAN_PATH="$out" python3 tools/check-duplicate-prefix-archive.py "$out/Representative.mir.json" \
  --output "$archive" --target RootNonzeroShared --target GeneratedSafetyOfTrace \
  --target LenFrameGrant --target LenRuntimeProfile --target TightParentDepth \
  --target SliceLenCompleteCurrent --target ReleaseFromHolderRights \
  --target RootZeroCompletePrefix --target RootRejectedPrefix --target ActiveStackRelease
export LEAN_PATH="$out:$archive:$PWD/.lake/build/lib/lean"
source_dir=examples/duplicate_prefix_vcgen
for module in ReturnPreOfEffects RootZeroShallowReturn RootRejectedAfterLen \
    RejectionEntryAfterLength RetainedRootAfterLength RejectionFromEnteredLength \
    ProtectedTagFresh RejectionFromLenCall RootRejectionPrepared CanonicalCallDomain; do
  lean -j1 --root="$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean"
done
lean -j1 "$source_dir/VerifyRejectedCanonical.lean"
```

The `EmptyIntegerLength` archive target checks the actual shared-reference
assignment, protected argument-validation callback, nested metadata call, and
length return for a non-null integer-address empty slice. The length is zero.
The two retags increase the tag counter while leaving memory and the global
protector ledger intact.

[VerifyEmptyIntegerCanonical.lean](VerifyEmptyIntegerCanonical.lean) closes
the emitted VC for these empty slices at every nonzero count with a cached
Boolean caller. The proof uses the canonical preparation and compiler
profiles. It checks the full path from the root guard through the real length
call, rejection, and actual false return. The empty argument contributes no
protector row. A concrete-provenance empty slice and an unresolved wildcard
use different retag and release paths.

```sh
out="$PWD/scratch/duplicate-prefix-vcgen"
archive="$PWD/scratch/duplicate-prefix-empty-integer"
LEAN_PATH="$out" python3 tools/check-duplicate-prefix-archive.py "$out/Representative.mir.json" \
  --output "$archive" --target EmptyIntegerPrefix --target RootLocalBoolReturn \
  --target ArchiveCatalogRoot --target GeneratedSafetyOfTrace \
  --target InitMaskCopy --target ProvenanceCopy
export LEAN_PATH="$out:$archive:$PWD/.lake/build/lib/lean"
source_dir=examples/duplicate_prefix_vcgen
for module in CanonicalCallDomain CanonicalSourceControl CanonicalEntryFacts; do
  lean -j1 --root="$source_dir" -o "$out/$module.olean" "$source_dir/$module.lean"
done
lean -j1 "$source_dir/VerifyEmptyIntegerCanonical.lean"
```

The positive-path archive targets `AsMutToCopyCall`, `RootPositiveRootSuffix`,
and `RootPositiveReleaseAfterCopy` check the actual helper calls, the bounded
copy, the Boolean result, and the post-copy release from their respective
prepared states. `RootPositiveSuccessOfPlan` checks the physical terminal
Return with the resulting release plan and its stated destination profile.

The optional `RetagFrozenChild` target checks actual child insertion and
the resulting range and permission frame under its concrete fresh-tag premises.
The `ConcreteFrozenReborrow` and `ExclusiveTypedRetag` targets connect the
concrete forest rights with the actual typed reborrow and final location state.
`TypedSharedReborrow` checks the actual shared reborrow under its structural
and pointer premises. `RootTwoPhaseComplete` checks the mutable reference
assignment at the selected root instruction and its resulting permissions.
`ProtectedSharedReborrow` derives the coherent readable region from actual
shared FnEntry retag under its stated initialized-region and pointer premises.
`RootSharedComplete` checks the current root's shared-slice assignment to its
actual length-call argument slot, retaining exact heap state and read rights.
`RootLenCurrentCall` checks the next root step, including the actual
protected receiver installation and entry into the length helper.

After the standalone example script builds `SourceDomain.olean`, the
optional `ExclusiveCopyStep` target verifies the actual positive copy
instruction and its byte update from the prepared tree permissions.
`--target CopyHelperCurrentCall` checks the current positive copy-helper
path from basic block 7 through the actual return to the caller, with
the stated machine, frame and Tree Borrows premises.
`--target ExclusiveCopyCurrentCall` derives the needed Tree Borrows access
from the prepared exclusive region and checks the same return and byte update.

The `LanguageGuardCurrent*` archive modules check the retained implementation
of the language-UB check helper in individual steps.
`--target PointerAddCurrentGuardTail` checks the selected current pointer-add
guard suffix. These targets use the standalone example's prebuilt local imports.
`--target PointerAddCurrentComplete` verifies the retained pointer-add helper
from its prepared basic block 6 through the exact caller return and pointer
result. `PointerAddGuardBoundary` connects a separately established guard
prefix to that proof. `RootCurrentCopyPreparation` and `CopyRootEntry`
check the root around pointer addition and entry into the copy helper;
`RootPositiveSuccessComplete` checks the positive root suffix from its
prepared return state with a physical Boolean destination.

```sh
LEAN_PATH="$PWD/scratch/duplicate-prefix-vcgen" \
  python3 tools/check-duplicate-prefix-archive.py \
    scratch/duplicate-prefix-vcgen/Representative.mir.json \
    --output scratch/duplicate-prefix-copy-step --target ExclusiveCopyStep
```

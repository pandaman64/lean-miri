#!/usr/bin/env python3
"""Recheck the verified portions of the duplicate-prefix archive on current MIR."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

REPO = Path(__file__).resolve().parent.parent
ARCHIVE = "7950c01b18013969c360df535b8b888dd6181dff"
ARCHIVE_DIR = "examples/duplicate_prefix"
RUSTC = "8eb778d04094d3af4b26580cab327e0413eb1e02"
CHECKED = (
    "Program", "Reflection", "Prepared", "RootBody", "AllocationCopy",
    "PreparedContracts", "CopyPreconditions", "MemoryCopyBridge",
    "OffsetAllocationCopy", "RetagPointerChecks", "BorrowRangeAccess",
    "BorrowCopyRanges", "BorrowRelease", "ExistingPartition", "ActiveStackRelease",
    "RootCompilerCore", "RootCompilerFacts", "SpanFacts", "CallEntryFacts",
)
CLIENT = REPO / "examples/duplicate_prefix_vcgen"
PATCH = CLIENT / "ArchiveMigration.patch"
LOCAL = {
    "ActiveReleaseOwned", "ActiveReleaseRange", "ActiveStackRelease", "RootCompilerCore",
    "ArchiveForestProjection", "ExclusiveConcreteRange", "ExclusiveCopyRanges", "ExclusiveCopyStep",
    "ArchiveTraceToVC", "RootLocalChecks", "HelperAbiLayouts", "RetagRangeFrame", "RetagLocationFrame", "RetagFrozenChild",
    "ZeroImmediateFacts",
    "CompilerFrameLayout",
    "CopyHelperCurrentCall",
    "CopyHelperCurrentExit",
    "CopyHelperResult",
    "LocationPointeeLayout",
    "PointerAddCurrentFacts",
    "PointerAddCurrentReturn",
    "RootThinPointerCopy",
    "RootThinPointerWrite",
    "ArchiveCatalogRoot",
    "ConcreteFrozenReborrow",
    "ExclusiveCopyCurrentCall",
    "ExclusiveFrozenEntry",
    "ExclusiveNormalRights",
    "ExclusiveRetagFrame",
    "ExclusiveRetagRead",
    "ExclusiveTypedRetag",
    "RetagKeyFrame",
    "VacantRetagRead",
    "LanguageGuardCurrentControl",
    "LanguageGuardCurrentFacts",
    "LanguageGuardCurrentFalse",
    "LanguageGuardCurrentReturn",
    "LanguageGuardCurrentRuntime",
    "LanguageGuardCurrentStorage",
    "LanguageGuardCurrentSwitch",
    "LanguageGuardCurrentUnit",
    "PointerAddCurrentGuardTail",
    "ActualCurrentSlice",
    "RootCurrentDecision",
    "AsMutPtrFacts",
    "ConcreteSharedReborrow",
    "CurrentMutableRetag",
    "CurrentReferenceCore",
    "CurrentReferenceLocalValidity",
    "CurrentReferenceLocalWrite",
    "CurrentReferenceMetadata",
    "CurrentReferenceVisitor",
    "CurrentSlicePlace",
    "CurrentTwoPhaseStructural",
    "ExclusiveTwoPhaseRetag",
    "RetagGraphFrame",
    "RetagSharedChild",
    "RootMutableStep",
    "RootSharedRef",
    "RootSharedStep",
    "RootTwoPhaseComplete",
    "TypedSharedReborrow",
    "ActiveReleaseExclusive",
    "ActiveStackReleaseExclusive",
    "RetagReleaseRights",
    "ActualOffsetCore",
    "PointerAddCurrentCleanup",
    "PointerAddCurrentComplete",
    "PointerAddCurrentExit",
    "PointerAddCurrentOffset",
    "PointerAddCurrentSetup",
    "PointerAddCurrentStatements",
    "PointerAddCurrentStorage",
    "PointerAddGuardBoundary",
    "PointerOffsetRvalueCore",
    "InheritedSharedRights",
    "NormalAccessRights",
    "ProtectedSharedReborrow",
    "ReadAccessRange",
    "SharedReadOwnership",
    "SharedReborrowContinuity",
    "RetagReleaseFootprint",
    "LenPlanOfOwnership",
    "SliceLenCompleteCurrent",
    "CurrentSharedRetag",
    "RootSharedComplete",
    "SharedHolderAttach",
    "SharedHolderRead",
    "SharedReleaseRange",
    "CurrentLenFnEntry",
    "ReleaseFromHolderRights",
    "CopyCurrentGuardSuffix",
    "CopyCurrentGuardSwitch",
    "CopyCurrentGuardTail",
    "RootCurrentAddCall",
    "RootCurrentAddPipeline",
    "RootCurrentCopyPreparation",
    "RootPositiveSuccessComplete",
    "AsMutCurrentArgument",
    "AsMutCurrentCall",
    "AsMutCurrentEntry",
    "AsMutCurrentInstall",
    "AsMutDispatchExact",
    "AsMutPassArgument",
    "AsMutPreparedEntry",
    "AsMutReturnExclusive",
    "AsMutReturnStep",
    "AsMutRootRoundtrip",
    "AsMutRootStep",
    "AsMutRoundtrip",
    "CurrentAsMutFnEntry",
    "CurrentAsMutStrong",
    "FrameRootRelevance",
    "RootNonzeroEntry",
    "CurrentLenArgument",
    "CurrentLenEntry",
    "RootLenCurrentCall",
    "LenEntryControl",
    "LenFrameGrant",
    "LenRuntimeProfile",
    "TightParentDepth",
    "EmptyEntryReferenceValidator",
    "EmptyIntegerBorrow",
    "EmptyIntegerLength",
    "EmptyIntegerValidity",
    "EmptyLenArgumentCopy",
    "EmptyLenCallReturn",
    "EmptyLenCallStep",
    "EmptyLenEntry",
    "EmptyLenEntryShape",
    "EmptyLenEntryValidity",
    "EmptyLenInstall",
    "EmptyLenPushFacts",
    "EmptyLenUncachedCall",
    "EmptyLocalReferenceValidator",
    "EmptyLocalReferenceWrite",
    "EmptyReferenceAllocation",
    "EmptyReferenceContext",
    "EmptyReferenceFactory",
    "EmptyReferenceFacts",
    "EmptyReferenceInfo",
    "EmptyReferenceMetadata",
    "EmptyReferenceRvalue",
    "EmptyReferenceSteps",
    "EmptyReferenceValidity",
    "EmptyReferenceWrite",
    "EmptyRootLenCall",
    "EmptySharedReference",
    "SliceLenExtended",
    "GeneratedSafetyOfTrace",
    "RootNonzeroShared",
    "UnprotectedSharedRights",
    "AsMutPreparedAddFrame",
    "AsMutToCopyCall",
    "CopyHolderRights",
    "CopyOwnershipTransport",
    "CopyRootCurrentGuardBody",
    "CopyRootCurrentGuardReach",
    "CopyRootCurrentReadyFacts",
    "CopyRootPositiveRoundtrip",
    "CopyRootPositiveRoundtripExact",
    "InitMaskReadComplete",
    "InitializedRegionPrefix",
    "LanguageGuardCurrentABI",
    "LanguageGuardCurrentLeafTrace",
    "LanguageGuardCurrentParentExit",
    "LanguageGuardCurrentParentPrelude",
    "LanguageGuardCurrentParentTail",
    "LanguageGuardCurrentRoundtrip",
    "LanguageGuardEntryAt",
    "PointerAddCurrentFullGuard",
    "PointerAddCurrentGuardSuffix",
    "PointerAddGuardEntryCurrent",
    "PointerAddLanguageGuardFacts",
    "PointerAddLanguageGuardStep",
    "PointerAddLanguageGuardStorage",
    "PointerAddLanguageGuardUncached",
    "RootCopiedHolderAuthorization",
    "RootCopiedHolderRelease",
    "RootCurrentAddCallExact",
    "RootCurrentAddInitial",
    "RootCurrentAddPipelineExact",
    "RootCurrentCopyReady",
    "RootCurrentCopyReadyExact",
    "RootGuardRelevance",
    "RootPhysicalReturnOfPlan",
    "RootPositiveAfterAsMut",
    "RootPositiveCopyFromBB7",
    "RootPositiveReleaseAfterCopy",
    "RootPositiveReturnContinuation",
    "RootPositiveRootSuffix",
    "RootPositiveSuccessOfPlan",
    "RootPositiveTwoRelease",
    "RuntimeZeroCurrentCallStep",
    "RuntimeZeroCurrentInstalled",
    "RuntimeZeroCurrentRoundtrip",
    "RuntimeZeroCurrentStep",
    "RuntimeZeroCurrentUncached",
    "EmptyIntegerPrefix",
    "RootLocalBoolReturn",
    "AsMutHolderScope",
    "FrozenReborrowInputs",
    "FrozenReborrowScope",
    "LenExitFacts",
    "PositiveRetagResources",
    "RawHolderScope",
    "RetagCapacityFrame",
    "RetagInsertionCapacity",
    "RetagStageImage",
    "RetagSuccessorCapacity",
    "RootAcceptedAfterLen",
    "RootAcceptedAsMut",
    "RootAcceptedPreparation",
    "RootAsMutReservation",
    "RootPositiveCachedReturn",
    "RootPositiveFromLength",
    "RootPositiveToCachedCaller",
    "ScopedReleaseMaterialization",
    "SharedKeyResources",
    "CopyHolderRelease",
    "DuplicatePrefixPhysicalContexts",
    "PhysicalBoolGhostClear",
    "PhysicalBoolGhostPointer",
    "PhysicalBoolGhostRead",
    "PhysicalBoolGhostWindow",
    "PhysicalBoolWindowActual",
    "PhysicalBoolWindowPrimitive",
    "PhysicalBoolWindowValidateActual",
    "PhysicalBoolWindowValidation",
    "PhysicalBoolWindowWrite",
    "PhysicalSlotReleaseRights",
    "RootActualPhysicalReturn",
    "RootWindowPhysicalReturn",
    "S04ReturnAllocationClear",
    "S04ReturnPostStorage",
    "S04ReturnProvenanceClear",
    "S04ReturnResolvedWindowMemory",
    "S04ReturnResolvedWindowPointer",
    "S04ReturnWindowScalar",
    "S04SingleByteInit",
    "RootNonzeroSharedHeap",
    "RootPhysicalCarrierTransport",
    "RootPositiveFromBacking",
    "RootPositivePhysicalPop",
    "RootPositiveToPhysicalWindow",
    "RootPositiveWindowCarrier",
    "RootPositiveWindowReturn",
    "EmptyPointerShallow",
    "EmptyUnresolvedPointerBorrow",
    "EmptyWildcardLenArgumentCopy",
    "EmptyWildcardLenCallReturn",
    "EmptyWildcardLenCallStep",
    "EmptyWildcardLenEntry",
    "EmptyWildcardLenEntryValidity",
    "EmptyWildcardLenInstall",
    "EmptyWildcardLenUncachedCall",
    "EmptyWildcardLength",
    "EmptyWildcardLocalValidator",
    "EmptyWildcardLocalWrite",
    "EmptyWildcardPrefix",
    "EmptyWildcardReference",
    "EmptyWildcardRetag",
    "EmptyWildcardRootLenCall",
}
IMPORTS = re.compile(rb"^import duplicate_prefix\.([A-Za-z0-9_]+)\s*$", re.MULTILINE)
CLIENT_IMPORTS = re.compile(rb"^import ([A-Za-z][A-Za-z0-9_]*)(?:\.([A-Za-z0-9_]+))?\s*$", re.MULTILINE)


def client_imports(data):
    for namespace, module in CLIENT_IMPORTS.findall(data):
        name = namespace.decode()
        if name == "empty_function" and module == b"FrameExit":
            yield "empty_function.FrameExit"
        elif not module and (name == "Representative" or (CLIENT / f"{name}.lean").is_file()):
            yield name
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def archived(name):
    return subprocess.check_output(
        ["git", "show", f"{ARCHIVE}:{ARCHIVE_DIR}/{name}.lean"], cwd=REPO
    )


def proof_source(name):
    if name in LOCAL:
        return (CLIENT / "archive" / f"{name}.lean").read_bytes()
    return archived(name)


def install_sources(output, targets):
    source = output / ARCHIVE_DIR
    source.mkdir(parents=True)
    dependencies = {}

    def visit(name):
        if name in dependencies:
            return
        data = proof_source(name)
        (source / f"{name}.lean").write_bytes(data)
        parents = sorted({item.decode() for item in IMPORTS.findall(data)})
        dependencies[name] = set(parents)
        for parent in parents:
            visit(parent)

    # Load the pinned sources touched by the migration, including changes
    # outside the selected compilation closure.
    patch_modules = re.findall(
        rf"^--- a/{re.escape(ARCHIVE_DIR)}/([A-Za-z0-9_]+)\.lean$", PATCH.read_text(), re.MULTILINE
    )
    for target in (*targets, *patch_modules, *sorted(LOCAL)):
        visit(target)
    subprocess.run(
        ["patch", "--batch", "--forward", "--fuzz=0", "-p1", "-i", str(PATCH)],
        cwd=output,
        check=True,
    )
    # Imports can change when a proof needs a supporting tactic.
    for name in tuple(dependencies):
        data = (source / f"{name}.lean").read_bytes()
        dependencies[name] = {item.decode() for item in IMPORTS.findall(data)}
        for parent in dependencies[name]:
            visit(parent)
    closure = set()

    def keep(name):
        if name in closure:
            return
        closure.add(name)
        for parent in dependencies[name]:
            keep(parent)

    for target in targets:
        keep(target)
    return {name: dependencies[name] for name in sorted(closure)}


def input_copy(source, output):
    data = json.loads(source.read_text())
    if data["schema_version"] != 16 or data["producer"]["rustc_commit"] != RUSTC:
        raise SystemExit("expected a fresh schema-16 export from the pinned rustc")
    if [root["def_path"] for root in data["body_roots"]] != ["duplicate_prefix"]:
        raise SystemExit("expected the bare duplicate_prefix source as the sole exported root")
    shutil.copyfile(source, output / ARCHIVE_DIR / "input.json")


def install_clients(output, targets, generated, input_file):
    sources = output / "client"
    sources.mkdir()
    dependencies = {}

    def visit(name):
        if name in dependencies:
            return
        if name == "Representative":
            path = generated
        elif name == "empty_function.FrameExit":
            path = REPO / "examples/empty_function/FrameExit.lean"
        else:
            path = CLIENT / f"{name}.lean"
        if path is None or not path.is_file():
            raise SystemExit(f"missing source for {name}; provide --generated for Representative")
        data = path.read_bytes()
        source = sources.joinpath(*name.split(".")).with_suffix(".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_bytes(data)
        clients = set(client_imports(data))
        archive = {"duplicate_prefix." + item.decode() for item in IMPORTS.findall(data)}
        dependencies[name] = clients | archive
        for parent in sorted(clients):
            visit(parent)

    for name in targets:
        visit(name)
    if "Representative" in dependencies:
        shutil.copyfile(input_file, sources / "Representative.mir.json")
    return dependencies


def install_graph(output, archive_targets, client_targets, generated, input_file):
    if not client_targets and generated is None:
        archive = install_sources(output, archive_targets or CHECKED)
        return {
            "duplicate_prefix." + name: {"duplicate_prefix." + parent for parent in parents}
            for name, parents in archive.items()
        }
    client_targets = list(client_targets)
    clients = install_clients(output, client_targets, generated, input_file)
    targets = set(archive_targets or (CHECKED if not clients else ()))
    while True:
        targets.update(
            name.removeprefix("duplicate_prefix.")
            for parents in clients.values() for name in parents if name.startswith("duplicate_prefix.")
        )
        archive = install_sources(output, sorted(targets))
        extra = set()
        for name, parents in archive.items():
            data = (output / ARCHIVE_DIR / f"{name}.lean").read_bytes()
            direct = set(client_imports(data))
            extra.update(direct - clients.keys())
            clients["duplicate_prefix." + name] = {
                "duplicate_prefix." + parent for parent in parents
            } | direct
        if not extra:
            break
        targets.update(archive)
        shutil.rmtree(output / ARCHIVE_DIR)
        shutil.rmtree(output / "client")
        client_targets.extend(sorted(extra))
        clients = install_clients(output, client_targets, generated, input_file)
    return clients


def compile_proofs(output, dependencies, library, jobs):
    objects = output / "duplicate_prefix"
    objects.mkdir()
    logs = output / "logs"
    logs.mkdir()
    search_paths = [str(output), str(library)]
    if os.environ.get("LEAN_PATH"):
        search_paths.append(os.environ["LEAN_PATH"])
    env = {**os.environ, "LEAN_PATH": os.pathsep.join(search_paths), "LEAN_NUM_THREADS": "1"}
    lean = shutil.which("lean")
    if lean is None:
        raise SystemExit("put the pinned lean executable on PATH")

    def build(name):
        archive, _, module = name.partition(".")
        if archive == "duplicate_prefix":
            source_root = output / "examples"
            source = output / ARCHIVE_DIR / f"{module}.lean"
            object_file = objects / f"{module}.olean"
        else:
            source_root = output / "client"
            source = source_root.joinpath(*name.split(".")).with_suffix(".lean")
            object_file = output.joinpath(*name.split(".")).with_suffix(".olean")
            object_file.parent.mkdir(parents=True, exist_ok=True)
        path = logs / f"{name}.log"
        with path.open("wb") as log:
            result = subprocess.run(
                [lean, "-j1", f"--root={source_root}", "-o", str(object_file), str(source)],
                cwd=output, env=env, stdout=log, stderr=subprocess.STDOUT,
            )
        details = path.read_text(errors="replace")
        if re.search(r"declaration uses .sorry.", details):
            return name, False
        for listed in re.findall(r"depends on axioms: \[(.*?)\]", details, re.DOTALL):
            axioms = {item.strip() for item in listed.split(",") if item.strip()}
            if axioms - ALLOWED:
                return name, False
        return name, result.returncode == 0

    remaining = set(dependencies)
    checked = set()
    failed = set()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        pending = set()
        while remaining or pending:
            ready = sorted(name for name in remaining if dependencies[name] <= checked)
            for name in ready[:jobs - len(pending)]:
                remaining.remove(name)
                pending.add(pool.submit(build, name))
            if not pending:
                break
            completed, pending = wait(pending, return_when=FIRST_COMPLETED)
            for future in completed:
                name, success = future.result()
                print(f"{name}: {'checked' if success else 'failed'}", flush=True)
                (checked if success else failed).add(name)
    print(f"{len(checked)} checked, {len(failed)} failed, {len(remaining)} blocked")
    if failed:
        print("Failed: " + ", ".join(sorted(failed)))
    return 1 if failed or remaining else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="bare emitted duplicate_prefix MIR JSON")
    parser.add_argument("--output", required=True, type=Path, help="new proof overlay directory")
    parser.add_argument("--library", type=Path, default=REPO / ".lake/build/lib/lean",
                        help="prebuilt library artifacts")
    parser.add_argument("--target", action="append", help="override coverage with archive module names")
    parser.add_argument("--client", action="append", default=[], help="check a current example and its archive dependencies")
    parser.add_argument("--generated", type=Path, help="Representative.lean emitted alongside the supplied MIR")
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1 or any(not name.isidentifier() for name in (args.target or []) + args.client):
        parser.error("use a positive job count and archive module identifiers")
    present = subprocess.run(
        ["git", "cat-file", "-e", f"{ARCHIVE}^{{commit}}"], cwd=REPO
    )
    if present.returncode:
        parser.error(f"fetch the pinned proof archive revision with git fetch origin {ARCHIVE}")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dependencies = install_graph(output, args.target, args.client, args.generated, args.input.resolve())
    input_copy(args.input.resolve(), output)
    print(f"Checking {len(dependencies)} modules with archive revision {ARCHIVE}", flush=True)
    return compile_proofs(output, dependencies, args.library.resolve(), args.jobs)


if __name__ == "__main__":
    sys.exit(main())

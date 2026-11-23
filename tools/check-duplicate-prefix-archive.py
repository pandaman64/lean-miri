#!/usr/bin/env python3
"""Recheck the verified portions of the duplicate-prefix archive on current MIR."""
import argparse
from concurrent.futures import ThreadPoolExecutor
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
    "BorrowCopyRanges", "BorrowRelease", "ExistingPartition",
)
PATCH = REPO / "examples/duplicate_prefix_vcgen/ArchiveMigration.patch"
IMPORTS = re.compile(rb"^import duplicate_prefix\.([A-Za-z0-9_]+)\s*$", re.MULTILINE)
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def archived(name):
    return subprocess.check_output(
        ["git", "show", f"{ARCHIVE}:{ARCHIVE_DIR}/{name}.lean"], cwd=REPO
    )


def install_sources(output, targets):
    source = output / ARCHIVE_DIR
    source.mkdir(parents=True)
    dependencies = {}

    def visit(name):
        if name in dependencies:
            return
        data = archived(name)
        (source / f"{name}.lean").write_bytes(data)
        parents = sorted({item.decode() for item in IMPORTS.findall(data)})
        dependencies[name] = set(parents)
        for parent in parents:
            visit(parent)

    # Apply the same checked patch to every target. Materialize its touched
    # sources even for an explicitly selected subset.
    for target in (*CHECKED, *targets):
        visit(target)
    subprocess.run(
        ["patch", "--batch", "--forward", "--fuzz=0", "-p1", "-i", str(PATCH)],
        cwd=output,
        check=True,
    )
    # Imports can change when a proof needs a supporting tactic.
    for name in dependencies:
        data = (source / f"{name}.lean").read_bytes()
        dependencies[name] = {item.decode() for item in IMPORTS.findall(data)}
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


def compile_proofs(output, dependencies, library, jobs):
    objects = output / "duplicate_prefix"
    objects.mkdir()
    logs = output / "logs"
    logs.mkdir()
    env = {**os.environ, "LEAN_PATH": os.pathsep.join((str(output), str(library))),
           "LEAN_NUM_THREADS": "1"}
    lean = shutil.which("lean")
    if lean is None:
        raise SystemExit("put the pinned lean executable on PATH")

    def build(name):
        source = output / ARCHIVE_DIR / f"{name}.lean"
        path = logs / f"{name}.log"
        with path.open("wb") as log:
            result = subprocess.run(
                [lean, "-j1", f"--root={output / 'examples'}", "-o",
                 str(objects / f"{name}.olean"), str(source)],
                cwd=output, env=env, stdout=log, stderr=subprocess.STDOUT,
            )
        details = path.read_text(errors="replace")
        for listed in re.findall(r"depends on axioms: \[(.*?)\]", details):
            if set(item.strip() for item in listed.split(",")) - ALLOWED:
                return name, False
        return name, result.returncode == 0

    remaining = set(dependencies)
    checked = set()
    failed = set()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while remaining:
            ready = sorted(name for name in remaining if dependencies[name] <= checked)
            if not ready:
                break
            for name, success in pool.map(build, ready):
                remaining.remove(name)
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
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.jobs < 1 or any(not name.isidentifier() for name in args.target or []):
        parser.error("use a positive job count and archive module identifiers")
    present = subprocess.run(
        ["git", "cat-file", "-e", f"{ARCHIVE}^{{commit}}"], cwd=REPO
    )
    if present.returncode:
        parser.error(f"fetch the pinned proof archive revision with git fetch origin {ARCHIVE}")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dependencies = install_sources(output, args.target or CHECKED)
    input_copy(args.input.resolve(), output)
    print(f"Checking {len(dependencies)} modules from {ARCHIVE}", flush=True)
    return compile_proofs(output, dependencies, args.library.resolve(), args.jobs)


if __name__ == "__main__":
    sys.exit(main())

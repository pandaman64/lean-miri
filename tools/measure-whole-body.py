#!/usr/bin/env python3
"""Measure public whole-body and imported-program VC generation.

First build Miri.Verification.BodyVCGen and Miri.Frontend.ImportMIR with the pinned Lean toolchain.
The output directory receives the compiled harness, probe inputs, and JSON.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import statistics
import subprocess
import time


ROOT = Path(__file__).resolve().parent.parent
CGROUP = Path("/sys/fs/cgroup")
PHASES = ("source_ns", "compile_ns", "equations_ns", "vcgen_ns", "entry_ns", "reflect_ns", "generate_ns", "typecheck_ns")
PROGRAM_COUNTS = ("bodies", "root_blocks", "largest_callee_blocks")
COUNTS = ("blocks", "equations", "edges", "joins", "vcs", "expression_nodes", "max_expression_nodes")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cpu_stats():
    return {
        key: int(value)
        for key, value in (line.split() for line in (CGROUP / "cpu.stat").read_text().splitlines())
    }


def steal(cpu):
    for line in Path("/proc/stat").read_text().splitlines():
        if line.startswith(f"cpu{cpu} "):
            return int(line.split()[8]) / os.sysconf("SC_CLK_TCK")
    raise RuntimeError(f"CPU {cpu} is missing from /proc/stat")


def parse_measurements(stdout, diamonds=None):
    row = {}
    for line in stdout.splitlines():
        for field in line.split():
            key, sep, value = field.partition("=")
            if sep and key in PHASES + COUNTS + PROGRAM_COUNTS:
                if key in row:
                    raise RuntimeError(f"duplicate benchmark field {key}")
                row[key] = int(value)
    missing = set(PHASES + COUNTS) - row.keys()
    if missing:
        raise RuntimeError(f"missing benchmark fields {sorted(missing)} in {stdout!r}")
    if row["vcs"] != row["equations"] or not row["blocks"]:
        raise RuntimeError(f"invalid generated condition count: {row}")
    if diamonds is None:
        if any(not row.get(key) for key in ("bodies", "root_blocks")):
            raise RuntimeError(f"invalid imported catalogue counts: {row}")
        return row
    blocks = 3 * diamonds + 1
    expected = {"blocks": blocks, "equations": 2 * blocks, "edges": 7 * diamonds + 1,
                "joins": diamonds, "vcs": 2 * blocks}
    if any(row[key] != value for key, value in expected.items()):
        raise RuntimeError(f"invalid benchmark topology: {row}")
    return row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="pinned Lean executable")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--library", type=Path, default=ROOT / ".lake/build/lib/lean",
                        help="directory containing the compiled Miri library")
    parser.add_argument("--diamonds", type=int, nargs="*", default=[32, 128, 512, 1024])
    parser.add_argument("--import-json", type=Path, action="append", default=[],
                        help="exported execution input for an independent program-catalogue trial")
    parser.add_argument("--root", type=int, default=0, help="root index for imported trials")
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("--cpu must be in the current affinity set")
    if args.trials < 1 or args.timeout < 1 or any(count < 1 for count in args.diamonds):
        parser.error("diamond count, trial count, and timeout must be positive")
    if args.root < 0:
        parser.error("--root must be nonnegative")
    if not args.diamonds and not args.import_json:
        parser.error("provide a diamond count or an imported body")
    if len(set(args.diamonds)) != len(args.diamonds):
        parser.error("provide distinct diamond counts")

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    library = args.library.resolve()
    harness_source = ROOT / "tools/BenchmarkWholeBody.lean"
    harness = output / "BenchmarkWholeBody.olean"
    cfg = library / "Miri/Verification/BodyCFG.olean"
    frontend = library / "Miri/Verification/BodyVCGen.olean"
    whole_body = library / "Miri/Verification/WholeBodyWP.olean"
    pinned = ["taskset", "-c", str(args.cpu), args.lean, "-j1"]
    env = {**os.environ, "LEAN_NUM_THREADS": "1", "LEAN_PATH": str(library)}
    start = time.perf_counter()
    subprocess.run(
        pinned + ["--root=" + str(ROOT / "tools"), "-o", str(harness), str(harness_source)],
        cwd=ROOT, env=env, check=True, timeout=args.timeout,
    )
    harness_compile_wall_s = time.perf_counter() - start
    env["LEAN_PATH"] = os.pathsep.join((str(output), str(library)))
    artifact_digests = {str(path): digest(path) for path in (harness_source, harness, cfg, frontend, whole_body)}
    probes = []
    common = "open Std.WP\nset_option maxHeartbeats 0\nset_option maxRecDepth 65536\nset_option experimental.vcgen true\n"
    for diamonds in args.diamonds:
        probe = output / f"Diamond{diamonds}.lean"
        probe.write_text(
            "import BenchmarkWholeBody\n" + common + f"#benchmark_whole_body {diamonds}\n"
        )
        probes.append((f"diamond-{diamonds}", diamonds, probe))
    import_compile_wall_s = {}
    for index, source in enumerate(args.import_json):
        source = source.resolve()
        module = f"ImportedBody{index}"
        importer, artifact = (output / (module + extension) for extension in (".lean", ".olean"))
        importer.write_text(
            "import Miri.Frontend.ImportMIR\nopen Miri.Frontend\n" + common +
            f"import_mir {json.dumps(str(source))} as benchmarkInput{index}\n"
        )
        start = time.perf_counter()
        subprocess.run(
            pinned + ["--root=" + str(output), "-o", str(artifact), str(importer)],
            cwd=ROOT, env=env, check=True, timeout=args.timeout,
        )
        import_compile_wall_s[f"imported-{index}"] = time.perf_counter() - start
        for path in (source, importer, artifact):
            artifact_digests[str(path)] = digest(path)
        probe = output / f"ImportedProbe{index}.lean"
        probe.write_text(
            f"import {module}\nimport BenchmarkWholeBody\n" + common +
            f"#benchmark_imported_body benchmarkInput{index} {args.root}\n"
        )
        probes.append((f"imported-{index}", None, probe))
    for _, _, probe in probes:
        artifact_digests[str(probe)] = digest(probe)
    result = {
        "cpu": args.cpu,
        "lean_threads": 1,
        "cpu_max": (CGROUP / "cpu.max").read_text().strip(),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "artifacts_sha256": artifact_digests,
        "harness_compile_wall_s": harness_compile_wall_s,
        "import_compile_wall_s": import_compile_wall_s,
        "trials": [],
    }
    log = output / "measurements.json"
    for trial in range(args.trials):
        order = probes if trial % 2 == 0 else reversed(probes)
        for case, diamonds, probe in order:
            command = pinned + [str(probe)]
            cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
            stat_before, steal_before = cpu_stats(), steal(args.cpu)
            start = time.perf_counter()
            completed = subprocess.run(command, cwd=ROOT, env=env, capture_output=True,
                                       text=True, timeout=args.timeout)
            wall_s = time.perf_counter() - start
            cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
            stat_after, steal_after = cpu_stats(), steal(args.cpu)
            record = {
                "case": case, "diamonds": diamonds, "trial": trial, "command": command,
                "wall_s": wall_s, "user_s": cpu_after.ru_utime - cpu_before.ru_utime,
                "system_s": cpu_after.ru_stime - cpu_before.ru_stime,
                "same_cpu_steal_s": steal_after - steal_before,
                "cgroup_delta": {key: after - stat_before[key] for key, after in stat_after.items()},
                "exit_code": completed.returncode, "stdout": completed.stdout,
                "stderr": completed.stderr,
            }
            result["trials"].append(record)
            log.write_text(json.dumps(result, indent=2) + "\n")
            completed.check_returncode()
            record.update(parse_measurements(completed.stdout, diamonds))
            if any(digest(Path(path)) != value for path, value in artifact_digests.items()):
                raise RuntimeError("benchmark inputs changed during measurement")
            log.write_text(json.dumps(result, indent=2) + "\n")
            print(f"{record['blocks']} blocks, trial {trial + 1}: "
                  f"generation {record['generate_ns'] / 1e6:.3f} ms, "
                  f"reflection {record['reflect_ns'] / 1e6:.3f} ms", flush=True)
    result["summary"] = {}
    for case, _, _ in probes:
        trials = [record for record in result["trials"] if record["case"] == case]
        result["summary"][case] = {
            field: {
                "min": min(record[field] for record in trials),
                "median": statistics.median(record[field] for record in trials),
                "max": max(record[field] for record in trials),
            }
            for field in (*PHASES, "wall_s", "user_s", "system_s", "same_cpu_steal_s")
        }
    log.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()

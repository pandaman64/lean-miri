#!/usr/bin/env python3
"""Time public VC generation, generated-module checking, and a proof from source.

Build the pinned library and prepare the proof's inputs first. Use --library
and --proof-library to point at immutable compiled dependency trees. Each
sample starts fresh processes and generates a fresh module. File-system caches
and compiled imports are retained. Any certificate preparation is outside these
timers unless the Lean proof file itself performs it.
"""
import argparse
import json
import os
from pathlib import Path
import re
import resource
import statistics
import subprocess
import time

from measure import ROOT, TICKS, counters, sha


def sample(command, env, cpu, timeout, output):
    before = counters(-1, cpu)
    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.perf_counter()
    with output.open("wb") as log:
        completed = subprocess.run(
            ["taskset", "-c", str(cpu), *command], cwd=ROOT, env=env,
            stdout=log, stderr=subprocess.STDOUT, timeout=timeout,
        )
    wall_s = time.perf_counter() - start
    cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    after = counters(-1, cpu)
    stats_before = before["cgroup_cpu_stat"]
    stats_after = after["cgroup_cpu_stat"]
    return {
        "command": command,
        "wall_s": wall_s,
        "user_s": cpu_after.ru_utime - cpu_before.ru_utime,
        "system_s": cpu_after.ru_stime - cpu_before.ru_stime,
        "same_cpu_steal_s": (after["selected_cpu_steal_ticks"] - before["selected_cpu_steal_ticks"]) / TICKS,
        "cgroup_delta": {key: value - stats_before[key] for key, value in stats_after.items()},
        "exit_code": completed.returncode,
        "log": str(output),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--proof", type=Path, help="Lean source proof to check")
    parser.add_argument("--replay-runner", type=Path,
                        help="frozen NativeRunner for an exact deterministic replay")
    parser.add_argument("--execution-input", type=Path,
                        help="runtime harness export, checked against the exact emitted MIR body")
    parser.add_argument("--replay-args", default="[]", help="JSON list of runner arguments before profiling")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", default="Generated", help="generated Lean module imported by the proof")
    parser.add_argument("--root", help="optional root selector passed to body-vc")
    parser.add_argument("--lean", default="lean", help="pinned Lean executable")
    parser.add_argument("--library", type=Path, default=ROOT / ".lake/build/lib/lean")
    parser.add_argument("--proof-library", type=Path, action="append", default=[])
    parser.add_argument("--cpu", type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument("--trials", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    if not args.proof and not args.replay_runner:
        parser.error("provide --proof or --replay-runner")
    if args.cpu not in os.sched_getaffinity(0):
        parser.error("--cpu must be in the current affinity set")
    if args.trials < 1 or args.timeout < 1:
        parser.error("--trials and --timeout must be positive")
    if not args.module.isidentifier():
        parser.error("--module must be a single Lean module identifier")

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    source = args.input.resolve()
    proof = args.proof.resolve() if args.proof else None
    replay = args.replay_runner.resolve() if args.replay_runner else None
    execution_input = args.execution_input.resolve() if args.execution_input else None
    if execution_input and not replay:
        parser.error("--execution-input is only used with --replay-runner")
    replay_args = json.loads(args.replay_args)
    if not isinstance(replay_args, list) or not all(isinstance(arg, str) for arg in replay_args):
        parser.error("--replay-args must be a JSON array of strings")
    library = args.library.resolve()
    cli = ROOT / "tools/body-vc"
    artifacts = [
        source, cli, ROOT / "tools/GenerateBodyVC.lean",
        *(path for path in (proof, replay, execution_input) if path is not None),
        library / "Miri/Verification/BodyVCGen.olean",
        library / "Miri/Verification/WholeBodyWP.olean", library / "Miri/Verification/BodyCFG.olean",
    ]
    artifact_digests = {str(path): sha(path) for path in artifacts}
    result = {
        "source": str(source), "proof": str(proof) if proof else None,
        "replay_runner": str(replay) if replay else None,
        "execution_input": str(execution_input) if execution_input else None, "lean": args.lean,
        "library": str(library), "proof_libraries": [str(path.resolve()) for path in args.proof_library],
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "cpu": args.cpu, "lean_threads": 1, "artifacts_sha256": artifact_digests,
        "cpu_max": counters(-1, args.cpu)["cpu_max"], "trials": [],
        "boundary": "fresh output and Lean processes, prebuilt imports, file-system caches retained",
    }
    summary_path = output / "measurements.json"
    for trial in range(args.trials):
        work = output / f"trial-{trial + 1}"
        work.mkdir()
        generated = work / f"{args.module}.lean"
        artifact = generated.with_suffix(".olean")
        # The proof's dependency packages may refer to the newly generated module.
        lean_path = os.pathsep.join(str(path) for path in (
            work, library, *(path.resolve() for path in args.proof_library),
        ))
        env = {**os.environ, "LEAN_PATH": lean_path, "LEAN_NUM_THREADS": "1"}
        if (ROOT / ".elan").is_dir():
            env.setdefault("ELAN_HOME", str(ROOT / ".elan"))
        generate = [str(cli), "safety", str(source), "--output", str(generated),
                    "--no-build", "--no-check"]
        if args.root is not None:
            generate.extend(["--root", str(args.root)])
        record = {}
        result["trials"].append(record)
        stages = [
            ("generate", generate),
            ("check_generated", [args.lean, "-j1", f"--root={work}", "-o", str(artifact), str(generated)]),
        ]
        for label, command in stages:
            log = work / f"{label}.log"
            record[label] = sample(command, env, args.cpu, args.timeout, log)
            if label == "generate" and record[label]["exit_code"] == 0:
                rendered = log.read_text()
                for phase, pattern in (
                    ("rust_mir_export_s", r"Rust MIR export: ([0-9.]+) s"),
                    ("generated_vc_s", r"VC generation and artifact writing: ([0-9.]+) s"),
                    ("load_and_graph_ns", r"Loaded and compiled MIR equations in ([0-9]+) ns"),
                ):
                    match = re.search(pattern, rendered)
                    if match:
                        record[label][phase] = float(match[1]) if phase.endswith("_s") else int(match[1])
            summary_path.write_text(json.dumps(result, indent=2) + "\n")
            if record[label]["exit_code"]:
                raise SystemExit(f"{label} failed, see {record[label]['log']}")
            print(f"trial {trial + 1} {label} {record[label]['wall_s']:.3f}s", flush=True)

        checks = []
        if proof:
            checks.append(("check_proof", [args.lean, "-j1", str(proof)]))
        if replay:
            selected = re.search(r"BodyVCGen.loadProgram input (\d+)", generated.read_text())
            if selected is None:
                raise SystemExit(f"cannot identify the generated body in {generated}")
            sidecar = generated.with_suffix(".mir.json")
            if execution_input:
                selector = ["--check-body-vc-input", str(sidecar), selected[1]]
            else:
                selector = ["--check-body-vc-root", selected[1]]
            command = [str(replay), str(execution_input or sidecar), *replay_args, "--profile", *selector]
            checks.append(("check_replay", command))
        for label, command in checks:
            log = work / f"{label}.log"
            record[label] = sample(command, env, args.cpu, args.timeout, log)
            stages.append((label, command))
            if label == "check_replay" and record[label]["exit_code"] == 0:
                rendered = log.read_text()
                verdicts = [line for line in rendered.splitlines() if line.startswith("body_vc: ")]
                durations = [float(value) / (1000 if unit == "ms" else 1) for value, unit in re.findall(
                    r"body_vc.proof_replay took ([0-9.]+)(ms|s)", rendered)]
                record[label]["certificates"] = verdicts
                record[label]["certificate_replay_s"] = sum(durations)
                if (not verdicts or len(durations) != len(verdicts) or
                        any("normal=true" not in verdict or "no_ub=true" not in verdict for verdict in verdicts) or
                        "run: finalized_exit code=0" not in rendered):
                    summary_path.write_text(json.dumps(result, indent=2) + "\n")
                    raise SystemExit(f"the runner did not certify a completed positive call, see {log}")
            summary_path.write_text(json.dumps(result, indent=2) + "\n")
            if record[label]["exit_code"]:
                raise SystemExit(f"{label} failed, see {log}")
            print(f"trial {trial + 1} {label} {record[label]['wall_s']:.3f}s", flush=True)
        if any(sha(Path(path)) != digest for path, digest in artifact_digests.items()):
            raise SystemExit("benchmark inputs changed during measurement")
    summary = {}
    for label, _ in stages:
        summary[label] = {}
        for metric in ("wall_s", "user_s", "system_s", "same_cpu_steal_s", "rust_mir_export_s",
                       "generated_vc_s", "load_and_graph_ns", "certificate_replay_s"):
            if not all(metric in trial[label] for trial in result["trials"]):
                continue
            values = [trial[label][metric] for trial in result["trials"]]
            summary[label][metric] = {
                "min": min(values), "median": statistics.median(values), "max": max(values),
            }
    result["summary"] = summary
    summary_path.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()

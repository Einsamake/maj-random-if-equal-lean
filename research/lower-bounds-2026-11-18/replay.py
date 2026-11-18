"""Rebuild this extension against the locked, already built analysis project."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
MODULES = (
    "FullBlockThreshold", "DirectionalDrift", "SquareSurvival", "UniformLower",
    "Packing", "FastTail", "TriangleLoss", "ImprovedMean", "LowerProgressAudit",
)
OPTIONAL_PARALLEL_RESULTS = {
    "ClockLiteratureTransfer.lean", "DeterministicClockRestart.lean",
    "FirstMomentClockUpper.lean",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(directory, pattern):
    return {p.name: digest(p) for p in sorted(directory.glob(pattern))}


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--repo", type=Path, default=HERE.parents[1])
    cli.add_argument("--analysis", type=Path, help="Reuse a byte-matching analysis checkout")
    cli.add_argument("--lean", default="lean", help="Lean executable or elan shim")
    args = cli.parse_args()
    repo = args.repo.resolve()
    locked = repo / "formal/analysis"
    analysis = args.analysis.resolve() if args.analysis else locked
    lock = digest(locked / "lake-manifest.json")
    if lock != digest(analysis / "lake-manifest.json"):
        raise SystemExit("Analysis dependency lock mismatch")
    sources = snapshot(locked / "MathResearchAnalysis", "*.lean")
    reused_sources = snapshot(analysis / "MathResearchAnalysis", "*.lean")
    missing = sources.keys() - reused_sources.keys()
    if (not reused_sources or missing - OPTIONAL_PARALLEL_RESULTS
            or any(sources.get(name) != sha for name, sha in reused_sources.items())):
        raise SystemExit("Analysis source mismatch")
    live = analysis / ".lake/build/lib/lean"
    objects = {
        name: value for name, value in
        snapshot(live / "MathResearchAnalysis", "*.olean*").items()
        if not name.endswith(".hash")
    }
    if not objects:
        raise SystemExit("Build the locked analysis project first")
    roots = [live, *sorted((analysis / ".lake/packages").glob("*/.lake/build/lib/lean"))]
    out = HERE / ".lake/lower-progress"
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [out, *roots])))
    version = subprocess.check_output([args.lean, "--version"], cwd=analysis, text=True).strip()
    if "version 4.35.0-rc4," not in version:
        raise SystemExit(f"Unexpected toolchain: {version}")
    records = {}
    for name in MODULES:
        src = (repo / "research/revision-ab-2026-11-17/lean/dependencies"
               if name == "FullBlockThreshold" else HERE) / f"{name}.lean"
        obj = out / f"{name}.olean"
        log = out / f"{name}.log"
        with log.open("wb") as stream:
            proc = subprocess.run(
                [args.lean, "--trust=0", "-j", "4", "--root=" + str(src.parent),
                 "-o", str(obj), str(src)],
                cwd=analysis, env=env, stdout=stream, stderr=subprocess.STDOUT,
            )
        if proc.returncode:
            print(log.read_text(encoding="utf-8", errors="replace"))
            raise SystemExit(proc.returncode)
        records[name] = dict(source=digest(src), compiled=digest(obj), log=digest(log))
        print("PASS", name, flush=True)
    audit = (out / "LowerProgressAudit.log").read_text(encoding="utf-8")
    counts = {mod: int(count) for mod, count in re.findall(r"AUDIT_COUNT (\w+) (\d+)", audit)}
    if set(counts) != set(MODULES[:-1]) or len(re.findall(r"\bAUDIT ", audit)) != sum(counts.values()):
        raise SystemExit("Incomplete audit output")
    if reused_sources != snapshot(analysis / "MathResearchAnalysis", "*.lean"):
        raise SystemExit("Analysis sources changed during replay")
    receipt = dict(status="PASS", trust=0, toolchain=version, modules=records,
                   audit_counts=counts, audit_total=sum(counts.values()),
                   driver=digest(Path(__file__)), analysis_dependency_lock=lock,
                   analysis_sources=reused_sources, absent_parallel_sources=sorted(missing),
                   reused_analysis_objects=objects)
    (out / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("AUDIT_TOTAL", receipt["audit_total"], flush=True)


if __name__ == "__main__":
    main()

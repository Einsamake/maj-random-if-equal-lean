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
    "Packing", "FastTail", "Reciprocal", "TriangleLoss", "StaticSharpness",
    "ImprovedMean", "AsymptoticLower", "StoppedOccupation", "StoppedLower",
    "LowerConsequences", "EarliestSquare", "EarliestAtom", "AllScaleLower",
    "ForcedCorners", "MinimumAtomUpper", "LowerAudit",
)
PREVIOUS = {"DirectionalDrift", "SquareSurvival", "UniformLower"}
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
        directory = HERE
        if name == "FullBlockThreshold":
            directory = repo / "research/revision-ab-2026-11-17/lean/dependencies"
        elif name in PREVIOUS:
            directory = repo / "research/lower-bounds-2026-11-18"
        src = directory / f"{name}.lean"
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
    audit = (out / "LowerAudit.log").read_text(encoding="utf-8")
    total = re.search(r"AUDIT_TOTAL (\d+)", audit)
    if total is None or len(re.findall(r"\bAUDIT ", audit)) != int(total[1]):
        raise SystemExit("Incomplete audit output")
    if reused_sources != snapshot(analysis / "MathResearchAnalysis", "*.lean"):
        raise SystemExit("Analysis sources changed during replay")
    receipt = dict(status="PASS", trust=0, toolchain=version, modules=records,
                   audit_total=int(total[1]),
                   driver=digest(Path(__file__)), analysis_dependency_lock=lock,
                   analysis_sources=reused_sources, absent_parallel_sources=sorted(missing),
                   reused_analysis_objects=objects)
    (out / "validation.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print("AUDIT_TOTAL", receipt["audit_total"], flush=True)


if __name__ == "__main__":
    main()

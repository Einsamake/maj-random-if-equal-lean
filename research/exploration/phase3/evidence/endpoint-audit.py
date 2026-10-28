"""Preserve each actual standard-trust-zero build and its axiom outputs."""
from pathlib import Path
from datetime import datetime
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
parser = argparse.ArgumentParser()
parser.add_argument("source", type=Path)
parser.add_argument("--attempt", required=True)
parser.add_argument("--cache", action="store_true")
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
source = args.source.resolve()
project = Path("D:/MyWorks/Math")
root.joinpath("build").mkdir(parents=True, exist_ok=True)
prefix = root / "evidence" / (source.stem + "-" + args.attempt)
assert not prefix.with_suffix(".json").exists()
before = source.read_bytes()
source_text = before.decode("utf-8")
expected = re.findall(r"^#print axioms (\S+)", source_text, re.M)
assert expected
assert not re.search(r"\b(sorry|admit|native_decide)\b", source_text)
environment = os.environ.copy()
environment["LEAN_PATH"] = ";".join(
    [str(root / "build"), str(project / "research/exploration/phase2/build")]
)
command = [
    str(project / "formal/.tools/lean-4.35.0-rc4-windows/bin/lake.exe"),
    "env", "lean", "--trust=0", "--root=" + str(source.parent),
]
output = root / "build" / (source.stem + ".olean")
if args.cache:
    command.extend(["-o", str(output)])
command.append(str(source))
run = subprocess.run(
    command, cwd=project / "formal/analysis", env=environment,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
prefix.with_suffix(".log").write_bytes(run.stdout)
text = run.stdout.decode("utf-8", errors="replace")
actual = []
by_declaration = {}
for match in re.finditer(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    text, re.S,
):
    name = match.group(1)
    actual.append(name)
    by_declaration[name] = [] if match.group(2) is None else [
        item.strip() for item in match.group(2).split(",") if item.strip()
    ]
axioms = {item for items in by_declaration.values() for item in items}
checks = {
    "actual_exit_zero": run.returncode == 0,
    "standard_trust_zero": "--trust=0" in command,
    "source_unchanged_during_build": before == source.read_bytes(),
    "actual_names_match_expected": actual == expected,
    "only_standard_axioms": axioms <= {"propext", "Classical.choice", "Quot.sound"},
    "no_errors_in_log": not re.search(r"\berror(?:\(|:)", text),
}
passed = all(checks.values())
metadata = {
    "checked_at": datetime.now().astimezone().isoformat(),
    "module": source.stem, "source": str(source), "exit_code": run.returncode,
    "trust_level": 0, "checks_passed": passed, "checks": checks,
    "source_sha256": hashlib.sha256(before).hexdigest(),
    "log_sha256": hashlib.sha256(run.stdout).hexdigest(),
    "command": command, "cwd": str(project / "formal/analysis"),
    "LEAN_PATH": environment["LEAN_PATH"],
    "named_declarations": actual, "expected_prints": expected,
    "declaration_axioms": by_declaration, "axioms_seen": sorted(axioms),
}
if args.cache and passed:
    metadata["olean_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
prefix.with_suffix(".json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
print(text)
print(json.dumps({key: value for key, value in metadata.items()
                  if key not in ["named_declarations", "expected_prints", "declaration_axioms"]}))
sys.exit(0 if passed else 1)

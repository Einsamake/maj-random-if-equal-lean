"""Independent read-only checks against the saved validation baseline."""
from datetime import datetime, timedelta, timezone
from pathlib import Path
import hashlib
import json
import re
import sys

formal = Path(__file__).resolve().parents[1]
audit = formal / "audit"
analysis = formal / "analysis"


def no_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def check_layer(name, root):
    validation_path = audit / f"{name}-validation.json"
    validation = json.loads(validation_path.read_text(encoding="utf-8"))
    scanned = {}
    for relative, expected in validation["source_sha256"].items():
        path = root / relative
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        code = no_comments(path.read_text(encoding="utf-8"))
        scanned[relative] = {
            "sha256": actual,
            "baseline_matches": actual == expected,
            "forbidden": re.findall(
                r"\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|debug\.skipKernelTC",
                code,
            ),
            "metaprogramming_to_review": re.findall(
                r"\b(?:elab|macro|run_elab|extern|addDecl|ofReduceBool|ofReduceNat)\b", code
            ),
        }
    log = (audit / f"{name}-axioms.log").read_text(encoding="utf-8")
    declarations = re.findall(
        r"(?m)^'(.+)' (?:depends on axioms:|does not depend on any axioms)", log
    )
    axioms = sorted(set(
        item.strip()
        for body in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
        for item in body.split(",") if item.strip()
    ))
    return {
        "recorded_validation_at": validation.get("validated_at"),
        "validation_sha256": hashlib.sha256(validation_path.read_bytes()).hexdigest(),
        "public_theorems": validation["public_theorems"],
        "recorded_build_exit": validation["build_exit"],
        "recorded_axiom_audit_exit": validation["axiom_audit_exit"],
        "recorded_kernel_trust_level": validation.get("kernel_trust_level"),
        "recorded_axiom_audit_command": validation.get("axiom_audit_command"),
        "public_axiom_log_entries": len(declarations),
        "unique_axiom_log_entries": len(set(declarations)),
        "axioms_seen_independently": axioms,
        "sources": scanned,
    }


visited = set()


def visit(module):
    if module in visited or not module.startswith("MathResearchAnalysis."):
        return
    visited.add(module)
    path = analysis / (module.replace(".", "/") + ".lean")
    for imported in re.findall(r"(?m)^\s*(?:public\s+)?import\s+(\S+)", path.read_text(encoding="utf-8")):
        visit(imported)


visit("MathResearchAnalysis.SquarePWCensoring")
result = {
    "checked_at_beijing": datetime.now(timezone(timedelta(hours=8))).isoformat(),
    "audit_role": "independent AI code and semantic review; no human expert certification",
    "analysis": check_layer("analysis", analysis),
    "core": check_layer("core", formal),
    "trust_zero_entrypoint": "SquarePWCensoring",
    "trust_zero_local_import_closure_modules": sorted(visited),
    "trust_zero_local_import_closure_count": len(visited),
}
path = audit / (sys.argv[1] if len(sys.argv) > 1 else "independent-semantic-baseline-2026-10-14.json")
path.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
summary = {k: {s: v for s, v in result[k].items() if s != "sources"} for k in ("analysis", "core")}
summary["source_hash_mismatches"] = {
    k: [p for p, v in result[k]["sources"].items() if not v["baseline_matches"]]
    for k in ("analysis", "core")
}
summary["forbidden_or_metaprogramming_hits"] = {
    k: {p: v for p, v in result[k]["sources"].items() if v["forbidden"] or v["metaprogramming_to_review"]}
    for k in ("analysis", "core")
}
summary["trust_zero_local_import_closure_count"] = len(visited)
print(json.dumps(summary, ensure_ascii=False, indent=2))

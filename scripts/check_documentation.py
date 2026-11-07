"""Read-only checks for the academic documentation edition.

This checks byte identity and document consistency, not Lean proof correctness.
Run in a Git clone containing the recorded baseline commit.
"""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, json, re, subprocess, sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
META = ROOT / "docs/academic-revision-2026-11-07/manifest.json"

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def tree(commit):
    p = subprocess.run(["git", "-C", str(ROOT), "ls-tree", "-rz", commit],
                       check=True, stdout=subprocess.PIPE)
    result = {}
    for item in p.stdout.split(b"\0"):
        if not item:
            continue
        head, path = item.split(b"\t", 1)
        mode, kind, obj = head.split()
        if kind == b"blob":
            result[path.decode("utf-8")] = obj.decode("ascii")
    return result

def blob(path):
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()

def stripped_markdown(s):
    s = re.sub(r"```[\s\S]*?```", "", s)
    s = re.sub(r"\$\$[\s\S]*?\$\$", "", s)
    return re.sub(r"(?<!\\)\$[^$\n]+\$", "", s)

def main():
    a = argparse.ArgumentParser()
    a.add_argument("--json-output", type=Path)
    args = a.parse_args()
    meta = load(META)
    base = tree(meta["baseline_commit"])
    rewritten = set(meta["rewritten_baseline_documents"])
    assert rewritten <= set(base)
    assert all(p.endswith(".md") for p in rewritten)
    retained = 0
    for rel, obj in base.items():
        if rel in rewritten:
            continue
        path = ROOT / rel
        assert path.is_file(), "Missing archived file: " + rel
        assert blob(path) == obj, "Archived bytes changed: " + rel
        retained += 1
    official = load(ROOT / "formal/audit/original-theta-independent-final-binding-evidence.json")
    for rel, h in official["all_formal_source_sha256"].items():
        assert digest(ROOT / "formal" / rel) == h.lower(), rel
    assert len(official["all_formal_source_sha256"]) == 267
    for rel, h in meta["exploration_source_sha256"].items():
        assert digest(ROOT / rel) == h, rel
    links = 0
    for rel, h in meta["current_documents_sha256"].items():
        path = ROOT / rel
        assert digest(path) == h, "Document version mismatch: " + rel
        raw = path.read_bytes()
        assert b"\r\r" not in raw, "Repeated CR: " + rel
        s = raw.decode("utf-8")
        assert not re.search(r"^\+(?:#|\[|[^\s+])", stripped_markdown(s), re.M), "Edit marker: " + rel
        assert s.count("$$") % 2 == 0, "Unpaired display math: " + rel
        for block in re.findall(r"\$\$([\s\S]*?)\$\$", s):
            assert not re.search(r"\n\s*\n", block), "Blank paragraph inside display math: " + rel
        text = stripped_markdown(s)
        for dest in re.findall(r"!?\[[^\]\n]*\]\(([^)\n]+)\)", text):
            dest = dest.strip().split(' "', 1)[0].strip("<>")
            if dest.startswith(("https://", "http://", "mailto:")):
                continue
            target, _, anchor = dest.partition("#")
            if target:
                assert not re.match(r"[A-Za-z]:", target), "Local machine path: " + rel
                resolved = (path.parent / unquote(target)).resolve()
                assert resolved.is_relative_to(ROOT), (rel, dest)
                assert resolved.exists(), (rel, dest)
            else:
                resolved = path
            if anchor and resolved.suffix == ".md":
                body = resolved.read_text(encoding="utf-8")
                headings = re.findall(r"^#+\s+(.+)$", body, re.M)
                slugs = {re.sub(r"[^\w\- ]", "", t.lower()).replace(" ", "-") for t in headings}
                assert anchor in slugs or ('id="' + anchor + '"') in body, (rel, dest)
            links += 1
    for rel, h in meta["current_figures_sha256"].items():
        assert digest(ROOT / rel) == h
    figure = load(ROOT / "docs/academic-figures/toy-checks.json")
    assert digest(ROOT / "docs/academic-figures/render_figures.py") == figure["render_script_sha256"]
    for name, h in figure["figures"].items():
        assert digest(ROOT / "docs/academic-figures/images" / name) == h
    for row in figure["ordinary_and_weighted_initial_rates"]:
        assert Fraction(row["ordinary_masked"]) == 2 * row["L"]
        assert Fraction(row["ordinary_expanded"]) == 2
        assert row["weighted_masked"] == row["weighted_expanded"]
    assert Fraction(33, 50) - Fraction(353, 606) == Fraction(587, 7575)
    assert Fraction(16, 129) < Fraction(1, 8)
    result = {
        "status": "PASS",
        "scope": "Documentation, exact examples, links, unchanged published proofs and archives; no new Lean build",
        "baseline_commit": meta["baseline_commit"],
        "baseline_files_retained_byte_identically": retained,
        "rewritten_baseline_documents": len(rewritten),
        "current_documents_checked": len(meta["current_documents_sha256"]),
        "local_document_links_checked": links,
        "formal_source_sha256_matches": 267,
        "exploration_source_sha256_matches": len(meta["exploration_source_sha256"]),
        "academic_figures_checked": len(meta["current_figures_sha256"]),
        "sealed_zip_sha256": digest(ROOT / "deliverables/Lean形式化材料_2026-10-26.zip"),
        "new_kernel_build_performed": False,
        "human_expert_review_claimed": False,
    }
    if args.json_output:
        args.json_output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, subprocess.CalledProcessError) as exc:
        print("FAIL: " + str(exc), file=sys.stderr)
        sys.exit(1)

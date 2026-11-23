# Versions and archival records

[简体中文](ARCHIVAL_RECORD.zh-CN.md)

<a id="版本与归档约定"></a>

The mathematical sources, machine-check records and explanatory documents each apply to their recorded versions. The November 2026 documentation revisions retained the Lean sources, existing audit logs, verification JSON files and sealed ZIP archives.

<a id="数学源与说明文稿"></a>

## Mathematical sources and expository documents

The original main theorem's formal sources are the 267 files under `formal/`. Research summaries and figure captions describe the theorems in prose. The waiting-network research studies a different model from the cellular automaton and has its own mathematical sources and verification records for each phase.

The current manuscript draws on the sources in this repository. Checks recorded for earlier versions apply to those versions. The [pre-revision snapshot](https://github.com/Einsamake/maj-random-if-equal-lean/tree/f3dc0ba5495c78e238c2e58a1f6b040a936df0c0) contains the original text and its reader feedback. Hashes of documents and figures in earlier verification files identify the exact versions checked in those reviews.

[SNAPSHOT_MANIFEST.json](../SNAPSHOT_MANIFEST.json) inventories a previous release snapshot. Some documents, JSON files and logs had local machine paths redacted for publication. The `workspace_sha256` field identifies the original local file, and `sha256` identifies the published file. The digests may differ. The mathematical sources were preserved byte for byte. The document digests in the manifest still refer to the archived versions. See [verification and reproduction](VERIFICATION.md) for the documentation checks and the mathematical source comparison.

<a id="历史材料"></a>

## Historical material

These records retain their original wording and language. Interpret phase-specific conclusions as of the dates recorded.

| Material | Scope |
| --- | --- |
| `formal/PROGRESS_*.md` | Proof progress by phase, including intermediate dependencies that were still open at the time |
| `formal/audit/` | Builds, axiom outputs, source hashes and independent AI reviews. The `history/` directory contains earlier versions. |
| `research/followup/` | Method notes, proposed approaches and literature searches as of the recorded dates |
| Phase-specific `notes/`, `evidence/` and reader feedback | Drafts, worked examples, actual outputs and the versions read |
| `research/exploration/phase1-overview.md` | Record of the first research phase |
| Sealed archives in `deliverables/` | Fixed deliverables identified by their accompanying inventories |

For the current exposition, see the [theorems](RESEARCH_RESULTS.md), [proof outline](PROOF_GUIDE.md) and [verification records](VERIFICATION.md). The historical material traces how the results and their verification developed.

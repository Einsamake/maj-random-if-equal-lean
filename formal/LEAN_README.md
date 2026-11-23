# Lean project guide

[中文](LEAN_README.zh-CN.md) · [Formalization and audits](README.md)

This directory formalizes the two-dimensional synchronous four-neighbour majority rule with independent fair tie breaking. The original quadratic-order theorem is in [OriginalQuadraticRecovery](analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean). [OriginalRecoveryProfile](analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean) defines the worst extended expected recovery time over deterministic initial perturbations of exact size, measured by their smallest enclosing square.

The October 26 development contains 267 project Lean source files, with 8 in the deterministic core and 259 in the probability analysis project. The final October 26 check rebuilt and audited the analysis project. It verified the core source fingerprints against the existing core audit. Later results have their own build records. [Build and audit guide](../docs/VERIFICATION.md)

| Project | Lean version | Pinned configuration |
| --- | --- | --- |
| Deterministic core in `formal/` | `4.35.0` | [Toolchain](lean-toolchain) · [Lake configuration](lakefile.toml) · [Dependency lock](lake-manifest.json) |
| Probability analysis in `formal/analysis/` | `4.35.0-rc4` | [Toolchain](analysis/lean-toolchain) · [Dependency lock](analysis/lake-manifest.json) |

Use the pinned compiler and dependency versions for each project. For the mathematical statements, proof dependencies and historical records, see [research results](../docs/RESEARCH_RESULTS.md), [formalization map](FORMALIZATION_MAP.md) and [archival record](../docs/ARCHIVAL_RECORD.md).

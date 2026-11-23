# Formal verification and reproduction

[简体中文](VERIFICATION.zh-CN.md)

<a id="形式化验证与复现"></a>

<a id="当前修订的验证入口"></a>

## Verification record for the 17 November revision

The [validation record](../research/revision-ab-2026-11-17/validation.json) for the 17 November 2026 A/B revision covers recompilation of the original 267 project source files, 58 named declarations in five new modules and 47 declarations in two modules used by the strengthened lower bound. The combined audit used standard Lean with `--trust=0`. The reported axioms were drawn from `propext`, `Classical.choice` and `Quot.sound`. The run used the already installed, pinned external Lean and mathlib dependencies.

For the upper and lower bounds, block tails and moment results in the original synchronous model, see [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean). The filled-square extremum appears in [OriginalRecoveryResults.lean](../research/revision-ab-2026-11-17/lean/OriginalRecoveryResults.lean). The [unified build record](../research/revision-ab-2026-11-17/evidence/unified-build.json), [rebuild of the original project](../research/revision-ab-2026-11-17/evidence/base-replay/replay.json) and [independent final verification record](../research/revision-ab-2026-11-17/evidence/independent-final-binding.json) give the commands, outputs and file hashes. Adapt the absolute paths in those records to your installation when reproducing the checks.

<a id="11-月-19-日下界补充"></a>

## Lower-bound supplement of 19 November

The [replay script](../research/lower-bounds-2026-11-19/replay.py) uses the pinned Lean version `4.35.0-rc4`. First build `formal/analysis` as described below. From the repository root, run `python research/lower-bounds-2026-11-19/replay.py` and use `--lean` to specify the path to that version of the compiler. The script recompiles four prerequisite modules, the fifteen mathematical modules included in this audit and the audit entry point. It reuses the built analysis library and mathlib. The [axiom log](../research/lower-bounds-2026-11-19/evidence/LowerAudit.log) reports 377 entries. See the [validation record](../research/lower-bounds-2026-11-19/evidence/validation.json) for details.

<a id="原封存版本的内核检查"></a>

## Kernel checks of the original archived release

The main theorem is `MathResearchAnalysis.OriginalQuadraticRecovery.tau_theta_quadratic`. The [analysis validation record of 26 October 2026](../formal/audit/analysis-validation.json) reports a successful build of all 259 analysis source files and exit code 0 for `lake env lean --trust=0 AnalysisAxioms.lean`. The axioms reported for the 3,280 analysis theorems checked were drawn from `propext`, `Classical.choice` and `Quot.sound`.

Eight additional core source files use a separate toolchain. In the final phase, their source hashes were matched to the existing [core audit](../formal/audit/core-validation.json). The final verification therefore combines a fresh analysis build with an earlier core audit tied to the matching sources. The [independent final verification record](../formal/audit/original-theta-independent-final-binding-evidence.json) covers 267 formal source files and 3,406 axiom outputs.

| Project | Lean version | Dependencies |
| --- | --- | --- |
| `formal/analysis/` | `4.35.0-rc4` | mathlib commit `54c01c3314d33d15d77893cbe4e0472ff26bb34d` |
| `formal/` | `4.35.0` | As specified by the project's `lakefile` and lockfiles |

The [analysis toolchain file](../formal/analysis/lean-toolchain) and the [core toolchain file](../formal/lean-toolchain) pin their respective versions. Build each project using the artifacts produced by its own Lean version.

<a id="在独立检出中复现"></a>

## Reproducing the checks in a separate checkout

Install the corresponding Lean and Lake versions and restore the pinned dependencies. From the repository root, run the analysis build and audit as follows.

```text
cd formal/analysis
lake build
lake env lean --trust=0 AnalysisAxioms.lean
```

Use the specified core toolchain in the separate core directory. Start these commands from the repository root as well.

```text
cd formal
lake build
lake env lean --trust=0 audit/CoreAxioms.lean
```

Install the compilers separately. An initial build needs to fetch the locked dependencies and verify that their versions match those specified by the project sources.

`formal/scripts/validate_analysis.py` and `formal/scripts/validate_core.py` were written for the original Windows workspace. They expect the compiler paths under `formal/.tools/`. For a different installation layout, use the Lake commands above or adapt the local script paths. The scripts write audit outputs, so run them in a separate checkout to preserve the archived records.

<a id="文档与历史证据"></a>

## Documentation and historical evidence

Documentation revisions and mathematical builds have separate records. Document hashes in earlier validation JSON files identify the versions they checked. The [archival record](ARCHIVAL_RECORD.md) explains how to interpret those records.

Kernel checks apply to specific formal declarations and their dependencies. An [independent AI semantic review](../formal/audit/original-theta-independent-review.md) (in Chinese) examined the correspondence to the original model. AI agents simulated readers with undergraduate mathematics backgrounds to review the readability of the original documentation. The 17 November documentation review simulated readers with research backgrounds in probability and stochastic processes. The [reader-review record](mathematical-introduction-2026-11-17/README.md) (in Chinese) preserves their feedback and file hashes. See [references and sources](REFERENCES.md) for the literature citations.

<a id="当前文稿的只读检查"></a>

## Read-only checks for the 17 November documentation edition

Use a Git checkout of the [recorded documentation edition](https://github.com/Einsamake/maj-random-if-equal-lean/tree/b7d63f9f573e460d62576e6823104eee38ec643f) with the baseline commit in its history. From the repository root, run the following command.

```text
python scripts/check_documentation.py
```

The script uses the [edition's manifest](mathematical-introduction-2026-11-17/documentation-manifest.json) to check that edition's documents and links, the 267 formal source files, 54 research Lean sources and the original archive bytes. It also recomputes the listed finite examples. These are file and arithmetic checks. The same edition separately checked all 372 files in the accepted A/B snapshot. Its [review and verification notes](mathematical-introduction-2026-11-17/README.md) (in Chinese) record the results and independent simulated-reader feedback. The [earlier publication manifest](ab-publication-2026-11-17/documentation-manifest.json) and preceding manifests remain tied to their historical editions. For current mathematical documents, use the [documentation index](INDEX.md).

<a id="2026-11-17-ab修订审计"></a>

## A/B revision audit of 17 November 2026

The [validation record](../research/revision-ab-2026-11-17/validation.json) reports that the original 267 unmodified project sources were recompiled. A combined audit using standard Lean with `--trust=0` covered 58 declarations in five new modules and 47 declarations in two modules used by the strengthened lower bound. The external pinned dependencies came from the existing installation. A separate AI review examined the manuscript's meaning and matched its evidence to actual outputs by file hash. The user cancelled the simulated-reader review for this revision. The public directories preserve the accepted files and original command record. Absolute paths describe the historical environment and must be adapted for local reproduction. Publication checks compared the accepted files with the repository. The Lean run is documented in the earlier validation record.

# Repository status

**English** | [简体中文](STATUS.zh-CN.md)

The public repository contains the original quadratic recovery theorem, the A/B revisions, the [C1/C2 alternative proofs](research/manuscript/quadratic-recovery-v6/C1-C2-verification.md), and the [November 19 supplement on lower bounds and earliest extinction](research/README.md#lower-bounds-and-earliest-extinction). The [archived revision 6 manuscript](research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) is a 60-page English working draft. The [research results](docs/RESEARCH_RESULTS.md) identify which statements appear in that manuscript and which are proved in later supplements.

## Synchronous random majority dynamics

For the four-neighbour synchronous rule with fair ties,

$$
N^2/850000 \le \tau(N) \le 664066N^2\qquad(N\ge16).
$$

The lower bound holds for every integer $N\ge1$. Here $N$ is the side length of the smallest translated square enclosing the perturbation, counted in lattice sites. The worst expectation is over all deterministic perturbations of size exactly $N$, in either homogeneous background. The results also identify the filled square as an extremizer and give block-tail bounds, bounds for each fixed positive moment, and a uniform exponential moment on the quadratic scale.

The [original October 26 release](deliverables/README.md) retains its 267 Lean source files and its original lower bound $N^2/56623104000$ for $N\ge786432000$. The November 17 A/B manuscript incorporates a stronger bound first established in the phase 2 work and contains its own proof and audit records. The November 19 lower bound is a separate supplement; the archived PDF retains the constants it originally stated. See [Verification](docs/VERIFICATION.md) for the exact scope of each run.

The dated A/B README, checkpoint, and run records retain their original wording as historical files. [PR #6](https://github.com/Einsamake/maj-random-if-equal-lean/pull/6) records publication of those materials, and [PR #9](https://github.com/Einsamake/maj-random-if-equal-lean/pull/9) records integration of C1 and C2.

## Stochastic waiting network

The public network material ends at [phase 12](research/exploration/phase12/validation.json) and covers random waiting representations, comparison of parameters, identification from observed completion times, and route-marker rules. See the [result statements](docs/RESEARCH_RESULTS.md#stochastic-waiting-network) and the [research index](research/README.md). Work from phases 13–19A is outside this public release.

The [documentation index](docs/INDEX.md) lists English entry points and Chinese counterparts. Dated evidence, sealed releases, and mathematical source files retain their published versions.

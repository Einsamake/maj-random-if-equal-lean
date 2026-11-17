# Recovery time for a two-dimensional random majority cellular automaton

[中文](README.md) | **English**

This repository studies synchronous four-neighbour majority dynamics on the integer lattice and proves that the worst-case expected recovery time from a finite perturbation has quadratic order. The model is the random tie-breaking majority rule considered by Fatès, Marcovici and Taati; see [reference [1], §4.2 and Question 7.4](docs/REFERENCES.md#fates-marcovici-taati-2022).

## Model and main theorem

Each site has colour $0$ or $1$. At every round, all sites update simultaneously using the colours of their four neighbours—above, below, left and right—from the preceding round. A strict majority determines the new colour. In a two-against-two tie, either colour is chosen with probability $1/2$. Tie-breaking choices are independent across sites and rounds. The site itself does not vote.

The initial configuration is a finite set $A\subset\mathbb Z^2$ of sites whose colour differs from a homogeneous background. Let $s(A)$ be the side length of the smallest translated axis-parallel lattice square containing $A$, counted in lattice sites along a side. For example, $s(\{(0,0),(2,1)\})=3$, although this set has only two sites. Let $T_A$ be the first round at which the original homogeneous background is restored, with $T_A=\infty$ if recovery never occurs. Define

$$
\tau(N)=\sup_{s(A)=N}\mathbb E[T_A]\in[0,\infty].
$$

The initial configuration is deterministic; the expectation is over the tie-breaking randomness. Translation invariance and colour symmetry reduce this supremum to a finite nonempty family of normalized patterns, so the supremum is attained. Both background colours are included. Full definitions and the attainment argument appear in [Model and notation](docs/NOTATION.md) (in Chinese).

**Theorem.** For every integer $N\ge786432000$,

$$
\frac{N^2}{56623104000}\le\tau(N)\le664066N^2.
$$

The upper bound alone holds for $N\ge16$. Thus there exist positive constants $c,C$, independent of $N$, and a finite threshold $N_0$ such that $cN^2\le\tau(N)\le CN^2$ for all $N\ge N_0$; equivalently, $\tau(N)=\Theta(N^2)$.

A filled square witnesses the lower bound. The upper bound applies to every finite perturbation whose smallest enclosing-square side length is exactly $N$. The lower-bound proof uses a weighted-area estimate for an auxiliary clock process; the upper-bound proof uses a particle representation of staircase boundaries, heat decay and a restart tail bound. The [proof outline](docs/PROOF_GUIDE.md) describes the reductions and the explicit constants. The formal theorem is `tau_theta_quadratic` in [OriginalQuadraticRecovery.lean](formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean).

A separate subsequent proof improves the explicit lower bound to

$$
\tau(N)\ge\frac{N^2}{576000000}\qquad(N\ge500001).
$$

This result is in [ImprovedOriginalLower.lean](research/exploration/phase2/lean/ImprovedOriginalLower.lean) and is retained separately from the original main theorem.

## Revision of 17 November 2026

A1–A3 and B1–B3 are complete. The revision integrates the strengthened lower bound and formalizes the full-square extremizer, retained block failure rate, positive moments and exponential integrability for the original model. See the [60-page manuscript](research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) and [revision and audit records](research/revision-ab-2026-11-17/README.md). C1 and C2 remain [reserved for collaborators](docs/collaborator-handoff-2026-11-14/TASKS.md).

## Related results and materials

The repository also contains an independent stochastic waiting network, studied through a probabilistic representation of its output response, parameter comparisons and the effect of the observed variables on binary discrimination. Its model, assumptions and theorems are given in [Research results](docs/RESEARCH_RESULTS.md). It is a different mathematical object from the cellular automaton above.

The detailed expositions linked below are currently in Chinese. Lean sources and verification commands are available through the same links from both README versions.

| Content | Entry point |
| --- | --- |
| Model, size, recovery time and worst-case expectation | [Model and notation](docs/NOTATION.md) |
| Main theorem and waiting-network results | [Research results](docs/RESEARCH_RESULTS.md) |
| Main steps in the quadratic lower and upper bounds | [Proof outline](docs/PROOF_GUIDE.md) |
| Toolchains, builds and archived audit records | [Verification](docs/VERIFICATION.md) |
| Scope of the published materials | [Version status](STATUS.md) |
| References | [References](docs/REFERENCES.md) |
| Proof methods, figures and examples | [Notes on proof methods](docs/proof-discovery/README.md) |

Formal mathematical sources, historical audits and sealed materials retain their respective versions. The objects, dates and conclusions of the archived checks are specified in [Verification](docs/VERIFICATION.md); earlier materials are listed in the [archival index](docs/ARCHIVAL_RECORD.md).

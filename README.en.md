# Recovery time for a two-dimensional random majority cellular automaton

[中文](README.md) | **English**

This repository gives quadratic recovery-time bounds for synchronous random majority dynamics on the square lattice, with a mathematical manuscript and a Lean formalization. The question is how the worst expected recovery time grows with $N$, the side length of the smallest square enclosing the initial perturbation. The worst expected recovery time satisfies $\tau(N)=\Theta(N^2)$, the quadratic order proposed by Fatès, Marcovici and Taati in [Question 7.4](docs/REFERENCES.md#fates-marcovici-taati-2022).

## Model and question

Each site of $\mathbb Z^2$ has colour $0$ or $1$. At each round, all sites simultaneously read their four nearest neighbours from the preceding round. A strict majority determines the new colour; a two-against-two tie is resolved by a fair coin. The centre site does not vote. The coins are independent across sites and rounds.

The initial state is a deterministic finite set $A$ of sites whose colour differs from either homogeneous background. Write

$$
Q_N=\{0,\ldots,N-1\}^2,\qquad
s(A)=\min\{N\in\mathbb N_0:\exists z\in\mathbb Z^2,\ A\subset z+Q_N\}.
$$

Here $\mathbb N_0$ denotes the nonnegative integers and $Q_0=\varnothing$. Side length counts lattice sites: $s(\{(0,0),(2,1)\})=3$. Let $T_A$ be the first round at which the original background is restored, with $T_A=\infty$ if recovery never occurs, and set

$$
\tau(N)=\sup_{s(A)=N}\mathbb E T_A\in[0,\infty].
$$

The expectation is over the tie-breaking coins. The supremum includes both backgrounds and all deterministic initial states of size exactly $N$. Full definitions appear in [Model and notation](docs/NOTATION.md) (in Chinese).

## Main results

For every integer $N\ge500001$,

$$
\frac{N^2}{576000000}\le\tau(N)\le664066N^2.
$$

The upper bound holds for every $N\ge16$. Thus the worst expected recovery time has quadratic order. For $N\ge2$, the filled square attains the extremum:

$$
\tau(N)=\mathbb E T_{Q_N}.
$$

Here $T_{Q_N}$ is the recovery time of the filled $N\times N$ perturbation in a zero background; colour symmetry gives the same conclusion for the other background.

The distributional bounds hold uniformly over the permitted initial states of size $s(A)=N$. Put

$$
b_N=331776N^2+257,\qquad
a_N=\frac{32}{8N+1}+\frac{12}{5}N^2\,2^{-(1296N^2+1)}.
$$

For $N\ge16$ and every integer $j\ge0$,

$$
\mathbb P(T_A>jb_N)\le a_N^j,\qquad
0\le a_N\le\min\{1/2,5/N\},\qquad
\tau(N)\le\frac{b_N}{1-a_N}.
$$

Recovery by the explicit quadratic deadline $b_N$ therefore has probability tending uniformly to one. For every fixed real $r>0$, the same range of $N$ and initial states satisfies $\mathbb E T_A^r\le C_rN^{2r}$; for $0<\lambda<\log(2)/332033$,

$$
\sup_{N\ge16}\ \sup_{s(A)=N}
\mathbb E\exp(\lambda T_A/N^2)<\infty.
$$

See [Research results](docs/RESEARCH_RESULTS.md) for constants and formal declarations. These are the results of the revision dated 17 November 2026. The original archived theorem has a weaker explicit lower bound; both versions are retained.

## Proof strategy

Majority updates are monotone under common tie-breaking marks. A perturbation cannot spread beyond its initial enclosing square, so every initial state is dominated by the filled square in the same background. This gives the extremizer and reduces the infinite-lattice problem to a finite square with fixed background boundary.

Both estimates use a continuous-time auxiliary process in which sites update singly at independent rate-one Poisson clocks. For the lower bound, take a clipped region inside a square of side $2L+1$, where $L=\lfloor(N-1)/2\rfloor$ is of order $N$. A modified process admits additional deletions and is frozen when a site of a protected region first loses its perturbation colour. These operations control its geometry. Protected loss requires $\Omega(L^3)$ missing weighted area, whereas the weighted-loss drift from the raw updates is at most $O(L)$ and the total weighted cost of additional deletions is $O(L^2)$. Extinction of the original clock process implies protected loss, so the area balance gives a positive probability that the original clock process survives for time of order $L^2$.

For the upper bound, an auxiliary square has zero south and west boundary values and unit north and east boundary values, starting from the filled state. Its interface remains a staircase. Corner flips correspond to adjacent particle exchanges at rate $1/2$ on a finite one-dimensional path. The discrete heat equation controls the particle density, and nonpositive covariances at distinct sites control count fluctuations. Together they give a lower bound on the probability that a specified corner region is empty after $O(N^2)$ physical time. A monotone coupling transfers this event to the target zero-boundary square.

Censoring comparisons and probability bounds for the random update schedule transfer these continuous-time estimates to synchronous rounds. Conditional restart from the state observed at the end of each block then gives the geometric tail above. The [proof outline](docs/PROOF_GUIDE.md) explains how the estimates connect; the [English manuscript](research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) gives the full argument.

## Reading and reproduction

| Content | Entry point |
| --- | --- |
| Current manuscript | [60-page English PDF](research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) · [Text and six figures](research/revision-ab-2026-11-17/paper/paper.md) |
| Definitions, theorems and proof structure | [Model and notation](docs/NOTATION.md) · [Research results](docs/RESEARCH_RESULTS.md) · [Proof outline](docs/PROOF_GUIDE.md) |
| Formalization and reproduction | [Toolchains, builds and audits](docs/VERIFICATION.md) · [Current theorem source](research/revision-ab-2026-11-17/lean/OriginalConsequences.lean) |
| References and versions | [References](docs/REFERENCES.md) · [Version status](STATUS.md) · [Archival index](docs/ARCHIVAL_RECORD.md) |

The detailed documentation pages in this table are in Chinese. The manuscript is in English. Standard Lean kernel build and axiom-audit records cover the original proof and the additional results; the verification page identifies their exact scope and versions. The current manuscript is a working draft.

The repository also contains [parameter-comparison and statistical-identification results for a stochastic waiting network](docs/RESEARCH_RESULTS.md#随机等待网络). That part has its own model and proof entries, organized separately from the lattice recovery theorem.

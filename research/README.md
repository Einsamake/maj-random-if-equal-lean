# Research

[中文](README.zh-CN.md) · [Repository home](../README.md) · [Lean and audits](../formal/README.md)

## Synchronous majority dynamics

On the infinite square lattice, each site reads its four nearest neighbours from the previous round and takes their majority. Every tie uses a fair coin independent across sites and rounds. Start from a deterministic configuration that differs from an all-zero or all-one background at finitely many sites. Its size is the side length, counted in lattice sites, of the smallest translated axis-parallel square containing the difference. Write $T_x$ for the first round at which all sites are again in their original background state and set $T_x=\infty$ if that never occurs. The function $\tau(N)$ is the supremum of the extended expectations $\mathbb E[T_x]$ over initial configurations of size exactly $N$ and either background. Write $T_N$ for the recovery time from a filled $N\times N$ square of ones surrounded by zeros.

### Lower bounds and earliest extinction

The November 19 supplement gives the following bound for every integer $N\ge1$.

$$
\tau(N)\ge\mathbb E[T_N]\ge\max\{m_N,N^2/850000\},
\qquad
m_N=1+2\left\lfloor\frac{N-1}{2}\right\rfloor .
$$

For the filled square, the earliest possible recovery round is $m_N$. Every trajectory from that square survives through round $m_N-1$, and recovery in round $m_N$ has probability at least $2^{-2N^2}$. The maximum distance from a square site to its nearest corner is $m_N-1$, counting horizontal and vertical steps. A site survives through its distance in rounds under arbitrary tie outcomes. If all ties choose zero in this filled-square evolution, a site first turns zero in the following round. For example, a filled $4\times4$ square has maximum distance $2$, so its earliest recovery is in round $3$. For $q_N=\mathbb P(T_N=m_N)$, the odd- and even-side arguments give the common bound $q_N\le 2^{-\lfloor N^2/8\rfloor}$ when $N\ge7$. [Earliest recovery and its probability (Chinese)](lower-bounds-2026-11-19/earliest.md) · [Lean proof of the earliest round](lower-bounds-2026-11-19/EarliestSquare.lean) · [Lean proof of positive probability](lower-bounds-2026-11-19/EarliestAtom.lean) · [Lean probability upper bounds](lower-bounds-2026-11-19/MinimumAtomUpper.lean)

For $c=(\log 2)/64{,}000{,}000$ and all nonnegative integer rounds $k$,

$$
\mathbb P(T_N\le k)\le 2\exp\!\left(-\frac{cN^2}{k+1}\right),
\qquad
\mathbb E\exp\!\left(\frac{cN^2}{2(T_N+1)}\right)\le 3 .
$$

Here $\log$ is the natural logarithm, and the fraction inside the expectation is zero at infinite recovery time. Separate sub-squares with fixed zero boundaries use disjoint sets of coins. Reuse those coins in the full process. With a fixed tie outcome, changing a neighbour from zero to one can only increase the updated value. Thus any site occupied at a given round in a sub-square is also occupied at that round in the full process. If the full square recovers by round $k$, all the independent sub-squares must have recovered by that round, so their recovery probabilities can be multiplied. The early-recovery estimate applies to the filled square and implies $\mathbb P(T_N\le k_N)\to0$ for every nonnegative integer sequence $k_N$ with $k_N/N^2\to0$. A separate estimate sums survival probabilities and gives $\liminf_{N\to\infty}\mathbb E[T_N]/N^2\ge 1/(1{,}152{,}000\log2)$. [Lower-tail proof (Chinese)](lower-bounds-2026-11-19/lower-tail.md) · [Lean early-recovery bound](lower-bounds-2026-11-19/FastTail.lean) · [Lean all-size quadratic bound](lower-bounds-2026-11-19/AllScaleLower.lean) · [Audit record](lower-bounds-2026-11-19/evidence/validation.json)

### November 18 lower bound

The earlier supplement gives $\tau(N)\ge\mathbb E[T_N]\ge\max\{N/2,N^2/1{,}900{,}000\}$ for every integer $N\ge1$, together with the filled-square early-recovery bound. Its linear term follows from the fact that the state of a site after $k$ rounds depends only on sites at distance at most $k$ in the initial configuration. The quadratic term comes from counting the weight missing at the first loss of an interior region. [November 18 overview (Chinese)](lower-bounds-2026-11-18/README.md) · [Proof note (Chinese)](lower-bounds-2026-11-18/lower-bound.md) · [Lean expectation bound](lower-bounds-2026-11-18/ImprovedMean.lean) · [Audit record](lower-bounds-2026-11-18/evidence/validation.json)

### Revision 6 and the A/B results

The English working paper presents the original synchronous proof and connects its steps to Lean. It proves $N^2/576{,}000{,}000\le\tau(N)\le664{,}066N^2$ for $N\ge500{,}001$, with the upper bound valid for $N\ge16$. The filled square attains the worst expectation for $N\ge2$. For every permitted deterministic initial configuration of size $N\ge16$, the working paper gives $\mathbb P(T_x>j b_N)\le 2^{-j}$ for integers $j\ge0$, where $b_N=331{,}776N^2+257$. The paper retains a sharper probability bound for failure in one block, which yields a sharper expectation bound. The block tail also bounds all fixed positive moments and gives a uniform bound on $\mathbb E[\exp(\lambda T_x/N^2)]$ for each $0<\lambda<\log(2)/332{,}033$. [Working paper PDF (English)](revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) · [Editable paper (English)](revision-ab-2026-11-17/paper/paper.md) · [A/B revision notes (Chinese)](revision-ab-2026-11-17/README.md) · [Audit record](revision-ab-2026-11-17/validation.json)

### C1 and C2 alternative proof routes

- **C1** obtains quadratic bounds by transferring an odd-side continuous-time Ising extinction window to synchronous rounds, with even sides bracketed by odd sides. The Lean theorem takes the clock window as an explicit hypothesis. The paper addendum identifies the literature result used for that input. [C1 addendum (English)](manuscript/quadratic-recovery-v6/C1-clock-literature.md) · [Lean transfer theorem](../formal/analysis/MathResearchAnalysis/ClockLiteratureTransfer.lean)
- **C2** uses a first-moment estimate and restarts the original clock process at deterministic times. Transferring the resulting estimate to synchronous rounds gives $\tau(N)\le 2{,}322{,}432N^2+514$ for every $N\ge16$. [C2 addendum (English)](manuscript/quadratic-recovery-v6/C2-first-moment-upper.md) · [Lean upper bound](../formal/analysis/MathResearchAnalysis/FirstMomentClockUpper.lean)

Both are published as separate addenda. [C1 and C2 verification (English)](manuscript/quadratic-recovery-v6/C1-C2-verification.md)

## Stochastic waiting network

The three-node network has fixed rates $a,b>0$, $e,f\ge0$, and $e+f>0$. For one task, draw independent exponential waits $W_a,W_b,W_c$ of rates $a,b,e+f$, respectively, and an independent branch indicator $J$ with $\mathbb P(J=1)=f/(e+f)$. The total completion time is $S=W_a+W_c+J W_b$. The wait at rate $b$ contributes exactly when the task takes that branch. An exponential wait of rate $r$ has mean $1/r$. By independence,

$$
\mathbb E[S]=\frac1a+\frac1{e+f}+\frac{f}{e+f}\frac1b
=\frac1a+\frac{b+f}{b(e+f)}.
$$

The network's output response to a constant unit input from zero initial state equals $\mathbb P(S\le t)$ for $t\ge0$. When $a,b,e$ are fixed and known, the output mean identifies $f$ if $b\ne e$. When $b=e$, the whole output distribution is constant as $f$ varies over the allowed values. [Waiting network overview (Chinese)](exploration/README.md) · [Waiting-time representation (phase 5, Chinese)](exploration/phase5/README.md) · [Response and rate comparison (phase 6, Chinese)](exploration/phase6/README.md) · [Identifiability (phase 7, Chinese)](exploration/phase7/README.md)

The public notes also cover the following results. Their proof prose is in Chinese.

| Topic | Public notes |
| --- | --- |
| Order preservation for directed networks and bounds over allowed coefficients | [Network comparison](exploration/NETWORK_PROOF.md) · [Interval envelope (phase 2)](exploration/phase2/README.md) · [Attained trajectory under ratio bounds (phase 3)](exploration/phase3/README.md) · [Endpoint condition and counterexample (phase 4)](exploration/phase4/README.md) |
| One parameter choice that maximizes completion probability at every deadline in a product of rate intervals | [Rate-box maximum (phase 8)](exploration/phase8/README.md) |
| Bounds on the difference in probabilities between two models | [Deadline events (phase 9)](exploration/phase9/README.md) · [All measurable completion-time events (phase 10)](exploration/phase10/README.md) |
| Testing with repeated completion times or recorded branch indicators | [Completion-time testing (phase 11)](exploration/phase11/README.md) · [Comparison on the same original tasks (phase 12)](exploration/phase12/README.md) |

For the testing example, take $a=e=1$, $b=1.01$, and choose $f=1/2$ or $f=1$ once with equal prior probabilities. Conditional on that choice, generate 100 independent tasks. Any measurable deterministic rule using only the 100 completion times succeeds with average probability at most $353/606\approx58.25\%$. The rule using the actual branch indicators chooses $f=1$ when $\sum_{i=1}^{100} J_i\ge 5(100)/12$ and $f=1/2$ otherwise. Since $5(100)/12=125/3$, this means choosing $f=1$ for 42 or more branch marks. The rule succeeds with average probability at least $33/50=66\%$. In this experiment its success probability exceeds that of any such completion-time rule by at least $587/7575$, about 7.75 percentage points. [Phase 12 Lean theorem](exploration/phase12/lean/ObservationContrast.lean) · [Phase 12 audit](exploration/phase12/validation.json)

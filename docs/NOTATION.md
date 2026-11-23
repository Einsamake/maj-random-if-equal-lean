# Model and notation

**English** · [简体中文](NOTATION.zh-CN.md)

## Synchronous random majority rule

The sites are the points of $\mathbb Z^2$, and a configuration is a function $x:\mathbb Z^2\to\{0,1\}$. For $v=(v_1,v_2)$, let

$$
\mathcal N(v)=\{v+(1,0),v-(1,0),v+(0,1),v-(0,1)\}.
$$

Given an initial state $X_0=x$, let $\xi_{t,v}$ ($t\ge1$, $v\in\mathbb Z^2$) be independent fair $\{0,1\}$-valued random variables. Write $k_t(v)=\sum_{u\in\mathcal N(v)}X_t(u)$. The update rule is

$$
X_{t+1}(v)=
\begin{cases}
0,&k_t(v)<2,\\
\xi_{t+1,v},&k_t(v)=2,\\
1,&k_t(v)>2.
\end{cases}
$$

All sites update simultaneously. Only the four neighbours vote. A random mark is available at every site and round, and the rule uses it only on a tie. The [rule diagram (Chinese labels)](images/01-rule.png) shows, from left to right, a majority of black neighbours, a majority of white neighbours and a tie. Black denotes $1$ and white denotes $0$.

See `majority4` and `synchronous` in [InfiniteGridModel.lean](../formal/analysis/MathResearchAnalysis/InfiniteGridModel.lean) and the law of the independent marks in [InfiniteGridRandomDynamics.lean](../formal/analysis/MathResearchAnalysis/InfiniteGridRandomDynamics.lean).

## Finite perturbations and their size

Fix a background colour $b\in\{0,1\}$. The sites at which $x$ differs from the background form the set

$$A_b(x)=\{v\in\mathbb Z^2:x(v)\ne b\}.$$

The recovery-time theorems concern initial states with finite $A_b(x)$. Let $\mathbb N_0=\{0,1,2,\ldots\}$ denote the nonnegative integers. For a finite set $A$, define

$$
Q_N=\{0,\ldots,N-1\}^2,\qquad
s(A)=\min\{N\in\mathbb N_0:\exists a\in\mathbb Z^2,\ A\subset a+Q_N\}.
$$

Take $Q_0=\varnothing$, so $s(\varnothing)=0$. For $A\ne\varnothing$,

$$
s(A)=1+\max\left\{
\max_{v\in A}v_1-\min_{v\in A}v_1,
\max_{v\in A}v_2-\min_{v\in A}v_2
\right\}.
$$

The size counts the lattice sites along a side of the smallest enclosing square. For $A=\{(0,0),(2,1)\}$, the coordinate spans are $2$ and $1$, so $s(A)=3$. A singleton has size $1$. The declaration `diameter` uses the same definition in [PerturbationGeometry.lean](../formal/analysis/MathResearchAnalysis/PerturbationGeometry.lean). It takes the value $\infty$ for sets that fit in no finite square, so specifying a finite size excludes those sets.

## Recovery time and extended expectation

Write $\mathbf0,\mathbf1$ for the two constant configurations. For a deterministic initial state $x$, define

$$
T_x=\inf\{t\in\mathbb N_0:X_t\in\{\mathbf0,\mathbf1\}\},
\qquad\inf\varnothing=\infty.
$$

If $x$ is a finite perturbation of background $b$, the colour outside a finite enclosing square remains $b$ throughout the evolution. The first constant configuration reached is therefore the original background. Both constant configurations are absorbing, and $T_x=0$ when $x$ is already constant. See the definition and equivalence in [HomogeneousRecoveryTime.lean](../formal/analysis/MathResearchAnalysis/HomogeneousRecoveryTime.lean).

The expectation is a nonnegative extended real number,

$$
\mathbb E[T_x]=\sum_{t=0}^{\infty}\mathbb P(T_x>t)\in[0,\infty].
$$

For $N\in\mathbb N_0$, set

$$
\tau(N)=\sup\{\mathbb E[T_x]:\exists b\in\{0,1\},\ A_b(x)\text{ is finite and }s(A_b(x))=N\}.
$$

The expectation averages over the tie-breaking marks for each deterministic initial state. The supremum runs over the initial states of size exactly $N$.

## Attainment of the maximum

Translating the initial state or swapping the two colours leaves the distribution of the recovery time unchanged. For $N\ge2$, we can therefore restrict the supremum to patterns inside $Q_N$ on the zero background, keeping only patterns of size exactly $N$. There are finitely many such patterns, and the filled square is one of them. A finite nonempty set of extended real numbers has a maximum, including when that maximum is $\infty$.

In [OriginalRecoveryProfile.lean](../formal/analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean), `tau` defines the supremum, and `tau_eq_normalizedTau` and `tau_attained_finite_pattern` establish the reduction and attainment. For $N\ge2$, the internal square parameter is $N-2$, so the actual side length is $(N-2)+2=N$. The declarations `tau_zero` and `tau_one` give

$$\tau(0)=0,\qquad\tau(1)=1.$$

The second equality follows directly from the rule. After one round, the single perturbed site and all its neighbours have the background colour. The declaration `tau_attained_all` covers attainment for every $N\in\mathbb N_0$.

## The filled square attains the maximum

For $N\ge2$,

$$\tau(N)=\mathbb ET_{Q_N}.$$

Here $T_{Q_N}$ is the recovery time when every site of $Q_N$ is $1$ and the background is $0$. Run any pattern inside the same square with the same tie-breaking marks as the filled square. The update is monotone in the four neighbour colours, so the pattern stays pointwise below the process started from the filled square, and it recovers no later. Translation and colour symmetry cover all the initial states in the definition of $\tau(N)$, and the filled square has size exactly $N$. The equality holds for extended expectations. See [OriginalRecoveryResults.lean](../research/revision-ab-2026-11-17/lean/OriginalRecoveryResults.lean).

## Main notation

| Symbol | Meaning |
| --- | --- |
| $N$ | Exact perturbation size in the synchronous model |
| $T_x$ | First round at which the synchronous process reaches a constant configuration, with $\infty$ allowed |
| $\tau(N)$ | Maximum extended expectation at size exactly $N$ |
| $L$ | Parameter for the auxiliary square of side length $2L+1$ in the lower bound |
| $M$ | Side length of the mixed-boundary auxiliary square in the upper bound, with $M=8N+1$ |
| $t$ | Continuous time for the auxiliary clocks |
| $k,b_N$ | Number of scheduling layers and length of a synchronous restart block, respectively |
| $a,b,e,f$ | Rate parameters of the separate waiting network |

The [proof outline](PROOF_GUIDE.md) gives the probability bounds relating continuous clock time to the number of synchronous rounds.

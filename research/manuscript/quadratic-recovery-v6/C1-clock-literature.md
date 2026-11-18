# C1. A short proof via the zero-temperature Ising clock process

Consider the synchronous square-lattice majority process. All sites update in parallel from their four nearest neighbours and use independent fair bits for ties. A deterministic finite perturbation of a homogeneous background has size $N$ if $N$ is the smallest side of a translated axis-parallel square containing the perturbation. Its recovery time is the first round at which the lattice is homogeneous, with value $\infty$ if that never happens. Write $\tau(N)$ for the supremum of the expected recovery times at exact size $N$.

We prove $\tau(N)=\Theta(N^2)$ by combining Theorem 2 of Caputo, Martinelli, Simenhaus and Toninelli (CMST) with Lemma 2 of the project's v5 working draft. The constants in this route depend on the constants in CMST. The proof also gives a two-sided window for the filled-square initial state and a uniform upper tail for all allowed initial patterns.

## Identifying the clock law

Translate and, if necessary, exchange colours so that the perturbation is supported on $Q_N=\{0,\ldots,N-1\}^2$ with zero background. Each exterior site has at most one neighbour in $Q_N$, so the exterior stays zero in synchronous dynamics. Hence finite zero-boundary recovery agrees with infinite-lattice recovery. Write $T_g$ for the synchronous recovery time of a pattern $g$ on $Q_N$, $p_N(r)=\mathbb P(T_{\mathbf1_{Q_N}}>r)$ for the filled-square tail after $r$ rounds, and $C_N(t)$ for the probability that the zero-boundary **clock** process from the filled square is nonzero at time $t$. Zero is absorbing in each process, so being nonzero at a specified time is equivalent to having a recovery time strictly larger than that time.

CMST starts with all minus spins in $\{-L,\ldots,L\}^2$ and fixes plus spins on the exterior neighbour boundary. At inverse temperature $\beta$, the heat-bath probability of a plus spin at a ringing site with neighbour sum $S$ is $e^{\beta S}/(e^{\beta S}+e^{-\beta S})$. This follows from the terms of the Hamiltonian incident to that site. At $\beta=\infty$ it gives the strict majority spin when $S\ne0$ and gives either spin with probability $1/2$ when $S=0$. Fresh fair bits therefore realize the heat-bath updates at ties. Together with the clocks, this identifies the law of the two processes. [CMST, §2](https://arxiv.org/html/1007.3599v2#S2)

| Item | CMST | Zero-boundary clock process in v5 |
| --- | --- | --- |
| State and initial condition | Spin $\sigma\in\{-1,+1\}$, initially all minus | Set $x=(1-\sigma)/2$, so the square starts filled with ones |
| Sites and translation | $\{-L,\ldots,L\}^2$ | Add $(L,L)$ to get $Q_{2L+1}$ |
| Four-neighbour update | Zero-temperature heat bath | The four neighbours vote, with a fair bit in a tie |
| Exterior | Plus at each exterior neighbour | Zero at each exterior neighbour. All other exterior sites may also be set to zero |
| Clocks | An independent rate-one Poisson clock per site | Independent rate-one exponential interarrival gaps per site, with the same Poisson law |
| Time and recovery | Physical time, first all-plus time $\tau_+$ | Same physical time and first all-zero time. The rate is measured per site |
| Side lengths | Odd $2L+1$ for $L\ge1$ | Odd sides match exactly. Even sides use the coupling below |

For $L\ge1$, CMST supplies constants $c,\gamma>0$, independent of $L$, such that under this clock law the probability of a recovery time in $[cL^2,L^2/c]$ is at least $1-e^{-\gamma L}$. We may decrease $c$ to ensure $c\le1$. Thus
$$
C_{2L+1}(t)\ge 1-e^{-\gamma L}\quad (0\le t<cL^2),
\qquad
C_{2L+1}(t)\le e^{-\gamma L}\quad (t\ge L^2/c).
\tag{C1.1}
$$
The strict time restriction in the first inequality follows from the closed lower endpoint of the CMST window and the strict definition of survival. [CMST, §2.1 and Theorem 2](https://arxiv.org/html/1007.3599v2#S3.SS2)

## Comparing odd and even sides

For side lengths $u\le v$, use the clocks and tie bits on $Q_u$ from the larger sample on $Q_v$. Consider the clock processes started from their respective filled squares with zero boundary, and extend the smaller state by zeros on $Q_v\setminus Q_u$. The initial states are ordered. At a ring on $Q_u$, the two processes see ordered inputs and the same tie bit. The update with a fixed bit is nondecreasing in each input, so the order persists. At a ring on $Q_v\setminus Q_u$, the smaller extended value stays zero and the larger updated value is at least zero. On each bounded time interval there are finitely many rings and almost surely no simultaneous rings. Induction on them proves pathwise order for every time. In particular, whenever the larger square is all zero the smaller one is all zero, giving $C_u(t)\le C_v(t)$.

For $N\ge4$, set $L_-=\lfloor (N-1)/2\rfloor$ and $L_+=\lceil (N-1)/2\rceil$. Then
$$
C_{2L_-+1}(t)\le C_N(t)\le C_{2L_++1}(t).
$$
For even $N$, $L_-=N/2-1$ and $L_+=N/2$, so the sides are $N-1$ and $N+1$. For odd $N$, $L_-=L_+=(N-1)/2$, so both sides are $N$. Thus $N/4\le L_-\le L_+\le N/2$ for every $N\ge4$.

## Passing to synchronous rounds

Put $a=8\log 2$, $t_k=a(k+1)$, and $E_N(k)=\frac65N^2 2^{-(k+1)}$. The two directions of the existing bridge in v5, equations (7)–(9), are
$$
C_N(t_k)\le p_N(k)+E_N(k),\qquad
p_N(256(k+1)+1)\le 2C_N(t_k)+2E_N(k)\quad(k\ge0).
$$
The integer $k$ sets the comparison's physical time $t_k$. The first direction compares this time with $k$ parallel rounds. The proof of the second direction uses a conflict rank, which counts the length of a chain of clock updates that must stay in order. On the good scheduling event the rank is bounded by $R_k=128(k+1)$, so the proof can arrange the updates into at most $2R_k$ alternating single-colour scans. The comparison after accounting for both checkerboard phases gives the synchronous index $2R_k+1=256(k+1)+1$. The proof below uses the bridge as an input.

Take
$$
N_0=\left\lceil\max\{16,\ 64a/c,\ 16ca,\ (4/\gamma)\log 8\}\right\rceil
$$
and, for every integer $N\ge N_0$, define the integer indices
$$
k_-=\left\lfloor\frac{cL_-^2}{2a}\right\rfloor-1,\qquad
k_+=\left\lceil\frac{L_+^2}{ca}\right\rceil-1,\qquad
B_N=256(k_++1)+1.
$$
The definition of $N_0$ ensures $k_-+1\ge N$, since $cL_-^2/(2a)\ge cN^2/(32a)\ge 2N$. It also gives $k_++1\ge N$ since $L_+^2/(ca)\ge N^2/(16ca)\ge N$. Thus both bridge indices are nonnegative and both errors satisfy $E_N(k_\pm)\le3/160\le1/8$. Here $2^N\ge64N^2$ holds at $N=16$ and follows inductively thereafter, since $(1+1/N)^2<2$ for $N\ge16$. Also $e^{-\gamma L_\pm}\le1/8$ by the choice of $N_0$.

For the lower bound, $t_{k_-}\le cL_-^2/2<cL_-^2$. The lower odd square, (C1.1), and the first bridge inequality yield
$$
p_N(k_-)\ge 1-e^{-\gamma L_-}-E_N(k_-).
\tag{C1.2}
$$
For the upper bound, $t_{k_+}\ge L_+^2/c$. The upper odd square, (C1.1), and the second bridge inequality yield
$$
p_N(B_N)\le 2e^{-\gamma L_+}+2E_N(k_+)\le \frac12 .
\tag{C1.3}
$$
In particular, for the filled square and every $N\ge N_0$, the probability that $k_-<T_{\mathbf1_{Q_N}}\le B_N$ is at least
$$
1-e^{-\gamma L_-}-2e^{-\gamma L_+}-E_N(k_-)-2E_N(k_+).
$$
The lower estimate uses the filled-square witness. The upper estimate at $B_N$ holds for all initial patterns $g$ on $Q_N$, since common synchronous bits preserve order and the filled square dominates every such pattern.

At a deterministic block boundary $jB_N$, condition on the past. On survival up to that boundary, the current pattern is some $g'$ on $Q_N$ and the next $B_N$ rounds use fresh independent bits. Equation (C1.3) and the domination just proved bound the conditional probability of further survival by $1/2$. After absorption it is zero. Induction gives $\mathbb P(T_g>jB_N)\le2^{-j}$ for each integer $j\ge0$. Summing the extended tail in blocks gives $\mathbb ET_g\le 2B_N$.

Finally $B_N\le (64/(ca))N^2+257$, since $L_+\le N/2$ and $\lceil x\rceil\le x+1$. For the lower scale, $x=cL_-^2/(2a)\ge2N\ge4$, and $\lfloor x\rfloor-1\ge x/2\ge cN^2/(64a)$. Equation (C1.2) gives $p_N(k_-)\ge 1-1/8-1/8\ge1/2$. Since $T_{\mathbf1_{Q_N}}\ge k_-$ on $\{T_{\mathbf1_{Q_N}}>k_-\}$, its expectation is at least $k_-p_N(k_-)\ge cN^2/(128a)$. This pattern has exact side $N$, so for every $N\ge N_0$,
$$
\frac{c}{128a}N^2\ \le\ \tau(N)\ \le\ \left(\frac{128}{ca}+514\right)N^2.
$$

## Sources and placement in the manuscript

| Step | Source |
| --- | --- |
| Model, $\tau_+$, and the odd-side extinction window | [Caputo, Martinelli, Simenhaus and Toninelli, arXiv:1007.3599v2, §2, (2.17) and Theorem 2](https://arxiv.org/html/1007.3599v2#S3.SS2). |
| Normalization, support, and filled-square domination | v5 §2 and Lemma 1. Existing Lean declarations include `OriginalRecoveryProfile.tau_eq_normalizedTau` and `SquareRecoveryTime.synchronous_le_top`. |
| Odd/even zero-boundary comparison | The same-clock argument above. It uses the order-preservation and retained-coordinate mechanism of v5 §7. |
| Clock/synchronous inequalities and block restart | v5 Lemmas 2 and 6. Existing Lean declarations include `SquareRecoveryTime.two_way_clock_tail` and `OriginalQuadraticUpper.recovery_block_tail`. The latter uses the original v5 block scale. |
| Round window and C1 bounds on $\tau(N)$ | Equations (C1.1)–(C1.3) and the rounding and tail-sum argument above. |

The v5 references use the handoff manuscript's numbering. The [published A/B revision](https://github.com/Einsamake/maj-random-if-equal-lean/blob/b7d63f9f573e460d62576e6823104eee38ec643f/research/revision-ab-2026-11-17/paper/paper.md) retains the bridge, staircase, and comparison inputs cited here. This paper proof can serve as a short main argument with the existing self-contained route and formal proof in a supplement. If the authors keep the self-contained proof in the main text, this section can instead present the literature-based route and identify the time comparison as the step connecting the two models.


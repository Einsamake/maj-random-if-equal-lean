# C2. A first-moment upper bound with clock restart

For an integer $N\ge16$, let $Q_N=\{0,\ldots,N-1\}^2$ and let $g$ be any deterministic configuration of zeros and ones on it. Outside the square the state is zero. At each synchronous round, each site takes the majority of its four nearest neighbours, with an independent fair bit in a tie. Let $T_g$ be the first round at which the square is all zero, with $T_g=\infty$ if it never clears. Set
$$
k_N=4536N^2,\qquad b_N=256(k_N+1)+1=1{,}161{,}216N^2+257.
$$
Then for every integer $j\ge0$,
$$
\mathbb P(T_g>jb_N)\le 2^{-j},\qquad
\mathbb E T_g\le2b_N=2{,}322{,}432N^2+514.
$$
The same bounds apply to any deterministic finite perturbation of a homogeneous background of enclosing-square side $N$ on the infinite lattice. After exchanging colours if necessary and translating the square, each exterior site has at most one neighbour in the square and remains zero. In particular the supremum $\tau(N)$ of the expected recovery times of perturbations of exact side $N$ satisfies $\tau(N)\le 2b_N$.

## A single clock interval

In the clock version, independent rate-one Poisson clocks ring at the sites. A ring updates its own site by the same rule, with independent fair tie bits. Write $X^g_t$ for the zero-boundary clock process from $g$. Take $M=8N+1$ and $h=16M^2$. The auxiliary clock process on $Q_M$ starts all one, with zero boundary to the south and west and one boundary to the north and east.

The project's v5 working draft shows that the zeros of the auxiliary process have staircase shape (§4.1). Let $\lambda_d$ be the number of zeros in row $d$, counted from the south. The zeros are the leftmost $\lambda_d$ sites of that row and the lengths decrease weakly northward. In the encoding (14), the $M$ particles have positions $P_r=r+\lambda_{M-1-r}$ among slots $0,\ldots,2M-1$. Writing $d=M-1-r$ shows that $P_r\ge M$ exactly when $\lambda_d\ge d+1$, which means that the diagonal cell $(d,d)$ is zero. Thus the count $J(t)$ of particles in the rightmost $M$ slots counts zero diagonal cells. These diagonal cells form an initial segment, and if $J(t)\ge N$, the zero cell $(N-1,N-1)$ forces the whole southwest $N$ by $N$ sub-square to be zero. For example, the three row lengths $2,2,0$ give particle positions $0,3,4$ and hence $J=2$, with a zero southwest $2$ by $2$ square.

The single-slot occupation means diffuse along the path, with average $1/2$ since there are $M$ particles and $2M$ slots. The heat-energy estimate (H4) and the right-half sum estimate (H5) in v5 bound the deficit from $M/2$. At $h=16M^2$ they give $\mathbb E J(h)\ge M/4$ by (H6). Also $0\le J(h)\le M$. With $q=\mathbb P(J(h)\ge M/8)$, bound $J(h)$ above by $M$ on this event and by $M/8$ on its complement. This gives
$$
\frac M4\le\mathbb E J(h)\le \frac M8(1-q)+Mq.
$$
Subtract $M/8$ from both sides and divide by $7M/8$ to obtain $q\ge 1/7$. Since $N\le M/8$, the event being counted ensures the southwest sub-square is zero at $h$.

Identify $Q_N$ with that sub-square. Use the larger process's clocks and bits at sites in $Q_N$ for the smaller process. Restricting the independent coordinates gives the smaller process its prescribed law. The smaller initial pattern is coordinatewise at most the larger pattern on $Q_N$. At each common ring the neighbour values are ordered. Inside $Q_N$ this follows from the current state order. Outside $Q_N$ the smaller process uses zero and the larger input is a bit. The update with a fixed tie bit is nondecreasing in each neighbour, so it preserves order. A ring outside $Q_N$ leaves both restrictions to $Q_N$ unchanged. Apply these steps in chronological order, using the fact that bounded intervals almost surely have finitely many rings with distinct times. This is the comparison of v5 Lemma 5, and it gives the uniform estimate
$$
\mathbb P(X_h^g=\mathbf 0)\ge 1/7 \qquad\text{for every }g.
\tag{C2.1}
$$
The auxiliary event concerns its state at time $h$. All-zero absorption is used below for $X^g$, which has zero boundary on all four sides.

## Restart at deterministic times

Let $\mathcal H_s$ record all arrivals through a deterministic time $s$ and their observed bits. The state $X_s^g$ is a function of this history. Each site's Poisson increments after $s$ are independent of the increments up to $s$, and the clocks at distinct sites are independent. Conditional on the clocks, the used bits are exactly the initial segment at each site whose length is its arrival count through $s$. All later bits have the independent fair product law on every such count event. Thus, after shifting time by $s$, the future marked clocks have the original law independent of $\mathcal H_s$. Equivalently, in the exponential-gap construction, the wait left until the next arrival at each site is a fresh rate-one exponential by memorylessness, and subsequent gaps and unused bits retain their product law. This uses the original sample with time measured from $s$.

Put $s_h(f)=\mathbb P(X_h^f\ne\mathbf0)$. Executing the future rings starting from the observed $X_s^g$ gives, almost surely,
$$
\mathbb P(X_{s+h}^g\ne\mathbf0\mid\mathcal H_s)
=s_h(X_s^g)\le \frac67\,\mathbf1_{\{X_s^g\ne\mathbf0\}}.
\tag{C2.2}
$$
Here (C2.1) bounds $s_h$ on every state, and $s_h(\mathbf0)=0$ by absorption. Taking expectations at $s=ih$ and inducting yields $\mathbb P(X_{ih}^g\ne\mathbf0)\le(6/7)^i$ for every integer $i\ge0$. For $i=14$, $8\cdot6^{14}=626{,}913{,}312{,}768<678{,}223{,}072{,}849=7^{14}$, so the survival probability is below $1/8$.

## From clock time to synchronous rounds

Let $C_N(t)$ be the clock survival probability at time $t$ from the filled square, and write $p_N(r)$ for the synchronous survival probability after $r$ rounds from that same initial pattern. The v5 bridge (7) and (9) takes the form
$$
p_N(256(k+1)+1)\le2C_N(t_k)+2E_N(k),
\quad t_k=8\log 2\,(k+1),\quad E_N(k)=\frac65N^2\,2^{-(k+1)}.
$$
Because $M\le9N$ and $\log 2\ge1/2$,
$$
14h\le14\cdot16\cdot81N^2=18144N^2=4k_N\le t_{k_N}.
$$
The clock survival probability decreases with time by absorption, so $C_N(t_{k_N})<1/8$. The inequality $64N^2\le2^N$ holds at $N=16$. From $N$ to $N+1$ the left side grows by a factor at most $(17/16)^2<2$, so it holds for all $N\ge16$. Since $k_N+1\ge N$,
$$
E_N(k_N)\le \frac65 N^2\,2^{-N}\le \frac3{160}<\frac18.
$$
Consequently $p_N(b_N)\le1/2$. The same inequality holds from every $g$ by order preservation under common synchronous bits and domination by the filled square. At each multiple of $b_N$, condition on all rounds seen so far. The fresh bits and uniform bound imply a conditional chance of survival at the next multiple of at most $1/2$ on survival so far, and zero after absorption. Iteration gives the claimed geometric tail. The extended tail-sum formula groups the integers $r\ge0$ into intervals $jb_N\le r<(j+1)b_N$ and yields $\mathbb E T_g=\sum_{r\ge0}\mathbb P(T_g>r)\le b_N\sum_{j\ge0}2^{-j}=2b_N$.

At $N=16$, $M=129$, $h=266{,}256$, $14h=3{,}727{,}584$, and $k_N=1{,}161{,}216$. The lower bound $4(k_N+1)=4{,}644{,}868$ on $t_{k_N}$ covers the 14 intervals. Here $E_N(k_N)\le (6/5)16^2\,2^{-16}=3/640<1/8$, and $b_N=297{,}271{,}553$ rounds. At this size $M/8=16.125$, so the event used in the first-moment bound is $J(h)ge17$, which implies $J(h)ge16$ as needed.

## Sources and proof dependencies

The argument uses the staircase dynamics and geometry, the one-site moment and heat-energy estimate through (H6), and the clock comparison, bridge, and synchronous restart. In the paper proof of this upper bound, the distinct-site second-moment equation, covariance equation and sign estimate, variance estimate for $J$, and Chebyshev step in (17) can be omitted. The new block length gives a larger upper-bound constant than the original v5 route.

| Step | Source |
| --- | --- |
| Staircase count, local clearing, and $\mathbb E J(h)\ge M/4$ | v5 §§4.1 and 4.3, especially (14)–(15), (H4)–(H6), and (H8). Existing Lean declarations include `MixedLocalClearing.endpoint_localWhite_of_count_le` and `MixedRightCountHeat.mean_at_mixingTime`. |
| Uniform transfer to the original zero-boundary square | v5 Lemma 5 and §7. Existing Lean declaration `CrossSquareClockBound.original_nonzero_probability_le_local_failure`. |
| Conditioned future and clock tail amplification | v5 §4.2.1 gives the deterministic-time clock law. Equations (C2.1)–(C2.2) apply it to the new first-moment bound and its iteration. |
| Synchronous bridge, restart, and tail sum | v5 Lemmas 1, 2, and 6. `SquareRecoveryTime.two_way_clock_tail` gives the bridge. `OriginalQuadraticUpper.recovery_block_tail` supplies the existing restart pattern at the original scale. |

The section and equation references use the v5 handoff manuscript's numbering. The [published A/B revision](https://github.com/Einsamake/maj-random-if-equal-lean/blob/b7d63f9f573e460d62576e6823104eee38ec643f/research/revision-ab-2026-11-17/paper/paper.md) retains (14), (H4)–(H8), and the bridge and retained-clock comparison. Its §3.4 contains the deterministic-time clock law used here. The new clock amplification and changed constants are proved here on paper. The cited Lean files document the existing inputs. In the current Lean import graph, the mean-estimate module still imports the right-count moments module, which imports the covariance module.


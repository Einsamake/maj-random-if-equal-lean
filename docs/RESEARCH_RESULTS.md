# Research results

**English** · [简体中文](RESEARCH_RESULTS.zh-CN.md)

## Recovery time for the synchronous random majority rule

Consider the synchronous four-neighbour majority rule on $\mathbb Z^2$. Ties are broken by fair coins that are independent across sites and rounds. A deterministic initial configuration $x$ is a finite perturbation of either constant background. Its size $s(x)$ is the side length of the smallest axis-aligned square containing the perturbation, counted in lattice sites along a side. The number of rounds until the original background is restored is $T_x\in\mathbb N_0\cup\{\infty\}$, and its worst expected value at size $N$ is

$$\tau(N)=\sup_{s(x)=N}\mathbb ET_x.$$

See [Model and notation](NOTATION.md) for the full definitions. The results below include the filled-square lower bounds established on 19 November 2026.

### Theorem 1 (quadratic bounds and extremizer)

For every integer $N\ge16$,

$$\frac{N^2}{850000}\le\tau(N)\le664066N^2.$$

In particular, $\tau(N)=\Theta(N^2)$. For $N\ge2$, the filled square $Q_N=\{0,\ldots,N-1\}^2$ in a zero background attains the worst expected recovery time,

$$\tau(N)=\mathbb E T_{Q_N}.$$

The extremizer identity holds for nonnegative extended expectations. With common tie-breaking marks, the filled square dominates every pattern inside the same square. Translation and colour symmetry extend the result to all locations and either background. These same comparisons bound the recovery time for $2\le N<16$ by that of the filled square of size $16$, so the upper bound at size $16$ also gives finiteness at those sizes.

For the quadratic bounds in the 17 November version, see `quadratic_bounds` in [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean). For the extremizer identity, see `tau_eq_full_square` in [OriginalRecoveryResults.lean](../research/revision-ab-2026-11-17/lean/OriginalRecoveryResults.lean).

Write $T_N=T_{Q_N}$ and $m_N=1+2\lfloor(N-1)/2\rfloor$. For every $N\ge1$, $\mathbb E T_N\ge\max\{m_N,N^2/850000\}$. The first possible extinction round is $m_N$, which equals $N$ for odd side lengths and $N-1$ for even ones. If $q_N=\mathbb P(T_N=m_N)$, then

$$2^{-2N^2}\le q_N\le 2^{-\lfloor N^2/8\rfloor}\qquad(N\ge7).$$

The filled square can therefore disappear in time linear in its side length, and the probability of disappearing in the first possible round decays exponentially in its area. [Proof and diagrams for the first possible round (Chinese)](../research/lower-bounds-2026-11-19/earliest.md) · [Asymptotic expectation and early-extinction bounds (Chinese)](../research/lower-bounds-2026-11-19/lower-tail.md)

Moreover, $\liminf_{N\to\infty}\mathbb E T_N/N^2\ge(1152000\log 2)^{-1}$. For every integer $k\ge0$, the early-extinction probability satisfies $\mathbb P(T_N\le k)\le2\exp[-(\log 2)N^2/(64000000(k+1))]$. In particular, $\mathbb P(T_N\le k_N)\to0$ for any sequence of nonnegative integers $k_N=o(N^2)$. [All-scale lower bound](../research/lower-bounds-2026-11-19/AllScaleLower.lean) · [Upper bound on the probability of earliest extinction](../research/lower-bounds-2026-11-19/MinimumAtomUpper.lean) · [Audit record](../research/lower-bounds-2026-11-19/evidence/validation.json)

### Theorem 2 (block tail and expectation)

Define

$$
b_N=331776N^2+257,\qquad
a_N=\frac{32}{8N+1}+\frac{12}{5}N^2\,2^{-(1296N^2+1)}.
$$

For every integer $N\ge16$, every admissible deterministic initial state $x$ of size exactly $N$ and every integer $j\ge0$,

$$
\mathbb P(T_x>jb_N)\le a_N^j\le2^{-j},\qquad
0\le a_N\le\min\{1/2,5/N\},
$$

$$\mathbb ET_x\le\tau(N)\le\frac{b_N}{1-a_N}.$$

It follows that $T_x<\infty$ almost surely and $\inf_{s(x)=N}\mathbb P(T_x\le b_N)\to1$ as $N\to\infty$. The block tail follows by restarting from the configuration at the end of each block, conditional on its history, and using monotonicity to compare with a filled square. See `original_sharp_block_tail` and `original_sharp_expectation` in [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean) and `tau_le` in [SharpRecoveryTail.lean](../research/revision-ab-2026-11-17/lean/SharpRecoveryTail.lean). The $5/N$ bound and the $O(N^{-1})$ rate appear in [SharpFailureRate.lean](../research/revision-ab-2026-11-17/lean/SharpFailureRate.lean).

### Corollary (positive-order and exponential moments)

Set $c_0=332033$. For a fixed real $r>0$, define

$$C_r=c_0^r\sum_{j=0}^{\infty}(j+1)^{\lceil r\rceil}2^{-j}<\infty.$$

For $N\ge16$ and all admissible initial states of size exactly $N$,

$$\mathbb E T_x^r\le C_rN^{2r}.$$

For $0<\lambda<\log(2)/c_0$, we also have

$$
\mathbb E\exp(\lambda T_x/N^2)
\le1+\frac{e^{c_0\lambda}}{1-e^{c_0\lambda}/2}<\infty.
$$

The constants are uniform in $N$ and the initial state. Powers and exponentials take the value $\infty$ at $T_x=\infty$. The block tail gives almost sure finiteness before either moment estimate is applied. See `original_rpow_le`, `original_exponential_le` and `original_exponential_lt_top` in [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean) and the estimates in [RecoveryMoments.lean](../research/revision-ab-2026-11-17/lean/RecoveryMoments.lean).

### Proof and versions

The [English manuscript](../research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) combines the geometric lower bound, the particle representation for the upper bound, the clock comparison and the restart argument to prove quadratic order and bound late recovery. The [proof outline](PROOF_GUIDE.md) explains how the estimates fit together. The revision also unifies two calculations of observables of the clock process through a finite-state Dynkin formula, `finite_machine_dynkin`, for a finite square with rate-$1$ clocks and fair marks at each site.

[OriginalQuadraticRecovery.lean](../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean) preserves the version of 26 October 2026, with lower bound $N^2/56623104000$ for $N\ge786432000$ and the same upper bound as above. The lower bound in the 17 November manuscript was first proved in [ImprovedOriginalLower.lean](../research/exploration/phase2/lean/ImprovedOriginalLower.lean) and then incorporated into revision 6. The version mapping and build records are in [Verification](VERIFICATION.md).

Section 4.2 of reference [1] gives a cubic upper bound for the expected recovery time of the synchronous rule, and Question 7.4 asks whether the correct order is quadratic. See [References](REFERENCES.md#fates-marcovici-taati-2022).

<a id="随机等待网络"></a>

## Stochastic waiting network

The following results concern a separate directed waiting network, with its own parameters, states and observations.

### Definition 3 (waiting-time representation and three-tank system)

Assume

$$a,b>0,\qquad e,f\ge0,\qquad e+f>0.$$

Take the following random variables to be mutually independent,

$$
W_a\sim\operatorname{Exp}(a),\quad
W_b\sim\operatorname{Exp}(b),\quad
W_c\sim\operatorname{Exp}(e+f),\quad
J\sim\operatorname{Bernoulli}\!\left(\frac f{e+f}\right),
$$

and set $S=W_c+W_a+JW_b$. Here $\operatorname{Exp}(r)$ denotes the exponential distribution of rate $r$ and mean $1/r$. The route with $J=1$ incurs the extra waiting time $W_b$.

Under a constant unit input, the corresponding three-tank system satisfies the following equations for $t>0$,

$$
\begin{aligned}
x_0'&=a(1-x_0),\\
x_1'&=b(x_0-x_1),\\
x_2'&=e(x_0-x_2)+f(x_1-x_2),
\end{aligned}
\qquad x_0(0)=x_1(0)=x_2(0)=0.
$$

### Proposition 4 (outlet distribution and mean)

For $t\ge0$,

$$
x_2(t)=\mathbb P(S\le t),\qquad
\mathbb E[S]=\frac1a+\frac{b+f}{b(e+f)}.
$$

The cumulative distribution function is zero for negative times. The representation comes from convolving the exponential waiting times for each route and mixing the results according to $J$. For $t\ge0$, it gives the outlet response, satisfies the differential equations for $t>0$ and has the stated initial values at $t=0$. See [ActualTankCdf.lean](../research/exploration/phase5/lean/ActualTankCdf.lean) and the general-parameter version in [GeneralTankCdf.lean](../research/exploration/phase6/lean/GeneralTankCdf.lean).

### Proposition 5 (comparison and identification of rates)

Fix $a,b,e$ and vary $f$ over the allowed range $f\ge0$, $e+f>0$. At each time, the completion probability is nondecreasing in $f$ if $e<b$ and nonincreasing in $f$ if $e>b$. If $e=b$, the entire completion-time distribution is independent of $f$.

When $a,b,e$ are known and $b\ne e$, the mean uniquely determines $f$. With $a,b,e$ fixed, two admissible rates $f_1,f_2$ give the same completion-time distribution if and only if $f_1=f_2$ or $b=e$. See `totalMeasure_eq_iff` in [LawIdentifiability.lean](../research/exploration/phase7/lean/LawIdentifiability.lean).

Suppose in addition that the four rates can vary independently over nonempty closed intervals,

$$
a\in[a_-,A],\quad b\in[b_-,B],\quad
e\in[e_-,E],\quad f\in[f_-,F],
$$

with $a_-,b_->0$, $e_-,f_-\ge0$ and $e_-+f_->0$. Choose

$$
(a_*,b_*,e_*)=(A,B,E),\qquad
f_*=
\begin{cases}F,&E\le B,\\f_-,&E>B.\end{cases}
$$

This corner of the parameter box maximizes the completion probability simultaneously for all $t\ge0$. The conclusion uses the assumption that all combinations of values in the four intervals are admissible. See `selected_maximizes_all_times` in [RateBoxMaximum.lean](../research/exploration/phase8/lean/RateBoxMaximum.lean).

## Identification bounds from completion times and route marks

Fix $a=e=1$ and $b=1+\varepsilon$ with $\varepsilon>0$. Compare the low model $f=1/2$ with the high model $f=1$. Select one model with probability $1/2$ each, then generate $n$ independent tasks conditional on that selected model. Each task produces both a completion time $S_i$ and a route mark $J_i$. The decision rules below are measurable deterministic functions of their observations with two possible outputs, one per model.

### Proposition 6 (uniform upper bound for completion-time observations)

Let

$$\delta=\frac{\varepsilon}{6(1+\varepsilon)}.$$

The two single-task completion-time distributions admit a common submeasure of mass $1-\delta$. This is a finite measure of total mass $1-\delta$ whose value on each measurable set is at most that of either distribution. Its $n$-fold product is a common submeasure for the samples, of mass $(1-\delta)^n$. Thus any rule that uses only $(S_1,\ldots,S_n)$ has average success probability under the equal prior bounded by

$$
p_{\mathrm{time}}\le1-\frac{(1-\delta)^n}{2}
\le\frac12+\frac{n\delta}{2}.
$$

Let $\nu$ be the common sample submeasure and $B$ the set of observations on which the rule chooses the high model. The error events are $B$ under the low model and $B^c$ under the high model. Their prior-weighted probability is at least $(\nu(B)+\nu(B^c))/2=(1-\delta)^n/2$. The second inequality uses $(1-\delta)^n\ge1-n\delta$. The common submeasure is constructed in [ActualCompletionEventBound.lean](../research/exploration/phase10/lean/ActualCompletionEventBound.lean). For the uniform bound over samples and rules, see `testSuccess_le_common_power` and `testSuccess_le_linear` in [ActualCompletionTesting.lean](../research/exploration/phase11/lean/ActualCompletionTesting.lean).

### Proposition 7 (lower bound for a rule using route marks)

The probabilities of $J_i=1$ are $1/3$ and $1/2$ for the low and high models, respectively. For $n>0$, let $K_n=\sum_{i=1}^nJ_i$. Select the high model if

$$K_n\ge5n/12$$

and the low model otherwise. The means and variances conditional on the model are

$$
\begin{array}{c|cc}
&\mathbb E[K_n]&\operatorname{Var}(K_n)\\\hline
\text{Low model}&n/3&2n/9\\
\text{High model}&n/2&n/4.
\end{array}
$$

The threshold is $n/12$ away from either mean. Chebyshev's inequality bounds the two error probabilities by $32/n$ and $36/n$, respectively, so the rule's average success probability under the equal prior satisfies

$$p_{\mathrm{branch}}\ge1-34/n.$$

For $\varepsilon=1/100$ and $n=100$, Propositions 6 and 7 give

$$
p_{\mathrm{time}}\le\frac{353}{606},\qquad
p_{\mathrm{branch}}\ge\frac{33}{50},\qquad
p_{\mathrm{branch}}-p_{\mathrm{time}}\ge\frac{587}{7575}.
$$

The upper bound applies to every rule using completion times, and the lower bound applies to the stated rule using route marks. Both observations come from the same random task. See `branchSuccess_ge`, `timeSuccess_le` and `advantage_ge` in [ObservationContrast.lean](../research/exploration/phase12/lean/ObservationContrast.lean) for the link between the distributions and the bound on the difference.

The [comparison figure (Chinese labels)](../research/exploration/phase12/images/observation-choice.png) shows the upper bound $353/606\approx58.25\%$ for all rules using completion times and the lower bound $33/50=66\%$ for the specified rule using route marks. Their difference is approximately $7.749$ percentage points, a lower bound on the advantage over any completion-time rule.

## Proof and version records

The [verification page](VERIFICATION.md) records the formal sources, standard kernel audits, toolchains and source fingerprints for the original main theorem. The waiting-network results and successive lower-bound improvements retain their own validation records. The public waiting-network material runs through phase 12. See [Version status](../STATUS.md) for the scope of the public versions. Each audit and independent review applies to its recorded files and date.

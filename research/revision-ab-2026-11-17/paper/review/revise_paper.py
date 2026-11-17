from pathlib import Path
import hashlib,json,shutil

ROOT=Path(__file__).resolve().parents[1]
OLD=Path('D:/MyWorks/Math/research/manuscript/quadratic-recovery-v5')
s=(OLD/'paper.md').read_text(encoding='utf-8')
changes=[]
def repl(old,new,task):
    global s
    assert s.count(old)==1,(task,s.count(old),old[:80])
    s=s.replace(old,new)
    changes.append({'task':task,'old_start':old[:110],'new_start':new[:110]})
def between(a,b,new,task):
    global s
    i=s.index(a);j=s.index(b,i)
    repl(s[i:j],new,task)

s=s.replace('Working draft, revision 5 — 29 October 2026.','Working draft, revision 6 — 17 November 2026.')
s=s.replace('56623104000','576000000').replace('786432000','500001')
s=s.replace('128000','12500')
repl('The upper bound alone holds for $N\\geq16$. This is the quadratic order',
     'The upper bound alone holds for $N\\geq16$, with a uniform geometric bound on its block tails. The filled square attains the worst extended expectation for every $N\\geq2$. This is the quadratic order','A1/A2/B1 abstract')
repl('The upper inequality holds for every $N\\geq16$. Consequently $\\tau(N)=\\Theta(N^2)$.',r'''The upper inequality holds for every $N\geq16$. Consequently $\tau(N)=\Theta(N^2)$.

**Theorem 2 (uniform block tail).** Put
$$
b_N=331776N^2+257.
$$
For every integer $N\geq16$, every deterministic finite perturbation $x$ of either homogeneous background with size exactly $N$, and every integer $j\geq0$,
$$
\mathbb P(T_x>jb_N)\leq2^{-j}.
\tag{4a}
$$
In particular, $T_x<\infty$ almost surely. The bound is uniform over the permitted initial configurations. Its proof uses conditional restart from the observed configuration; it does not require independence of successive survival events.''','A2 results')
anchor='**Lemma 2 (clock/synchronous bridge).**'
repl(anchor,r'''**Corollary 1 (an exact extremizer).** For every integer $N\geq2$,
$$
\tau(N)=\mathbb E T_{\mathbf1_{Q_N}}.
\tag{6a}
$$
Both sides are extended expectations. To prove the upper inequality, normalize any permitted initial configuration by translation and, when needed, colour complementation. Lemma 1 then compares its recovery time with that of the filled square on the same side-$N$ domain. Taking extended expectations and the supremum gives $\tau(N)\leq\mathbb E T_{\mathbf1_{Q_N}}$. For the reverse inequality, the filled square itself has size exactly $N$ and is one of the configurations in (3). Thus it gives $\mathbb E T_{\mathbf1_{Q_N}}\leq\tau(N)$. This proves equality without assuming finiteness or uniqueness of the maximizing initial configuration.

'''+anchor,'B1')
between('For $L\\geq12288000$','For the upper estimate, use a mixed-boundary',r'''For $L\geq250000$ and $0\leq t\leq L^2/1000000$, this gives $C_{2L+1}(t)\geq1/2$. Put
$$
q_L=\left\lfloor\frac{L^2}{8000000}\right\rfloor,
\qquad r_L=q_L-1.
\tag{11}
$$
Then, for every $L\geq250000$,
$$
p_{2L+1}(r_L)\geq1/4,\qquad
r_L\geq L^2/16000000.
\tag{12}
$$

**Proof.** A clipped process is frozen when a protected set first loses a site. Its weighted missing-area variable $V_t$ is nonnegative and satisfies
$$
\mathbb E V_t\leq(18L+12)t+(L+2)(4L+2).
\tag{13}
$$
Protected exit costs at least $L^3/12500$ weighted units, and extinction of the original clock process implies protected exit. Markov's inequality gives (10). The improved static cost uses the sum of all weights in a square of side $\lfloor L/20\rfloor$, rather than a uniform lower bound on a smaller square. The proof is given in §5.3.

The weight vanishes at exterior sites where clipping could suppress a birth. It cancels that correction in the drift. The separate cleanup estimate gives the finite budget in (13). The static threshold is (SG5); the completed-output freeze and original-clock comparison are (MM9)–(MM10). The cleanup budget and exact weighted balance are (PB21) and (WB4). Sections 6.4–6.6 establish shape preservation, the actual raw weighted rate, and (13).

We give the numerical and rounding details. For $L\geq250000$,
$$
18L+12\leq19L,\qquad (L+2)(4L+2)\leq5L^2.
$$
Consequently, at $t=L^2/1000000$,
$$
(18L+12)t+(L+2)(4L+2)
\leq\frac{19L^3}{1000000}+5L^2
\leq\frac{39L^3}{1000000}
\leq\frac12\frac{L^3}{12500}.
$$
The second inequality uses $L\geq250000$. Substitution in (10) proves the clock survival estimate, also for all earlier times by monotonicity.

Write $q=q_L$. Integer division gives
$$
8000000q\leq L^2<8000000(q+1),\qquad q\geq32.
$$
As $250000L\leq L^2$, these inequalities also give $L\leq32q+31\leq64(q-12)$. Set $s=q-12\geq16$. The elementary estimate $2^s\geq64s^2$ holds for every integer $s\geq16$: it holds at $16$, and its induction step follows from $2s^2\geq(s+1)^2$. Therefore
$$
64L^2\leq4096\,(64s^2)\leq4096\,2^s=2^q.
$$
Since $r_L+1=q$ and $\log2\leq1$,
$$
t_{r_L}=8\log2\,q\leq8q\leq L^2/1000000.
$$
Also $(2L+1)^2\leq9L^2$, so
$$
E_{2L+1}(r_L)
=\frac65(2L+1)^2\,2^{-q}
\leq\frac{54}{5}L^2\,2^{-q}
\leq\frac{27}{160}<\frac14.
$$
Subtract this scheduling error in (8) from the clock survival probability $1/2$. This proves $p_{2L+1}(r_L)\geq1/4$. Finally, $q+1\leq2(q-1)$ because $q\geq32$, whence
$$
L^2<8000000(q+1)\leq16000000(q-1)=16000000r_L.
$$
This proves (12), retaining the floor and the subtraction of one. No finite-extinction assumption has been used. $\square$

''','A1 lemma3')
between('**Assembly of Theorem 1.**','## 3. The clock/synchronous comparison',r'''**Assembly of Theorems 1 and 2.** Lemmas 1 and 6 give the upper bound and the uniform block tail in (4a), including initial perturbations of the other homogeneous background by colour complementation. For the lower bound take the filled square and
$$
L=\left\lfloor\frac{N-1}{2}\right\rfloor.
$$
For $N\geq500001$, integer division gives $L\geq250000$, $2L+1\leq N$ and $L\geq N/3$. The last inequality follows from $N\leq2L+2\leq3L$, since $L\geq2$. Place the side-$(2L+1)$ filled square inside $Q_N$ and apply common-mark monotonicity. Lemma 3 gives
$$
\mathbb E T_{\mathbf1_{Q_N}}
\geq r_L\,\mathbb P(T_{\mathbf1_{Q_N}}>r_L)
\geq r_L/4
\geq L^2/64000000
\geq N^2/576000000.
$$
These inequalities are valid for extended expectations. Corollary 1 identifies the left side with $\tau(N)$. Thus both bounds concern the original synchronous product law and the exact size convention (2).

''','A1 assembly')

# Move the common actual-clock calculation out of the exclusion application.
start='#### 4.2.1. From the original gaps and marks to an observable equation'
end='#### 4.2.2. The genuine one- and two-point equations'
i=s.index(start);j=s.index(end,i)
old_mc=s[i:j]
common=r'''### 3.4. A finite-state observable identity under the original clocks

We use the following identity twice: for the mixed-square occupation field and for the modified process carrying its cleanup counter. We state it for the finite squares used in this paper, with arbitrary finite state space and deterministic initial state.

Let $L\geq1$, $V=\{-L,\ldots,L\}^2$, and $K=|V|=(2L+1)^2$. A translated square of the same side has the identical coordinate law. Let $\mathcal A$ be a nonempty finite set, let $y_0\in\mathcal A$, and let
$$
F_{v,b}:\mathcal A\longrightarrow\mathcal A
\qquad(v\in V,\ b\in\{0,1\})
$$
be fixed update maps. Execute the original rate-one gap field and independent fair identity marks of §3.3.1 from $y_0$. Write $Y(t)$ for its endpoint at physical time $t$, including events at $t$. For $G:\mathcal A\to\mathbb R$, define
$$
\mathcal LG(y)=\frac12\sum_{v\in V}\sum_{b=0}^1
  [G(F_{v,b}(y))-G(y)].
\tag{FM1}
$$
Then, for every $T\geq0$,
$$
\mathbb E G(Y(T))=G(y_0)+\int_0^T\mathbb E\mathcal LG(Y(s))\,ds.
\tag{FM6}
$$
All expectations use the original gap-and-mark product law. No equation for a proposed replacement process is assumed.

**Proof.** Let $\mathcal H_t$ record the arrivals through deterministic time $t$ and the marks of those arrivals, revealing no future gaps or unused marks. Construct an $\mathcal H_t$-measurable state on every sample as follows. If the arrived identities form a finite strictly chronological list, execute that list with its observed marks from $y_0$; otherwise return $y_0$. For each candidate list, the assertion that it contains exactly the arrived identities is a countable intersection of observed arrival or nonarrival assertions. Its order and its finitely many marks are observed too. There are countably many lists and finite mark vectors, and each fixes its execution result. Taking their unions therefore describes the event of each possible output state. This proves measurability without a test of future regularity. On the single regular probability-one set from §3.3.1 this representative agrees with actual execution simultaneously for every $t$.

The same construction is jointly measurable in $(t,\omega)$. For a candidate list, selecting exactly the events through $t$ amounts to measurable inequalities $s_e(\omega)\leq t$ or $s_e(\omega)>t$, together with its measurable order and marks. Replacing $\leq t$ by $<t$ constructs the jointly measurable strict pre-event representative $Y(t-)$.

Conditional on $\mathcal H_t$, the residual waits at the $K$ sites are independent rate-one exponentials, the later gaps retain their original laws, and the unused marks remain independent and fair. We justify the required joint assertion directly. Partition by the first unarrived gap index $r_v$ at each site. Fix the earlier gaps and their observed marks, and let $b_v\leq t$ be the last arrival at $v$, or $0$ if none has occurred. The current gaps satisfy $G_{v,r_v}>t-b_v$. With residuals $u_v=G_{v,r_v}-(t-b_v)>0$, their product density factors as
$$
\prod_{v\in V}e^{-(t-b_v+u_v)}
=\left(\prod_{v\in V}e^{-(t-b_v)}\right)
 \left(\prod_{v\in V}e^{-u_v}\right).
$$
The first factor is the mass of the survival constraints; after normalization the second is the independent residual density. Later gaps are unrestricted coordinates. On this fixed index slice, the unused mark identities are fixed and disjoint from the observed ones, so their joint law is the original fair product law.

For precision, take an observed-history event $D$ and a measurable condition $C$ on finitely many residual, later-gap and unused-mark coordinates, numbered from the first unarrived event at each site. On the fixed earlier-coordinate slice, the indicator of $D$ is unchanged while the current gaps vary above their survival thresholds. The density factorization separates this indicator from the probability of $C$. Integrating earlier coordinates and summing the index vectors gives
$$
\mathbb P(D\cap\{\text{future coordinates satisfy }C\})
=\mathbb P(D)\,\mu_{\mathrm{future}}(C),
$$
where $\mu_{\mathrm{future}}$ is the prescribed product law. This proves the finite joint conditional laws used next. It is a deterministic-time statement; no arbitrary-stopping-time assertion is needed here.

For $h>0$, exactly one arrival in $(t,t+h]$, at a specified site $v$ and with a specified mark $b$, has conditional probability
$$
\frac12\int_0^h e^{-s}e^{-(h-s)}e^{-(K-1)h}\,ds
=\frac h2e^{-Kh}.
\tag{FM2}
$$
The factors describe the residual wait, the exclusion of a second arrival at that site, and the exclusion of arrivals at all other sites. The no-arrival probability is $e^{-Kh}$. These disjoint cases imply
$$
\mathbb P(\text{at least two arrivals in }(t,t+h]\mid\mathcal H_t)
=1-e^{-Kh}(1+Kh)\leq\frac{K^2h^2}{2},
\tag{FM3}
$$
using $1-e^{-x}(1+x)=\int_0^x u e^{-u}\,du\leq x^2/2$. Arrivals that leave the state unchanged are still counted.

Put $B_G=\max_{y\in\mathcal A}|G(y)|$. On a one-arrival event the state is exactly $F_{v,b}(Y(t))$. The exact one-arrival contribution is $he^{-Kh}\mathcal LG(Y(t))$, and $|\mathcal LG|\leq2KB_G$. Replacing $e^{-Kh}$ by $1$ costs at most $2B_GK^2h^2$. On the multiple-arrival event the observable changes by at most $2B_G$, and (FM3) bounds the additional cost by $B_GK^2h^2$. Thus
$$
\mathbb E[G(Y(t+h))-G(Y(t))\mid\mathcal H_t]
=h\mathcal LG(Y(t))+R_{t,h},
\qquad |R_{t,h}|\leq3B_GK^2h^2.
\tag{FM4}
$$
The estimate is uniform in the observed state and in $t$; closure of every $F_{v,b}$ on $\mathcal A$ ensures that all its terms are defined.

For any $A:\mathcal A\to\mathbb R$, changes between $s<t$ require a ring in $(s,t]$. Therefore
$$
|\mathbb E A(Y(t))-\mathbb E A(Y(s))|
\leq2\|A\|_\infty(1-e^{-K(t-s)})
\leq2K\|A\|_\infty(t-s).
\tag{FM5}
$$
Apply this to $G$ and to the finite function $\mathcal LG$. Their mean functions are continuous. Divide $[0,T]$ into $n$ equal intervals, take expectations in (FM4), and sum. The total error is at most $3B_GK^2T^2/n$, and the main term is the left Riemann sum for $\mathbb E\mathcal LG(Y(s))$. Letting $n\to\infty$ proves (FM6). The fundamental theorem of calculus then gives
$$
\frac d{dt}\mathbb E G(Y(t))
=\mathbb E\mathcal LG(Y(t))\qquad(t>0),
\tag{FM7}
$$
with continuity at $0$.

On each regular trajectory, $Y(s-)$ and $Y(s)$ differ only at its countably many ring times. Thus bounded jointly measurable functions of these two states have equal time integrals. Fubini's theorem permits the same replacement inside time integrals of expectations. This is the strict-before/end-point correspondence needed for event scores in §6.2.3. $\square$

The argument proves the identity directly from the given clocks. Its finite-state formulation does not identify arbitrary processes by a matching formal generator. In the artifact, the corresponding general observable theorem is `MachineClockDynkin.expected_observable_dynkin`; the state type and observable are arbitrary finite ones, while its site type remains the finite square `DropletClockLaw.Vertex L`.

'''
spec=r'''#### 4.2.1. Application of the finite-state observable identity

Use §3.4 on the side-$M=2L+1$ mixed square, translating its sites if necessary. Take $\mathcal A$ to be the finite set of coordinatewise nondecreasing square patterns, $y_0$ the specified deterministic initial pattern, and $F_{v,b}=\Phi_v^b$. The shape argument of §4.1 proves closure under both marks at every site. Its staircase map $f\mapsto\eta(f)$ is deterministic. Thus any function $F$ on the finite occupation space gives the observable $G(f)=F(\eta(f))$ on $\mathcal A$.

Equation (MC1) identifies the increment operator (FM1) of this observable with the exclusion operator $\mathcal LF$ evaluated at $\eta(f)$. Applying (FM6) therefore gives, under the original cell-clock and mark law,
$$
\mathbb E F(\eta(T))
=F(\eta(0))+\int_0^T\mathbb E\mathcal LF(\eta(s))\,ds.
\tag{MC6}
$$
The initial state is deterministic. By (FM5)–(FM7), the mean is continuous at $0$ and
$$
\frac d{dt}\mathbb E F(\eta(t))
=\mathbb E\mathcal LF(\eta(t))\qquad(t>0).
\tag{MC7}
$$
This application uses both the update-by-update encoding and the actual clock identity. A finite algebraic equality of operators alone would not supply the stochastic evolution equation.

'''
repl(old_mc,spec,'A3 mixed application')
repl('## 4. Proof of mixed local clearing',common+'## 4. Proof of mixed local clearing','A3 common lemma')
s=s.replace('(MC5)--(MC7)','(FM5), (MC6) and (MC7)')

# Replace the duplicated small-time proof in the counter application.
between('To be precise about exceptional samples, form $Y(t)$','Take $G=F$, where $F(U,c)=c$.',r'''Apply §3.4 with $V=\Lambda_L$, $\mathcal A=\mathcal E$, deterministic initial state $(D,0)$, and update maps $F_{v,b}=T_{(v,b)}$. The finite-word bound (PB13) and closure in (PB16) are the required finite-state hypotheses. In particular, this application needs the reachable counter space; it would not be justified by treating an unbounded auxiliary counter as automatically bounded.

The history-measurable representative from §3.4 executes the observed finite list and otherwise returns $(D,0)$. It belongs to $\mathcal E$ on every sample and agrees with the actual augmented execution simultaneously at all times on the common regular set. Its jointly measurable strict-before version records the input of each actual event.

For $G:\mathcal E\to\mathbb R$, its increment operator is
$$
\mathcal L_{\mathcal E}G(x)
=\sum_{v\in\Lambda_L}\frac12\sum_{b=0}^1
 [G(T_{(v,b)}x)-G(x)].
\tag{PB17}
$$
The common identity (FM6), with the original physical-time law, now gives
$$
\mathbb E G(Y(T))
=G(D,0)+\int_0^T\mathbb E\mathcal L_{\mathcal E}G(Y(s))\,ds.
\tag{PB19}
$$
All state functions are bounded because $\mathcal E$ is finite. The strict-before and endpoint versions may be interchanged in these time integrals by the final paragraph of §3.4.

''','A3 counter application')
s=s.replace('same kinds of original coordinates as in §4.2.1','original coordinates used in §3.4')
s=s.replace('the written original-clock argument in §6.2.3','the common original-clock identity in §3.4')

# Replace the old smaller-block estimate by full affine summation.
s=s.replace('We will find a block with order $L^2$ missing sites, each with order $L$ weight.',
            'We will find a block with order $L^2$ missing sites and sum its varying weights exactly.')
between('Let\n$$\nm=\\left\\lfloor\\frac L{40}', '### 5.4. A numerical check',r'''Let
$$
m=\left\lfloor\frac L{20}\right\rfloor,\qquad
B=\{q+(\sigma i,\tau j):1\leq i,j\leq m\}.
\tag{SG7}
$$
The coordinate map is injective, so $|B|=m^2$. The empty strict quadrant makes $B$ disjoint from $S$.

We check that the entire larger block is still inside the clipped domain. For $z=q+(\sigma i,\tau j)$, (SG3) and $m\leq L/20$ give
$$
\|z\|_1\leq\frac9{10}L+1+i+j\leq L+1.
$$
For each coordinate separately,
$$
|z_1|\leq\|q\|_1+i\leq\frac{19}{20}L+1\leq L,
\qquad
|z_2|\leq\|q\|_1+j\leq\frac{19}{20}L+1\leq L,
$$
where $L\geq80$. Hence $B\subseteq D_L\setminus S$.

A pointwise lower weight of order $L$ is not needed at every far corner. Instead, the triangle inequality gives
$$
w_L(q+(\sigma i,\tau j))
\geq\frac L{10}+1-i-j.
$$
Sum this affine lower bound over the whole block. Since $\sum_{i=1}^m i=m(m+1)/2$,
$$
\begin{aligned}
\sum_{z\in B}w_L(z)
&\geq \sum_{i=1}^m\sum_{j=1}^m
     \left(\frac L{10}+1-i-j\right)\\
&=m^2\left(\frac L{10}+1\right)-m^2(m+1)
=m^2\left(\frac L{10}-m\right).
\end{aligned}
\tag{SG8}
$$
The floor costs only a fixed factor. Write $L=20m+r$ with $0\leq r\leq19$. Since $L\geq80$ implies $m\geq4$, we have $r\leq5m$, hence $m\geq L/25$. Also $m\leq L/20$, so $L/10-m\geq L/20$. All remaining missing weights in $D_L$ are nonnegative. Therefore
$$
V_L(S)\geq\sum_{z\in B}w_L(z)
\geq m^2\left(\frac L{10}-m\right)
\geq\frac{L^2}{625}\frac L{20}
=\frac{L^3}{12500}.
$$
This proves (SG5), including $S=\varnothing$. It is the full sum (SG8), rather than a larger minimum site weight, that yields the improved threshold.

''','A1 full block')
between('Here $m=2$, and the block consists of','The lemma proves the static cost',r'''Here $m=4$ and the full block consists of the sixteen sites
$$
B=\{(72-i,1-j):1\leq i,j\leq4\}.
$$
Their weights are $11+i-j$, with row sums $50,46,42,38$, totalling $176$. Formula (SG8) gives the lower estimate $m^2(L/10-m)=16(8-4)=64$, while the uniform cubic threshold is $80^3/12500=40.96$. Thus the exact sum, the affine lower sum, and the final threshold have the required order. The two end sites of $S$ have only one occupied neighbour, so $S$ is not stable in the two-neighbour sense used later. Stability is not a hypothesis of this static lemma, and this configuration is not asserted to be reachable by a modified trajectory.

''','A1 numerical check')
repl('*Figure 3. Static geometry for $L=80$. The domain view shows $D_{80}$ and the protected set $P_{80}$, including the outer boundary of $A_{80}$. The local view uses $q=(72,1)$ and $S=\\{(73,1),(72,2),(73,2)\\}$. Its strict southwest quadrant is empty. The four highlighted missing sites have weights $11,10,12,11$, with sum $44$. This is a static configuration, with no claim that it is a state of a modified trajectory.*',
     '*Figure 3. Static geometry for $L=80$. The domain view shows $D_{80}$ and the protected set $P_{80}$, including the outer boundary of $A_{80}$. The local view uses $q=(72,1)$ and $S=\\{(73,1),(72,2),(73,2)\\}$. Its strict southwest quadrant contains the full $4$ by $4$ vacant block used in (SG7). The sixteen displayed weights sum to $176$, above both the affine lower sum $64$ and the cubic threshold $40.96$. This is a static configuration; it is not asserted to be a modified-trajectory state.*','A1 figure caption')

repl('The constants in (4) are not optimized. No leading constant, limiting extinction law, shape theorem, or stability from random perturbations is claimed. The lower witness is the filled square; the upper bound covers all finite perturbations of exact size $N$. Both are expectation bounds, not empirical averages.',
     'The constants in (4) are not optimized. No leading constant, limiting extinction law, shape theorem, or stability from random perturbations is claimed. The filled square attains the exact worst extended expectation by (6a). The lower argument gives a positive survival probability for that witness; the geometric upper tail (4a) holds uniformly for every permitted deterministic perturbation of exact size $N$.','A2/B1 scope')
repl('The main entry is [OriginalQuadraticRecovery.lean](../../../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean). The declaration tau_quadratic_bounds gives (4); tau_theta_quadratic gives its existential asymptotic form for OriginalRecoveryProfile.tau.',
     'The strengthened main entry is [ImprovedOriginalLower.lean](../../exploration/phase2/lean/ImprovedOriginalLower.lean). Its declarations tau_quadratic_bounds and tau_theta_quadratic give (4) and its asymptotic form for OriginalRecoveryProfile.tau. The original frozen theorem remains in [OriginalQuadraticRecovery.lean](../../../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean); the upper coefficient is unchanged.','A1 source entry')
repl('| Lemma 3 and original lower bound | [PhysicalWeightedDrift](../../../formal/analysis/MathResearchAnalysis/PhysicalWeightedDrift.lean): original_clock_extinction_le_linear_time; [SynchronousQuadraticTail](../../../formal/analysis/MathResearchAnalysis/SynchronousQuadraticTail.lean); [OriginalQuadraticLower](../../../formal/analysis/MathResearchAnalysis/OriginalQuadraticLower.lean) |',
     '| Lemma 3 and strengthened lower bound | [FullBlockThreshold](../../exploration/lean/FullBlockThreshold.lean): fullBlock_exact_lower_bound, fullBlock_cubic_weight, original_clock_extinction_at_quadraticHorizon_le_half; [ImprovedOriginalLower](../../exploration/phase2/lean/ImprovedOriginalLower.lean): synchronous_tail_ge_quarter, rounds_quarter_ge_original_square, tau_quadratic_bounds |\n| Common finite-state observable identity | [MachineClockDynkin](../../../formal/analysis/MathResearchAnalysis/MachineClockDynkin.lean): expected_observable_dynkin; its site type is the finite square DropletClockLaw.Vertex L |','A1/A3 source table')

ROOT.mkdir(parents=True,exist_ok=True)
(ROOT/'images').mkdir(exist_ok=True)
for p in (OLD/'images').glob('*.png'):shutil.copy2(p,ROOT/'images'/p.name)
for p in OLD.glob('*source-map.json'):shutil.copy2(p,ROOT/p.name)
(ROOT/'paper.md').write_text(s,encoding='utf-8',newline='\n')
manifest={'old_paper_sha256':hashlib.sha256((OLD/'paper.md').read_bytes()).hexdigest(),
          'new_paper_sha256':hashlib.sha256((ROOT/'paper.md').read_bytes()).hexdigest(),
          'changes':changes,'status':'A1/A2/A3/B1 prose draft; independent review and integrated B2/B3 pending',
          'frozen_source_modified':False,'new_kernel_build_claimed_by_this_script':False}
(ROOT/'review'/'paper-change-map.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'chars':len(s),'lines':len(s.splitlines()),'changes':len(changes)},ensure_ascii=False))

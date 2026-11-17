from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent; p=R/'paper/paper.md'
s=p.read_text(encoding='utf-8')
assert '\\tag{4b}' not in s
marker='The theorem concerns (1) under its actual product coin law.'
result=r'''**Theorem 3 (retained block failure).** For an integer $N\geq16$, set
$$
a_N=\frac{32}{8N+1}+\frac{12}{5}N^2\,2^{-(1296N^2+1)}.
\tag{4b}
$$
Then $0\leq a_N\leq1/2$, $a_N\to0$ as $N\to\infty$, and, for every initial configuration covered by Theorem 2 and every integer $j\geq0$,
$$
\mathbb P(T_x>jb_N)\leq a_N^j,\qquad
\mathbb E T_x\leq\frac{b_N}{1-a_N},\qquad
\tau(N)\leq\frac{b_N}{1-a_N}.
\tag{4c}
$$
In particular, the probability of recovery by the fixed quadratic deadline $331776N^2+257$ tends to one. The additive $257$ is retained in this deadline.

**Theorem 4 (moments and exponential integrability).** Put $c_0=332033$. For every fixed real $r>0$, define the finite constant
$$
C_r=c_0^r\sum_{j=0}^{\infty}(j+1)^{\lceil r\rceil}2^{-j}.
$$
For every $N\geq16$ and every initial configuration covered by Theorem 2,
$$
\mathbb E T_x^r\leq C_r N^{2r}.
\tag{4d}
$$
Moreover, if $0<\lambda<\log(2)/c_0$, then
$$
\mathbb E\exp(\lambda T_x/N^2)
\leq K_\lambda
:=1+\frac{e^{c_0\lambda}}{1-e^{c_0\lambda}/2}<\infty.
\tag{4e}
$$
The same constant is valid for all these $N$ and initial configurations. The interval is nonempty; for example $\lambda=1/(4c_0)$ is admissible. Both powers and exponentials are interpreted as $+\infty$ at an infinite recovery time. Finiteness is a consequence of the tail estimate, not an assumption on $T_x$.

'''
assert marker in s;s=s.replace(marker,result+marker,1)
marker2='## 3. The clock/synchronous comparison in more detail'
proof=r'''### 2.1. The retained failure rate and distributional consequences

We prove Theorem 3 without weakening the estimates used in Lemma 6. With $M=8N+1$, the genuine larger mixed-clock local-clearing estimate and retained-sample comparison give
$$
C_N(16M^2)\leq16/M.
$$
The scheduling time $t_{k_N}$ is at least $16M^2$. Thus $C_N(t_{k_N})\leq16/M$. Substitution into the second direction (9) of the synchronous comparison yields
$$
p_N(b_N)\leq2\frac{16}{8N+1}
  +2\frac65N^2\,2^{-(k_N+1)}=a_N.
\tag{DF1}
$$
The two factors of two belong to that comparison. The clock probability is evaluated under its original product gap/mark law.

For $N\geq16$, $32/(8N+1)\leq1/4$ and $E_N(k_N)\leq1/8$, as proved in Lemma 6. Hence $0\leq a_N\leq1/2<1$. At every deterministic block boundary the observed pattern is below the filled square, and unused future marks are independent of the used marks and have their original law. Consequently
$$
\mathbb P(T_x>(j+1)b_N)\leq
 a_N\mathbb P(T_x>jb_N).
\tag{DF2}
$$
Induction proves (4c), including $j=0$. This conditional estimate does not assert independence of the successive survival events.

For any $T\in\{0,1,\ldots\}\cup\{\infty\}$ and positive integer $b$,
$$
T\leq b\sum_{j=0}^{\infty}\mathbf1_{\{T>jb\}}.
\tag{DF3}
$$
For finite $T$ this counts the blocks meeting the waiting interval; for $T=\infty$ both sides are infinite. Tonelli's theorem and (DF2) give
$$
\mathbb E T_x\leq b_N\sum_{j=0}^{\infty}a_N^j
=\frac{b_N}{1-a_N}.
$$
Take the supremum over exact-size initial configurations for the stated $\tau(N)$ bound. Finally, $k_N+1\geq N$ and
$$
0\leq\frac{12}{5}N^2 2^{-(k_N+1)}
\leq\frac{12}{5}N^2 2^{-N}\longrightarrow0.
$$
Together with $32/(8N+1)\to0$, this proves $a_N\to0$ and the recovery-by-deadline conclusion.

For Theorem 4, we use only Theorem 2, so these moment conclusions do not depend on the refined $a_N$. First,
$$
\mathbb P(T_x=\infty)\leq\mathbb P(T_x>jb_N)\leq2^{-j}
\quad(j\geq0),
$$
which proves almost-sure finiteness by letting $j\to\infty$. We retain the original extended-valued random variable in the expectations below; its infinite-value event is now known to be null.

For any nondecreasing $F:\mathbb N\to[0,\infty]$, a finite positive $T$ belongs to exactly one interval $(jb_N,(j+1)b_N]$. Thus
$$
F(T)\leq F(0)+\sum_{j=0}^{\infty}
 F((j+1)b_N)\,\mathbf1_{\{T>jb_N\}}
\quad\text{almost surely}.
\tag{DF4}
$$
This also holds at $T=0$; the separate $F(0)$ term will matter for the exponential. Tonelli applies to its nonnegative summands without a prior moment assumption.

Take $F(t)=t^r$. Since $F(0)=0$ and $b_N\leq c_0N^2$,
$$
\mathbb E T_x^r
\leq b_N^r\sum_{j=0}^{\infty}(j+1)^r2^{-j}
\leq c_0^rN^{2r}\sum_{j=0}^{\infty}(j+1)^{\lceil r\rceil}2^{-j}.
$$
For $k=\lceil r\rceil$, the ratio of consecutive positive summands in the last series is
$$
\frac12\left(\frac{j+2}{j+1}\right)^k\longrightarrow\frac12<1.
$$
The ratio test proves $C_r<\infty$, for every fixed real $r>0$, and establishes (4d). For example, $r=1$ gives $\sum_{j\geq0}(j+1)2^{-j}=4$, so $C_1=4c_0$. Lemma 6 already gives the smaller first-moment constant $2c_0$; the single formula $C_r$ is used here to cover all positive real orders.

For the exponential choose $F(t)=e^{\lambda t/N^2}$. Now $F(0)=1$, and (DF4) gives
$$
\mathbb E e^{\lambda T_x/N^2}
\leq1+\sum_{j=0}^{\infty}e^{c_0\lambda(j+1)}2^{-j}
=1+\frac{e^{c_0\lambda}}{1-e^{c_0\lambda}/2}.
$$
The geometric sum converges precisely under the sufficient condition $c_0\lambda<\log2$ used here. Since $\log2\geq1/2$, the concrete positive choice $\lambda=1/(4c_0)$ satisfies it. This proves (4e). No step assumes a higher moment or exponential moment finite before proving it. $\square$

'''
assert marker2 in s;s=s.replace(marker2,proof+marker2,1)
s=s.replace('with a uniform geometric bound on its block tails. The filled square', 'with a uniform geometric bound on its block tails. Retaining the block failure rate gives recovery by an explicit quadratic deadline with probability tending to one, as well as bounds on all fixed positive moments and a common interval of exponential moments. The filled square',1)
s=s.replace('The filled square attains the exact worst extended expectation by (6a). The lower argument', 'The retained failure rate gives (4c); Theorem 4 supplies fixed positive moments and exponential integrability on its stated interval. The filled square attains the exact worst extended expectation by (6a). The lower argument',1)
p.write_text(s,encoding='utf-8',newline='\n')
record={'tasks':['B2','B3'],'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'new_result_tags':['4b','4c','4d','4e'],'proof_tags':['DF1','DF2','DF3','DF4'],'unimplemented':['C1','C2'],'formal_binding':'pending final aggregate build'}
(R/'paper/review/distribution-integration.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(record['source_sha256'])

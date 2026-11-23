# 研究结果

[English](RESEARCH_RESULTS.md) · **简体中文**

## 同步随机多数规则的恢复时间

考虑 $\mathbb Z^2$ 上的同步四邻多数规则，平票在格点和轮次之间独立公平取色。确定初态 $x$ 是任一纯色背景上的有限扰动，$s(x)$ 为其最小平移轴平行包围方形的边长，按格点列数计。$T_x\in\mathbb N_0\cup\{\infty\}$ 为恢复原背景的轮数，

$$\tau(N)=\sup_{s(x)=N}\mathbb ET_x.$$

完整定义见[模型与记号](NOTATION.zh-CN.md)。以下给出原模型结果，包括 11 月 19 日完成的方形下界。

### 定理 1（二次上下界与极值）

对整数 $N\ge16$，

$$\frac{N^2}{850000}\le\tau(N)\le664066N^2.$$

上界对所有 $N\ge16$ 成立，故 $\tau(N)=\Theta(N^2)$。对 $N\ge2$，零背景上填满的方形 $Q_N=\{0,\ldots,N-1\}^2$ 实现最坏期望：

$$\tau(N)=\mathbb E T_{Q_N}.$$

极值等式在非负扩展期望中成立；有限性由上界推出。共同标记下的单调性控制同一方形内的任意初态，平移不变性及颜色对称性还原两种背景。

11 月 17 日版本的二次上下界见 [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean) 的 `quadratic_bounds`，方形极值见 [OriginalRecoveryResults.lean](../research/revision-ab-2026-11-17/lean/OriginalRecoveryResults.lean) 的 `tau_eq_full_square`。

令 $T_N=T_{Q_N}$，$m_N=1+2\lfloor(N-1)/2\rfloor$。对每个 $N\ge1$，有 $\mathbb E T_N\ge\max\{m_N,N^2/850000\}$。$m_N$ 是可能消亡的第一轮，奇数边长时为 $N$，偶数边长时为 $N-1$。若 $q_N=\mathbb P(T_N=m_N)$，则

$$2^{-2N^2}\le q_N\le 2^{-\lfloor N^2/8\rfloor}\qquad(N\ge7).$$

因此，方形可以在线性时间内消亡，而恰在最早一轮消亡的概率随面积指数衰减。[最早消亡的证明与配图](../research/lower-bounds-2026-11-19/earliest.md) · [渐近期望与早消亡尾界](../research/lower-bounds-2026-11-19/lower-tail.md)

此外，$\liminf_{N\to\infty}\mathbb E T_N/N^2\ge(1152000\log 2)^{-1}$。对整数 $k\ge0$，方形的早消亡概率满足 $\mathbb P(T_N\le k)\le2\exp[-(\log 2)N^2/(64000000(k+1))]$。特别地，对任意非负整数序列 $k_N=o(N^2)$，有 $\mathbb P(T_N\le k_N)\to0$。[全尺度下界](../research/lower-bounds-2026-11-19/AllScaleLower.lean) · [最早消亡原子](../research/lower-bounds-2026-11-19/MinimumAtomUpper.lean) · [审计记录](../research/lower-bounds-2026-11-19/evidence/validation.json)

### 定理 2（块尾与期望）

令

$$
b_N=331776N^2+257,\qquad
a_N=\frac{32}{8N+1}+\frac{12}{5}N^2\,2^{-(1296N^2+1)}.
$$

对每个整数 $N\ge16$、每个尺寸恰为 $N$ 的允许确定初态 $x$ 和每个整数 $j\ge0$，

$$
\mathbb P(T_x>jb_N)\le a_N^j\le2^{-j},\qquad
0\le a_N\le\min\{1/2,5/N\},
$$

$$\mathbb ET_x\le\tau(N)\le\frac{b_N}{1-a_N}.$$

因此 $T_x<\infty$ 几乎必然，且 $\inf_{s(x)=N}\mathbb P(T_x\le b_N)\to1$。块尾由给定过去后的重启与单调支配得到。源码为 [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean) 的 `original_sharp_block_tail`、`original_sharp_expectation` 及 [SharpRecoveryTail.lean](../research/revision-ab-2026-11-17/lean/SharpRecoveryTail.lean) 的 `tau_le`；$5/N$ 界与 $O(N^{-1})$ 见 [SharpFailureRate.lean](../research/revision-ab-2026-11-17/lean/SharpFailureRate.lean)。

### 推论（正阶矩与指数矩）

取 $c_0=332033$。对固定实数 $r>0$，令

$$C_r=c_0^r\sum_{j=0}^{\infty}(j+1)^{\lceil r\rceil}2^{-j}<\infty.$$

对 $N\ge16$ 和上述所有初态，

$$\mathbb E T_x^r\le C_rN^{2r}.$$

对 $0<\lambda<\log(2)/c_0$，还有

$$
\mathbb E\exp(\lambda T_x/N^2)
\le1+\frac{e^{c_0\lambda}}{1-e^{c_0\lambda}/2}<\infty.
$$

常数对 $N$ 和初态一致。幂与指数在 $T_x=\infty$ 时均取 $\infty$；证明从真实块尾先推出几乎必然有限性。见 [OriginalConsequences.lean](../research/revision-ab-2026-11-17/lean/OriginalConsequences.lean) 的 `original_rpow_le`、`original_exponential_le`、`original_exponential_lt_top`，及 [RecoveryMoments.lean](../research/revision-ab-2026-11-17/lean/RecoveryMoments.lean)。

### 证明与版本

当前[英文论文](../research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf)将几何下界、粒子表示上界、时钟比较和重启组成二次阶与晚恢复估计的论证；[证明纲要](PROOF_GUIDE.zh-CN.md)概述这些连接。修订还将两处时钟可观测量计算统一为有限状态 Dynkin 公式，适用于有限方形上的每点速率 $1$、公平标记机器，见 `finite_machine_dynkin`。

原 [OriginalQuadraticRecovery.lean](../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean) 保留 2026-10-26 版本：下界 $N^2/56623104000$、门槛 $786432000$，上界同上。11 月 17 日论文中的下界先由 [ImprovedOriginalLower.lean](../research/exploration/phase2/lean/ImprovedOriginalLower.lean) 证明，随后收入 revision 6。版本对应及构建记录见[验证方法](VERIFICATION.zh-CN.md)。

文献 [1] 的 §4.2 给出同步规则的三次期望上界，Question 7.4 提出二次量级问题；出处见[参考文献](REFERENCES.zh-CN.md#fates-marcovici-taati-2022)。

## 随机等待网络

下述结果属于独立的有向等待网络。其参数、状态和观测均不等同于二维自动机的对应对象。

### 定义 3（等待表示与三箱系统）

设

$$a,b>0,\qquad e,f\ge0,\qquad e+f>0.$$

取相互独立的随机变量

$$
W_a\sim\operatorname{Exp}(a),\quad
W_b\sim\operatorname{Exp}(b),\quad
W_c\sim\operatorname{Exp}(e+f),\quad
J\sim\operatorname{Bernoulli}\!\left(\frac f{e+f}\right),
$$

并令 $S=W_c+W_a+JW_b$。$\operatorname{Exp}(r)$ 表示速率为 $r$、均值为 $1/r$ 的指数分布；$J=1$ 表示选取额外等待 $W_b$ 的路线。

相应三箱系统在持续单位输入下，对 $t>0$ 满足

$$
\begin{aligned}
x_0'&=a(1-x_0),\\
x_1'&=b(x_0-x_1),\\
x_2'&=e(x_0-x_2)+f(x_1-x_2),
\end{aligned}
\qquad x_0(0)=x_1(0)=x_2(0)=0.
$$

### 命题 4（出口分布与均值）

对 $t\ge0$，

$$
x_2(t)=\mathbb P(S\le t),\qquad
\mathbb E[S]=\frac1a+\frac{b+f}{b(e+f)}.
$$

负时间的分布函数为零。概率表示来自指数等待的卷积及按 $J$ 分支的混合；该表示在 $t\ge0$ 与出口响应相等，在 $t>0$ 满足上述微分方程，并在 $t=0$ 取所列零初值。相应证明见 [ActualTankCdf.lean](../research/exploration/phase5/lean/ActualTankCdf.lean) 及一般参数版本 [GeneralTankCdf.lean](../research/exploration/phase6/lean/GeneralTankCdf.lean)。

### 命题 5（参数比较与辨识）

固定 $a,b,e$，在允许的 $f\ge0$ 且 $e+f>0$ 范围内：若 $e<b$，则每个时刻的完成概率随 $f$ 单调不减；若 $e>b$，则单调不增；若 $e=b$，则整个完成时间分布与 $f$ 无关。

当 $a,b,e$ 已知且 $b\ne e$ 时，均值唯一确定 $f$。在 $a,b,e$ 固定时，两组允许参数 $f_1,f_2$ 的完成时间分布相同，当且仅当 $f_1=f_2$ 或 $b=e$。分布辨识结论见 [LawIdentifiability.lean](../research/exploration/phase7/lean/LawIdentifiability.lean) 的 `totalMeasure_eq_iff`。

进一步设四个参数分别属于可独立组合的非空闭区间

$$
a\in[a_-,A],\quad b\in[b_-,B],\quad
e\in[e_-,E],\quad f\in[f_-,F],
$$

其中 $a_-,b_->0$，$e_-,f_-\ge0$，$e_-+f_->0$。取

$$
(a_*,b_*,e_*)=(A,B,E),\qquad
f_*=
\begin{cases}F,&E\le B,\\f_-,&E>B.\end{cases}
$$

则这一角点同时最大化所有 $t\ge0$ 的完成概率。证明见 [RateBoxMaximum.lean](../research/exploration/phase8/lean/RateBoxMaximum.lean) 的 `selected_maximizes_all_times`。区间可独立组合是该角点结论的条件。

## 完成时间与路线标记的辨识界

固定 $a=e=1$、$b=1+\varepsilon$，其中 $\varepsilon>0$，比较低模型 $f=1/2$ 与高模型 $f=1$。先以各 $1/2$ 的概率选定一次模型，再在该模型条件下独立生成 $n$ 次任务。每次任务同时产生完成时间 $S_i$ 与路线标记 $J_i$。以下规则均为由观测唯一决定结果的可测二元规则；条件独立性指给定已选模型后的独立性。

### 命题 6（完成时间观测的统一上界）

令

$$\delta=\frac{\varepsilon}{6(1+\varepsilon)}.$$

两个单次完成时间分布具有质量 $1-\delta$ 的共同子测度，即存在一个总质量为 $1-\delta$、在所有可测集上均不超过两分布的有限测度。该子测度的 $n$ 重乘积给出质量为 $(1-\delta)^n$ 的样本共同子测度。因此，任意仅依赖 $(S_1,\ldots,S_n)$ 的上述规则，其等先验平均成功率满足

$$
p_{\mathrm{time}}\le1-\frac{(1-\delta)^n}{2}
\le\frac12+\frac{n\delta}{2}.
$$

共同部分在两模型下不能被区分，对该部分的等先验错误率至少为其质量的一半；第二步使用 $(1-\delta)^n\ge1-n\delta$。共同子测度的构造见 [ActualCompletionEventBound.lean](../research/exploration/phase10/lean/ActualCompletionEventBound.lean)，样本与规则的统一界见 [ActualCompletionTesting.lean](../research/exploration/phase11/lean/ActualCompletionTesting.lean) 的 `testSuccess_le_common_power`、`testSuccess_le_linear`。

### 命题 7（路线标记规则的下界）

两模型的路线概率分别为 $1/3$ 与 $1/2$。对 $n>0$，令 $K_n=\sum_{i=1}^nJ_i$，以

$$K_n\ge5n/12$$

判定高模型，其余情形判定低模型。条件均值与方差分别为

$$
\begin{array}{c|cc}
&\mathbb E[K_n]&\operatorname{Var}(K_n)\\\hline
\text{低模型}&n/3&2n/9\\
\text{高模型}&n/2&n/4.
\end{array}
$$

阈值距两均值均为 $n/12$。切比雪夫不等式分别给出误判概率至多 $32/n$ 和 $36/n$，故该规则的等先验平均成功率满足

$$p_{\mathrm{branch}}\ge1-34/n.$$

当 $\varepsilon=1/100$、$n=100$ 时，命题 6、7 给出

$$
p_{\mathrm{time}}\le\frac{353}{606},\qquad
p_{\mathrm{branch}}\ge\frac{33}{50},\qquad
p_{\mathrm{branch}}-p_{\mathrm{time}}\ge\frac{587}{7575}.
$$

这些是不等式方向不同的理论保证；并未给出两种观测的最优成功率。两观测均从同一随机任务中取得，分布连接及差值结论见 [ObservationContrast.lean](../research/exploration/phase12/lean/ObservationContrast.lean) 的 `branchSuccess_ge`、`timeSuccess_le`、`advantage_ge`。

[图：完成时间与路线标记的辨识保证](../research/exploration/phase12/images/observation-choice.png)。图中 $353/606\approx58.25\%$ 为全部完成时间规则的上界，$33/50=66\%$ 为指定路线规则的下界；差值至少约 $7.749$ 个百分点。

## 证明与版本记录

原主定理的形式数学源、标准内核审计、工具链和指纹绑定见[验证方法](VERIFICATION.zh-CN.md)。等待网络及下界改进分别保留各阶段的验证记录，公开范围截至 phase12；版本范围见[版本状态](../STATUS.zh-CN.md)。既有审计与独立复核的结论均按其对应文件和日期理解。

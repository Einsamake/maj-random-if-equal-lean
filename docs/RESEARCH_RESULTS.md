# 研究结果

## 同步随机多数规则的二次恢复时间

考虑 $\mathbb Z^2$ 上的同步四邻多数规则，平票在所有格点、所有轮次间独立地以公平概率取色。初态为任一纯色背景上的有限扰动。记 $s(x)$ 为初始异色集合的最小平移轴平行格点方形边长，$T_x$ 为首达常值构形的轮数，永不恢复时取 $\infty$。定义

$$\tau(N)=\sup_{s(x)=N}\mathbb E[T_x]\in[0,\infty],\qquad N\in\mathbb N_0.$$

初态 $x$ 确定，期望对平票标记取值；优化限制为尺寸恰为 $N$。该上确界由某个初态达到，完整定义与有限图形归约见[模型与记号](NOTATION.md)。

### 定理 1（二次上下界）

对所有整数 $N\ge786432000$，

$$
\frac{N^2}{56623104000}\le\tau(N)\le664066N^2.
$$

其中上界对所有 $N\ge16$ 成立。因此有渐近结论

$$
\exists c,C>0\ \exists N_0\in\mathbb N_0\ \forall N\ge N_0,
\qquad cN^2\le\tau(N)\le CN^2.
$$

定理分别由 [OriginalQuadraticLower.lean](../formal/analysis/MathResearchAnalysis/OriginalQuadraticLower.lean) 的 `tau_quadratic_lower_bound` 和 [OriginalQuadraticUpper.lean](../formal/analysis/MathResearchAnalysis/OriginalQuadraticUpper.lean) 的 `tau_quadratic_upper_bound` 组成；合并结果为 [OriginalQuadraticRecovery.lean](../formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean) 的 `tau_quadratic_bounds` 与 `tau_theta_quadratic`。

下界用实心 $N\times N$ 方块构形见证，断言存在恢复较慢的初态。上界对所有同尺寸初态成立，并推出 $N\ge16$ 时每个此类初态都有有限期望，因而几乎必然恢复。证明在取得尾界之前保留 $T_x=\infty$ 的可能性。上下界的主要约减见[证明纲要](PROOF_GUIDE.md)。

文献 [1] 的 §4.2 给出同步规则的三次期望上界，并在 Question 7.4 提出相应二次量级问题；此处的数学对象与该同步规则对应。连续时间多数过程是证明中的辅助对象，不能用其结论直接替代同步定理。文献条目及定位见[参考文献](REFERENCES.md#fates-marcovici-taati-2022)。

### 命题 2（另行保存的显示下界改进）

对所有整数 $N\ge500001$，

$$
\tau(N)\ge\frac{N^2}{576000000}.
$$

上界仍取定理 1 中的 $664066N^2$。此结果的实心方块见证也覆盖任意平移与黑白互换，见 [ImprovedOriginalLower.lean](../research/exploration/phase2/lean/ImprovedOriginalLower.lean) 的 `translated_square_witness`、`tau_quadratic_lower_bound`、`tau_quadratic_bounds`。该证明位于独立的 phase2 材料中；原主定理及其常数保持原版本。

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

原主定理的形式数学源、标准内核审计、工具链和指纹绑定见[验证方法](VERIFICATION.md)。等待网络及下界改进分别保留各阶段的验证记录，公开范围截至 phase12；版本范围见[版本状态](../STATUS.md)。既有审计与独立复核的结论均按其对应文件和日期理解。

# 模型与记号

## 同步随机多数规则

格点集合为 $\mathbb Z^2$，构形为函数 $x:\mathbb Z^2\to\{0,1\}$。对 $v=(v_1,v_2)$，令

$$
\mathcal N(v)=\{v+(1,0),v-(1,0),v+(0,1),v-(0,1)\}.
$$

给定初态 $X_0=x$，设 $\xi_{t,v}$（$t\ge1$，$v\in\mathbb Z^2$）为相互独立的公平 $\{0,1\}$ 随机变量，并记 $k_t(v)=\sum_{u\in\mathcal N(v)}X_t(u)$。演化规则为

$$
X_{t+1}(v)=
\begin{cases}
0,&k_t(v)<2,\\
\xi_{t+1,v},&k_t(v)=2,\\
1,&k_t(v)>2.
\end{cases}
$$

所有格点同时更新。随机标记预先定义于所有格点和轮次，但只在平票时使用。该定义不包含中心格 $X_t(v)$ 的投票。[规则图](images/01-rule.png)展示三种邻居计数情形。

对应源码为 [InfiniteGridModel.lean](../formal/analysis/MathResearchAnalysis/InfiniteGridModel.lean) 的 `majority4`、`synchronous`，以及 [InfiniteGridRandomDynamics.lean](../formal/analysis/MathResearchAnalysis/InfiniteGridRandomDynamics.lean) 的独立标记概率律。

## 有限扰动及其尺寸

取背景色 $b\in\{0,1\}$。初态 $x$ 相对背景的异色集合为

$$A_b(x)=\{v\in\mathbb Z^2:x(v)\ne b\}.$$

本项目的恢复时间定理限制在 $A_b(x)$ 有限的初态。$\mathbb N_0=\{0,1,2,\ldots\}$ 表示非负整数集。对有限集合 $A$，定义

$$
Q_N=\{0,\ldots,N-1\}^2,\qquad
s(A)=\min\{N\in\mathbb N_0:\exists a\in\mathbb Z^2,\ A\subset a+Q_N\},
$$

约定 $Q_0=\varnothing$，故 $s(\varnothing)=0$。若 $A\ne\varnothing$，则

$$
s(A)=1+\max\left\{
\max_{v\in A}v_1-\min_{v\in A}v_1,
\max_{v\in A}v_2-\min_{v\in A}v_2
\right\}.
$$

因此尺寸按格点列数而非坐标跨度计，也不等于点数。例如 $A=\{(0,0),(2,1)\}$ 的两坐标跨度为 $2,1$，故 $s(A)=3$；单点的尺寸为 $1$。源码 [PerturbationGeometry.lean](../formal/analysis/MathResearchAnalysis/PerturbationGeometry.lean) 中的 `diameter` 使用上述最小平移方形定义。对不受任何有限方形包含的集合，该源码取值为 $\infty$；本定理的精确尺寸条件排除了此情形。

## 恢复时间与扩展期望

记 $\mathbf0,\mathbf1$ 为两种常值构形。对确定初态 $x$，定义

$$
T_x=\inf\{t\in\mathbb N_0:X_t\in\{\mathbf0,\mathbf1\}\},
\qquad\inf\varnothing=\infty.
$$

若 $x$ 是背景 $b$ 的有限扰动，其演化始终保留某个有限包围方形外的背景色，故不能达到另一种常值构形。于是这里的首达两种常值构形，与首次恢复到原背景等价。常值构形是吸收态；初态已为常值时 $T_x=0$。定义及等价性见 [HomogeneousRecoveryTime.lean](../formal/analysis/MathResearchAnalysis/HomogeneousRecoveryTime.lean)。

期望取非负扩展值，

$$
\mathbb E[T_x]=\sum_{t=0}^{\infty}\mathbb P(T_x>t)\in[0,\infty].
$$

定义中不预设几乎必然恢复或期望有限。对 $N\in\mathbb N_0$，令

$$
\tau(N)=\sup\{\mathbb E[T_x]:\exists b\in\{0,1\},\ A_b(x)\text{ 有限且 }s(A_b(x))=N\}.
$$

期望先于对初态的优化：每个候选初态是确定的，随机性来自平票标记。条件是 $s(A_b(x))=N$，而非 $s(A_b(x))\le N$。

## 最大值的存在性

平移初态与同时交换两种颜色均不改变恢复时间分布。因此对 $N\ge2$，上述优化可归约到 $Q_N$ 内的 $0/1$ 图形，其中仅保留尺寸恰为 $N$ 的图形。该集合有限，且包含实心方块，因而非空。有限非空个扩展实数的上确界由其中一项达到，所以 $\tau(N)$ 是最大值，即使尚未证明其有限。

源码 [OriginalRecoveryProfile.lean](../formal/analysis/MathResearchAnalysis/OriginalRecoveryProfile.lean) 先以 `tau` 定义上确界，再由 `tau_eq_normalizedTau` 和 `tau_attained_finite_pattern` 证明上述归约与取到性。内部有限方形参数为 $N-2$，其实际格边长为 $(N-2)+2=N$；这里需要 $N\ge2$。$N=0,1$ 分别由 `tau_zero`、`tau_one` 处理，得到

$$\tau(0)=0,\qquad\tau(1)=1.$$

后一等式也可直接从规则读出：单个异色格及其所有邻居在一轮后均为背景色。`tau_attained_all` 合并了所有 $N\in\mathbb N_0$ 的最大值存在性。

## 主要记号

| 记号 | 含义 |
| --- | --- |
| $N$ | 原同步模型的精确扰动尺寸 |
| $T_x$ | 原同步模型首达常值构形的轮数，允许 $\infty$ |
| $\tau(N)$ | 尺寸恰为 $N$ 时的最坏扩展期望 |
| $L$ | 下界辅助方形的半边长参数，辅助边长为 $2L+1$ |
| $M$ | 上界混合边界辅助方形的边长，取 $M=8N+1$ |
| $t$ | 辅助随机时钟的连续时间 |
| $k,b_N$ | 调度层数及用于重启估计的同步轮数 |
| $a,b,e,f$ | 独立等待网络的速率参数；此处 $b$ 与背景色、$b_N$ 无关 |

辅助时钟的连续时间与原模型的同步轮数通过概率比较相联系，二者不直接等同。具体尺度见[证明纲要](PROOF_GUIDE.md)。

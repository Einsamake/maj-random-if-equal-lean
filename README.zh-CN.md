# 二维随机多数元胞自动机的恢复时间

[English](README.md) | **简体中文**

本仓库给出二维同步随机多数规则从有限扰动恢复到纯色背景的二次时间界，并提供数学论文与 Lean 形式化证明。研究问题是：初始扰动的最小包围方形边长为 $N$ 时，最坏期望恢复时间如何随 $N$ 增长？结论为最坏期望恢复时间 $\tau(N)=\Theta(N^2)$，对应 Fatès、Marcovici、Taati 在 [Question 7.4](docs/REFERENCES.zh-CN.md#fates-marcovici-taati-2022) 中提出的二次量级问题。

## 模型与问题

在 $\mathbb Z^2$ 上，每个格点取色 $0$ 或 $1$。每轮所有格点同时读取上一轮的上、下、左、右四邻颜色：严格多数决定新颜色，两色各占两个邻居时，以独立公平硬币取色。中心格自身不参与投票，硬币在格点和轮次之间相互独立。

初态为任一纯色背景上的确定有限异色集合 $A$。令

$$
Q_N=\{0,\ldots,N-1\}^2,\qquad
s(A)=\min\{N\in\mathbb N_0:\exists z\in\mathbb Z^2,\ A\subset z+Q_N\}.
$$

这里 $\mathbb N_0$ 为非负整数集，约定 $Q_0=\varnothing$。尺寸按格点列数计：$s(\{(0,0),(2,1)\})=3$。记 $T_A$ 为首次恢复原背景的轮数，永不恢复时取 $\infty$，并定义

$$
\tau(N)=\sup_{s(A)=N}\mathbb E T_A\in[0,\infty].
$$

期望对平票硬币取值，上确界覆盖两种背景以及尺寸恰为 $N$ 的所有确定初态。[模型与记号](docs/NOTATION.zh-CN.md)给出完整定义。

## 主要结果

对所有整数 $N\ge16$，

$$
\frac{N^2}{850000}\le\tau(N)\le664066N^2.
$$

因此最坏期望恢复时间具有二次量级。对 $N\ge2$，填满方形已经实现极值：

$$
\tau(N)=\mathbb E T_{Q_N}.
$$

这里 $T_{Q_N}$ 指零背景上全异色 $N\times N$ 方形的恢复时间；颜色对称性给出另一背景的同一结论。

令 $T_N=T_{Q_N}$，$m_N=1+2\lfloor(N-1)/2\rfloor$。对每个 $N\ge1$，有 $\mathbb E T_N\ge\max\{m_N,N^2/850000\}$。$m_N$ 是可能消亡的第一轮，奇数边长时为 $N$，偶数边长时为 $N-1$。若 $q_N=\mathbb P(T_N=m_N)$，则

$$2^{-2N^2}\le q_N\le 2^{-\lfloor N^2/8\rfloor}\qquad(N\ge7).$$

因此，方形可以在线性时间内消亡，而恰在最早一轮消亡的概率随面积指数衰减。[最早消亡的证明与配图](research/lower-bounds-2026-11-19/earliest.md) · [渐近期望与早消亡尾界](research/lower-bounds-2026-11-19/lower-tail.md)

下列晚恢复估计对尺寸 $s(A)=N$ 的任一允许初态一致成立。令

$$
b_N=331776N^2+257,\qquad
a_N=\frac{32}{8N+1}+\frac{12}{5}N^2\,2^{-(1296N^2+1)}.
$$

对 $N\ge16$ 和整数 $j\ge0$，

$$
\mathbb P(T_A>jb_N)\le a_N^j,\qquad
0\le a_N\le\min\{1/2,5/N\},\qquad
\tau(N)\le\frac{b_N}{1-a_N}.
$$

因而在明确的二次期限 $b_N$ 内恢复的概率一致趋于 $1$。此外，对上述尺寸和初态，任意固定实数 $r>0$ 均满足 $\mathbb E T_A^r\le C_rN^{2r}$；对 $0<\lambda<\log(2)/332033$，有

$$
\sup_{N\ge16}\ \sup_{s(A)=N}
\mathbb E\exp(\lambda T_A/N^2)<\infty.
$$

常数及声明入口见[研究结果](docs/RESEARCH_RESULTS.zh-CN.md)。11 月 17 日的论文给出二次阶、块尾和矩估计。11 月 19 日的下界补充给出上述全尺度期望下界、最早消亡时刻及其概率。

## 证明思路

共同平票标记下的多数更新具有单调性。扰动不能越出其初始包围方形，因此任意初态可由同一方形中的全异色初态支配。这给出方形极值，并把无限格点问题归约到固定背景边界的有限方形。

两侧估计通过一个连续时间辅助过程建立：每个格点以独立速率 $1$ 的泊松时钟逐点更新。下界在边长 $2L+1$ 的方形内取截角区域，其中 $L=\lfloor(N-1)/2\rfloor$，与 $N$ 同阶。区域中的修改过程在随机更新后附加删除，并在保护区域首次有格点失去异色时冻结，使几何形状可控。失守需要丢失 $\Omega(L^3)$ 的加权面积，而原始更新的加权损失漂移至多为 $O(L)$，全部附加删除的加权损失为 $O(L^2)$。原时钟过程的灭绝必导致保护失守，因此面积平衡给出原时钟过程在 $L^2$ 时间后仍存活的正概率。

上界使用南、西边界为 $0$，北、东边界为 $1$ 的辅助方形，从全 $1$ 初态出发。它保持阶梯形界面，界面上的角翻转对应一维有限路径上速率 $1/2$ 的相邻粒子交换。离散热方程控制粒子密度，异点非正协方差控制计数波动；两者给出指定角落区域在 $O(N^2)$ 物理时间后清空的概率下界。单调耦合将该事件用于零边界的目标方形。

删失比较与随机更新次序的概率估计，将这两种连续时间估计转成原模型的同步轮数界。最后，对每个时间块末观察到的构形条件重启，得到上面的几何尾界。[证明纲要](docs/PROOF_GUIDE.zh-CN.md)给出估计之间的连接；[英文论文](research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf)给出二次阶及晚恢复界的论证。

## 阅读与复现

| 内容 | 入口 |
| --- | --- |
| 当前论文 | [60 页英文 PDF](research/revision-ab-2026-11-17/paper/output/pdf/quadratic-recovery-v6.pdf) · [正文与六幅图](research/revision-ab-2026-11-17/paper/paper.md) |
| 定义、定理与证明结构 | [模型与记号](docs/NOTATION.zh-CN.md) · [研究结果](docs/RESEARCH_RESULTS.zh-CN.md) · [证明纲要](docs/PROOF_GUIDE.zh-CN.md) |
| 形式化与复现 | [工具链、构建和审计](docs/VERIFICATION.zh-CN.md) · [当前定理源码](research/revision-ab-2026-11-17/lean/OriginalConsequences.lean) |
| 文献与版本 | [参考文献](docs/REFERENCES.zh-CN.md) · [版本状态](STATUS.zh-CN.md) · [历史材料索引](docs/ARCHIVAL_RECORD.zh-CN.md) |

可从[中文文档索引](docs/INDEX.zh-CN.md)或[中文研究索引](research/README.zh-CN.md)浏览。原证明及新增结论均有标准 Lean 内核构建和公理审计记录，具体对象和版本集中列于验证页。当前论文为工作稿。

仓库另有[随机等待网络的参数比较与统计辨识结果](docs/RESEARCH_RESULTS.zh-CN.md#随机等待网络)。该部分有独立模型和证明入口，与二维恢复定理分开组织。

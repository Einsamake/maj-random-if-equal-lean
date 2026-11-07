# 二维随机多数元胞自动机的恢复时间

本仓库研究二维整数格上的同步四邻多数规则，并给出有限扰动的最坏期望恢复时间为二次量级的证明。模型对应于 Fatès、Marcovici、Taati 关于随机平票多数规则的恢复时间问题，见[文献 [1]，§4.2 与 Question 7.4](docs/REFERENCES.md#fates-marcovici-taati-2022)。

## 模型与主定理

每个格点取颜色 $0$ 或 $1$。每轮更新同时读取上一轮的上、下、左、右四邻颜色：严格多数决定新颜色；两色各占两个邻居时，以各 $1/2$ 的概率取色。平票选择在不同格点、不同轮次间相互独立，中心格自身不参与投票。

初态是在某一纯色背景上的有限异色集合 $A\subset\mathbb Z^2$。令 $s(A)$ 为包含 $A$ 的最小平移轴平行格点方形的边长，按格点列数计；例如 $s(\{(0,0),(2,1)\})=3$，而该集合只有两个点。恢复时间 $T_A$ 为首次回到纯色背景的轮数，永不恢复时取 $\infty$。定义

$$
\tau(N)=\sup_{s(A)=N}\mathbb E[T_A]\in[0,\infty],
$$

其中初态确定，期望仅对平票随机性取值。平移不变性与黑白对称性将这一上确界归约到有限非空的归一化图形集，因此它可写成最大值。两种背景均包括在内。完整定义及最大值的存在性见[模型与记号](docs/NOTATION.md)。

**定理。** 对所有整数 $N\ge786432000$，

$$
\frac{N^2}{56623104000}\le\tau(N)\le664066N^2.
$$

上界单独对 $N\ge16$ 成立。因此存在与 $N$ 无关的正常数 $c,C$ 及有限阈值 $N_0$，使得所有 $N\ge N_0$ 均满足 $cN^2\le\tau(N)\le CN^2$，即 $\tau(N)=\Theta(N^2)$。

下界以实心方块为见证；上界覆盖所有尺寸恰为 $N$ 的有限扰动。下界使用辅助时钟过程的加权面积估计，上界使用阶梯边界的粒子表示、热衰减与重启尾界。[证明纲要](docs/PROOF_GUIDE.md)给出主要约减和显示常数的来源。形式定理位于 [OriginalQuadraticRecovery.lean](formal/analysis/MathResearchAnalysis/OriginalQuadraticRecovery.lean)，声明名为 `tau_theta_quadratic`。

独立的后续证明将显示下界改进为

$$
\tau(N)\ge\frac{N^2}{576000000}\qquad(N\ge500001).
$$

该结果位于 [ImprovedOriginalLower.lean](research/exploration/phase2/lean/ImprovedOriginalLower.lean)，与原主定理分别保存。

## 相关结果与材料

仓库还包含一个独立的随机等待网络，研究出口响应的概率表示、参数比较及观测量对二元辨识的影响。其模型、条件和定理见[研究结果](docs/RESEARCH_RESULTS.md)；它与上述二维自动机是不同的数学对象。

| 内容 | 入口 |
| --- | --- |
| 模型、尺寸、恢复时间与最坏期望 | [模型与记号](docs/NOTATION.md) |
| 主定理及等待网络结果 | [研究结果](docs/RESEARCH_RESULTS.md) |
| 二次上下界的主要推导 | [证明纲要](docs/PROOF_GUIDE.md) |
| 工具链、构建与既有审计记录 | [验证方法](docs/VERIFICATION.md) |
| 公开材料范围 | [版本状态](STATUS.md) |
| 参考文献 | [参考文献](docs/REFERENCES.md) |
| 证明方法、图示与算例 | [证明方法说明](docs/proof-discovery/README.md) |

形式数学源、历史审计和封存材料按各自版本保留。既有审计的检查对象、日期和结论见[验证方法](docs/VERIFICATION.md)，原版本入口见[历史材料索引](docs/ARCHIVAL_RECORD.md)。

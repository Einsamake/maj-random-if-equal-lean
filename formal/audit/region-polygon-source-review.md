# Region、Polygon 与原 Good：原文及欧氏长度接口核对

2026-10-17，独立只读审阅者 `/root/modified_clock_independent_audit`。本文件是来源与实现接口建议，不是新 Lean 构建或完成证明；本代理未修改正式 Lean。

## 原始几何对象

重新直接读取 [CMST v2 §8 Definition 7(a–f)](https://arxiv.org/html/1007.3599v2)，特别是 HTML 1005–1034。原方格以负自旋格点为中心、边平行坐标轴、**物理边长1**；Gamma 是这些实际方格的并集。Good 同时要求整条边界为简单闭曲线、其**几何长度**等于两向包围盒跨度和的2倍、内域 D 被负自旋包含，以及多数清理后不变。Good 的内域条件只要求 D；D 与外边界的并集出现在停止条件中。

因此不能仅因已有暴露侧边计数等式，就把它当作已经证明的原几何长度结论。对真实简单多边形，两者相等应来自其完整实际边界分解、每侧物理长度1、无内部重叠；也可直接以真实欧氏曲线的总变差定义并证明弧长。

本工程初始剪角域组装几何 Good 的自然尺寸下限是 L≥1：初态稳定和既有全边界单轨道都在此成立，L=0 单格的多数清理并不保持。L≥40 是后续四向方块及显式面积常数的技术范围，不是原 Good 定义里的条件。

## 可形式化的实际证书

对有限占用集合 S，候选几何证书应包含：

- S 是真实 clippedDomain 内的状态；
- 存在 m>0 与连续 gamma:Real→EuclideanSpace Real (Fin 2)，首尾 gamma m=gamma 0，在[0,m)单射，gamma 的[0,m]像**恰为实际物理方格并集的整个 frontier**；
- gamma 在[0,m]的真实欧氏弧长／总变差等于实际 frontier 两个坐标跨度和的2倍；
- 实际 innerDiamond L 包含于 S，且实际 cleanup S=S。

这只是初态组装路线，不声称任意状态的一般 Good 等价或动态保持已证明。坐标极值也须与真实 frontier 接上：初始放大坐标为±(2L+1)，物理坐标因而是±(L+1/2)。每向物理跨度2L+1，物理周长8L+4。

## 已核对的固定 mathlib 接口

以下均直接读取本工程固定提交 `54c01c3314d33d15d77893cbe4e0472ff26bb34d` 的源码，未用不同版本推断。

| 用途 | 实际接口及位置 |
| --- | --- |
| 真正欧氏平面 | `Mathlib/Analysis/InnerProductSpace/PiL2.lean`：`EuclideanSpace Real (Fin 2)` 是 L² 范数，不是函数空间默认 sup 范数；`!₂[x,y]` 为 `WithLp.toLp 2 ![x,y]`。 |
| 坐标距离 | 同文件178、182行 `EuclideanSpace.dist_eq`、`EuclideanSpace.dist_sq_eq`，将距离或距离平方化为两坐标距离平方和；`Fin.sum_univ_two` 展开两个坐标。 |
| 轴向平方根 | `Mathlib/Analysis/Real/Sqrt.lean:188` 的 `Real.sqrt_sq_eq_abs`；也可用 dist_sq_eq 加距离非负，避免平方根化简。 |
| 坐标 homeomorphism | `EuclideanSpace.equiv (Fin 2) Real`（PiL2:296）到 `Fin2→Real`，再复合 `ContinuousLinearEquiv.finTwoArrow Real Real`（`Topology/Algebra/Module/Equiv/Pi.lean:145`）到 `Real×Real`，取逆即可搬运原 product topology 的曲线／区域。它是连续线性同构，**不能当作等距**。 |
| 连续直接嵌入 | `PiLp.continuous_toLp`（`Analysis/Normed/Lp/PiLp.lean:546`）接两个连续坐标；或使用上述连续线性同构。 |
| 从距离得等距 | `Isometry.of_dist_eq`（`Topology/MetricSpace/Isometry.lean:57`）。 |
| 实际弧长 | `Topology/EMetricSpace/BoundedVariation.lean` 的 `eVariationOn`，取 ENNReal 扩展总变差。 |
| 按段相加 | 同文件 `eVariationOn.sum'`（约427行），对单调分割 `I n=(n:Real)` 把[0,N]变差分成 N 个单位闭区间。 |
| 一段上下界 | `LipschitzOnWith.comp_eVariationOn_le`（1173行）及 `eVariationOn.edist_le`（187行）；`eVariationOn_id_Icc`（1157行）给恒等函数区间长度。 |
| 接实际 trace | `eVariationOn.congr`（184行）允许用真实 trace 在每个单位闭区间上的已证仿射等式替换。 |

## 最省而严格的欧氏路线

现有 Plane=Real×Real 的默认度量为 max 度量；其 topology 可直接通过上述同构搬到欧氏平面，**长度结论不能默认沿用**。

定义物理边参数为 `!₂[(segmentPoint e t).1/2,(segmentPoint e t).2/2]`。真实四个方向中总有一个坐标常量，另一个坐标是常数加 t 或减 t。因此直接在欧氏平面证明两参数间距离恰为 abs(t−u)，得到该边参数在整个 Real 上为 Isometry。

接着可选择两种都不假设目标长度的证明：

1. 由 Isometry 的 edist_eq 和 eVariationOn 定义证明等距复合保持变差，每一物理轴向段[0,1]的变差为1；
2. 或用1-Lipschitz给上界1，用真实端点距离1给下界1。

对整个实际 trace，单位区间[i,i+1]上的物理欧氏参数等于对应物理边参数再平移 t−i；平移也等距。由每段变差1及 sum'，总弧长严格等于真实侧边数 N=8L+4。这避免了另证 max 度量与欧氏度量在整条曲线上的变差相同，也无需先形式化一般 Hausdorff 测度。

frontier 的两个包含、完整边界识别、连续闭曲线去终点单射、物理缩放与弧长都实际构建通过后，才可以把这些与原有 D 包含和 cleanup 稳定组装成**初始** Good 证书。任意状态的保持、角点／更新分类及概率核心仍是后续任务。


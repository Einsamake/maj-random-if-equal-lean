# 真实矩方程与异点负相关阶段：独立语义复核

结论：本阶段已从原混合边界过程的真实时钟和标记 law 推出一、二点矩的积分方程与正时间 ODE，再证明不同槽位的协方差非正，并得到实际中心均值能量恒等式。下列七个非本人撰写模块的陈述与证明匹配，未发现语义漏洞。实际统一内核输出与全部源指纹的对应另见 mixed-moments-independent-final-binding-evidence.json；旧241源验收不能代替本阶段新增源验收。

## 审查责任

复核者为 AI `/root/sync_profile_review`，不是人类专家。独立审查 MixedClockMoments、FiniteMomentRegularity、FiniteExclusionEnergy、FinitePermutationComparison、MixedMomentEvolution、MixedClockCovariance、MixedMomentEnergy。本复核者撰写了 PositivePartSquare，故不对它作自己的独立语义认证；root 已独立逐条阅读其零点两半轴导数拼接、连续导数和四符号支持不等式，确认语义正确。全部八源仍须一起绑定真实标准内核输出。

## 已逐项核对

1. **真实期望，先可积后交换。** rho 是实际 slot density 期望，g 的两因子来自同一原始样本，未假设槽位独立。布尔值的0到1界和实际 endpoint 可测性先证明每个单点/乘积观测量可积，才交换有限 edge sum 与期望。rho/g 时零初值由真实原时钟所有事件时间严格为正推出。积分方程来自已验收的实际 MixedClockDynkin，保留每 edge 1/2 和物理时间 (0,T]。
2. **正则性无循环。** 泛型系统只以紧时间积分可积和积分表示为结构输入；先由积分原函数得各坐标在[0,∞)连续，再由有限线性算子得右端连续，最后 FTC 得 t>0 的导数。MixedMomentEvolution 逐个用上述真实积分方程/可积性解除这些结构输入，未把正则性或 ODE 当作真实过程的额外假设。
3. **质量和能量系数准确。** 实际形状的粒子基数为 M=parameter L+2，槽数为2M。rho 总质量直接从逐样本的真实粒子基数和已证明样本可积的有限积分换和得到。任意列出的 swap edge 只计一次且原率1/2，离散分部积分带1/2，平方质量导数则恰为−Σedge(diff)^2；自 loop 为0，未多添或漏掉因子2。泛型能量的导数结构前提在实际中心均值能量中由真实 rho ODE 解除。
4. **比较原理证明本身已给出。** FinitePermutationComparison 的每个作用是真正有限置换。支持不等式逐坐标求和，右边经真实置换换元完全相消，给正部平方能量耗散；减去非负源只会进一步降低该能量。初始每坐标非正使能量为0，能量在[0,∞)连续、仅内部须可导，反单调性推出所有坐标始终非正。未对不可微最大值取导，也未误用范数 Gronwall。
5. **对角线严格排除。** 协方差比较状态为 Pair={(i,j):i≠j}，同一 swap 同时作用两指标，经双向 distinctness 证明给出真正的子类型置换，绝无跳入对角线。C=g−rho_i rho_j 的实际导数为 Q2 C−source；source 恰是先前证明的 product_defect，在异点上等于非负平方乘连接 edge 基数。源的负号、率1/2、两方向 edge 的计数均与原算子一致。
6. **真实负相关没有未解前提。** C 的连续性和导数来自实际 Evolution，C0=0来自实际固定布尔初值，source≥0来自已证代数符号。最终 covariance_nonpos 和 offdiag_moment_le_product 解除比较原理的全部结构输入，只保留模型参数、固定单调形状初值、t≥0及 i≠j。对角 Bernoulli 方差并未被错误声明非正，未将占据独立作为假设。
7. **实际中心能量。** 中心取rho−1/2，2M槽和总质量M给零均值；固定布尔初值使每槽中心平方为1/4，总能量H0=M/2，无初态独立假设。H连续至0，正时间H'=−实际edgeEnergy，均在原law下成立。此处尚未声明从Poincare到指数衰减或概率界。

## 证明范围与后续缺口

本阶段仍使用原 DropletClockLaw 的 L 参数，实际方格边长 M=parameter L+2；只有L≥1时才等于2L+1，L=0时自然数截断给parameter 0=0、实际边长2；有限状态、有限算子和正则性泛型化都不等于任意边长的时钟限制 law 已证明。新模块没有改动原模型、真实标记身份、时间尺度或含∞恢复时间。

异点负相关是本阶段已证明的实质概率结论。热衰减、右半粒子数方差/集中、跨尺寸耦合、原同步比较后的重启及最终二次期望上界仍须补齐；完整Θ主定理未完成。保守常数提醒：当前松Poincare给 H'≤−H/(4M²)、H0=M/2；要由此取得右半均值至少M/4，旧候选t=8M²略不足，后续宜重新核对或用更保守时间，不能将候选常数当已验收。

## 本报告读取的源指纹

- `MixedClockMoments`: `aa0a21d873c640250a834fd8fc638c40eafb44f139fb7ba17d655069551dc17f`
- `FiniteMomentRegularity`: `f42002733d345aa3c3da012ee4fa64430acce9bd84d4ad224d22008bce78293e`
- `PositivePartSquare`: `e79122c726f1c76073da35e28e0396c7977bed04bfbff9b887c6d37190f741d4`
- `FiniteExclusionEnergy`: `d21596570a6fc66b0f84e04b5508eba06e3f82eca369c2a450295cf947e7f9eb`
- `FinitePermutationComparison`: `60d401a0708168d8c84cb23b8a21b91ce6d51187790747dbe06cbd94c33d0f00`
- `MixedMomentEvolution`: `607c3ba4bf08dae7977a2522de2069d171f63c414c9c71dd1a429b069629567e`
- `MixedClockCovariance`: `6c6ba7d5702153a79caeca65d26b23a38778e96416103d3e338f92bce4947854`
- `MixedMomentEnergy`: `a527c1b0ebd66c3928a16427e37dce1fbb2f294be54ab4fcb9d9e5291fecf104`

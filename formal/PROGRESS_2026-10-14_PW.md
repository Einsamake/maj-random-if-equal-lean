# 有限字 PW 与零温实际执行：阶段验收

统一验收时间：2026-10-14 **20:56:32 +08**。先完成用户要求的目录清理和路线复盘，再开始本阶段；期间子代理曾因额度中断，用户再次要求继续后检查到可用额度，接续已有源码完成验收。没有新建调度或重复文献检索。

**具体固定零边界方形、最大初态、任意有限更新字的 PW 随机偏序及零温实际执行积分比较已经通过 Lean。完整同步 CA `τ(n)=Θ(n²)` 仍未形式化。**

## 最终交付的数学接口

使用真实 `SquareSpin.Config n`，点态 `false < true`，分析方形边长 `n+2`。令 `topConfig n := fun _ => true`，`φ` 为任意单调实函数，`short.Sublist full` 表示时间正序中的删减子字。

1. `SquarePWCensoring.warmWord_censoring`：仅要求 `β≥0`、`Sublist` 和 `Monotone φ`，证明

   `warmWord β full φ top ≤ warmWord β short φ top`。

2. `actualMajorityWordMean_censoring`：以已有固定有限字零温极限传递不等式，得到真实公平平局多数更新均值的同向比较。
3. `chronological_fair_execution_censoring`：对真实事件身份字 `full.Nodup` 及 `short.Sublist full`，证明两侧分别使用正确长度公平乘积测度的实际执行积分比较。时间正序字送入 `freshRun` 时取 `.reverse`。
4. `freshExecutionLaw_censoring`：同一结论直接表述为真实有限执行测度上的积分偏序。

最终接口不接受 PW、密度保持、等待 law 或其他核心概率结论作为输入。同一个站点可以多次更新，但不同事件不能复用同一身份。两侧是分布比较，不是共用标记后的逐样本大小。最大初态限制不能扩张为任意确定初态。

## 实际证明链

| 模块 | 新增公开定理 | 完成的内容 |
|---|---:|---|
| `SquareAttractivity` | 7 | `β≥0` 时实际四邻局部场／热浴概率单调；单步及有限字保持单调测试函数；任意实 β 下保持测试函数点态序 |
| `SquarePWMeasure` | 10 | 真实核的前向质量演化、与现有后向 `warmWord` 的对偶；以实际详细平衡证明密度演化恒等式；最大态质量及密度单调 |
| `SquarePWDrop` | 5 | 同站布尔纤维上配置可比；真实可逆核的 Dirichlet 恒等式；单调 Gibbs 密度下单步更新降低单调期望 |
| `SquarePWCensoring` | 6 | 密度保持、Sublist 归纳、最大态热浴有限字 PW、零温及实际执行积分 |

单步 Dirichlet 结论本身对任意实 β 成立，因为核只在可比的两点纤维之间转移；铁磁条件 `β≥0` 用于后续更新保持密度单调。删除一步后把偏序传播到完整后缀，得到任意多步删减。零温传递只使用最终 `β≥0`，没有把 β=∞ 时退化的 Gibbs 质量当成处处正。

所用密度方法来自 [Peres–Winkler §2](https://arxiv.org/html/1112.0603)，本项目完成的是所需具体完整布尔配置空间版本，不是原文一般硬约束／total variation 全部结论。

## 验收证据

- 新增 **4 模块、28 条公开辅助定理**；分析工程现为 **64 模块、842 条公开定理、65 份正式 Lean 源**。
- 统一总构建与 842 条逐定理公理审计均退出 `0`；只出现标准 `Classical.choice`、`Quot.sound`、`propext`。
- 禁用构造扫描通过，无占位、自定义公理、`unsafe`、`native_decide`、`implemented_by` 或跳过内核。
- 自有源无编译／linter 警告；九项第三方 checkout 本地改动提示保留。
- 核心 125 条定理及模型定义未改，原验收源哈希仍匹配；合计 **967 条辅助定理**，包含迁移和基础引理，不表示独立发现数或主定理完成比例。
- 实际版本保持 Lean 4.35.0-rc4 与 mathlib `54c01c3314d33d15d77893cbe4e0472ff26bb34d`。核心继续使用独立 Lean 4.35.0。
- 原始证据为 `audit/analysis-validation.json`、`analysis-build.log`、`analysis-axioms.log`；上一阶段 16:33 审计已精确恢复到 `audit/history/2026-10-14-1633/`。

[独立语义审查](audit/square-pw-review.md) 核对了质量对偶、密度、删更新方向、最大态、零温与积分反序，未发现具体缺口；它不是外部数学认证。审查涉及的源指纹须与统一验收一致。

## 仍未完成及下一步

确定有限字 PW 阶段合同已闭合，见 [已验收合同](FINITE_PW_CONTRACT.md)。下一步为 [实际扫描嵌入和随机时钟比较](../README.md)：先补 rank 槽到完整扫描字的 Sublist，再对 clock-only 随机字连接两向恢复事件。

随机时钟平均和恢复概率比较、CMST／FSS 二维方岛、真实块重启、原尺寸／初态连接及最终期望常数均未完成。CMST 的上尾依赖 FSS，不能将完整主定理描写为只剩普通接口参数。完整未来 Poisson 向量强 Markov 未证，但当前专用等待和标记接口不需要重做。

原研究稿、失败记录和文献核查全部保留；未检出精确公开解答不证明开放性或新颖性。未联系作者或对外发布。

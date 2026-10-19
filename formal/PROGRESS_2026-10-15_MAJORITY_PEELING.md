# 严格多数清理：有限终止与真实规则桥接

2026-10-15。本阶段仅含 `FiniteMajorityPeeling` 和 `GridMajorityPeeling` 两个模块。按用户最新要求，本阶段统一验收、独立复核及材料整理完成后暂停，不继续后续楔形、轮廓或改造随机过程。

## 实际证明

`FiniteMajorityPeeling` 有26条公开定理。环境顶点类型可以无限，只要求初始占据集合S为有限集。定义邻数为实际邻集合与S的交集基数；并行清理保留当前占据且邻数至少2的点，`core` 是不超过S.card次的有界清理迭代。

稳定性是证明结果：有限严格包含导致基数下降，得到有限步稳定，再证明core是S内最大的稳定子集。由此给出core的单调性及幂等。合法单点删除必须删去当前S中的点且其邻数小于2；每步基数严格下降。实际证明存在终止合法串，所有已经无合法删除的终态等于同一个core，因此不依赖合法删除次序。没有将终止、固定点存在或结果唯一当成最终输入。

`GridMajorityPeeling` 有21条公开定理。真实整数格四方向互异，邻集合基数恰4，集合邻数等于现有四个Boolean输入的toNat之和。负自旋编码true、正背景编码false；邻数小于2时，原始规则对任何tie标记都返回false。邻数恰2时则返回真实tie标记，清理不能预先删除平局点。

证明单点真实写回恰等于从有限负自旋集合擦除该点，同时对旧有限方形模型证明现有 `SquareSpin.cellUpdate` 的对应。真实格点cleanup直接实例化泛型core，得到收缩、稳定、单调、幂等、合法删除可达性及终态唯一；合法删除与实际无限格或有限方形单点更新相符。

## 验收与语义范围

本阶段新增47条公开定理；最终总构建、显式标准 `--trust=0` 退出码、全部源SHA和警告见 [统一验收JSON](audit/analysis-validation.json)。前一1207条基线、构建及公理输出已保存在 `audit/history/2026-10-15-1539/`，未覆盖历史记录。

未编写本阶段Lean的独立AI代理对照 [CMST v2 §8 Definition 7](https://arxiv.org/html/1007.3599v2) 审查清理含义、阈值及终态条件，见 [语义报告](audit/majority-peeling-semantic-review.md) 和 [源指纹／全部公理输出核对](audit/majority-peeling-independent-evidence.json)。AI审阅不是人类专家签署，不声称绝对无漏洞。

## 未证明的后续内容

2-core稳定不能推出CMST的Good条件：简单轮廓、周长关系与内域包含均是额外几何义务。本阶段没有构造带剪角mask的随机改造链，没有证明任意事件字或停住后过程的随机law，也没有证明面积损失、FSS／CMST二次概率尾或最终二次期望界。

`ClippedDiamondGeometry.lean` 与 `DropletModifiedWord.lean` 均未创建；后续仅保留 [依赖计划](CMST_DEPENDENCY_PLAN.md)，不能把计划当成Lean结果。完整原问题 `τ(N)=Θ(N²)` 仍未形式化。暂停后的接续见 [NEXT_PHASE](../README.md)，须等待用户新指示。

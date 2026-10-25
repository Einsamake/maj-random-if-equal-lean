# 原同步、原exact-N二次期望下界

主定理的下界现在已经实际核验；二次上界和完整Θ仍未完成。

## 严格数学结果

对每个 N≥786432000：

$$
\operatorname{ofReal}(N^2/56623104000)\le\tau(N).
$$

τ 是原无限二维同步四邻规则下、尺寸恰N、到两种齐次背景的最坏扩展期望。∞仍保留。具体初态是N×N全黑方块，故这是最坏期望下界，不是每个图形的恢复时间下界。

SyncLowerScale令q=⌊L²/196608000⌋、k=q−1，证明k≥L²/393216000、调度时长≤L²/12288000和真实调度误差≤1/4。SynchronousQuadraticTail直接用已证真实物理均值界控制早时刻，并从同一clock law可测灭绝事件的补集得到生存≥1/2；实际two_way_clock_tail第一方向给原同步尾≥1/4。

ExtendedTailLower把常数尾集指示函数直接放入ENat.toENNReal非负扩展积分，给kP(T>k)≤E[T]，不要求T有限或可积。OriginalQuadraticLower取L=⌊(N−1)/2⌋，用同一N方框支持比较处理奇偶，再对两背景首达及exact-N优化供上述结论。最终模型定理没有核心概率或漂移作为输入。

## 实际验收

分析212个证明模块、2826条辅助定理、213份分析源；核心125条定理及1模型、8源未变。合计221份正式源、2951条辅助定理与1个模型，完整公理输出2952项。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-25T15:11:55.361456+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，本次未重编核心。

本批4模块26theorem/29named：scale11、connection6、profile12三个专项实际build0及标准trust0审计0，零新Lean warning。旧217完整JSON、build、axiom输出和入口表归档before-sync-lower-stage-2026-10-25，不拿旧验收覆盖新源。

[独立语义审查](audit/sync-lower-independent-review.md) · [221源完整绑定](audit/sync-lower-independent-final-binding-evidence.json) · [统一核验](audit/analysis-validation.json) · [最终定理源码](analysis/MathResearchAnalysis/OriginalQuadraticLower.lean)。

独立AI不是人类专家认证；本阶段不证明任何原同步二次上界，也未优化巨大常数。

## 下一步

构建南/西白、北/东黑的有限混合边界过程，证明真实单点更新与下方闭合白色区域的阶梯边界对应，再推进有限SSEP的一、二矩和收缩概率。该上界路线仍待形式化，不能以已有下界或重启工具代替。


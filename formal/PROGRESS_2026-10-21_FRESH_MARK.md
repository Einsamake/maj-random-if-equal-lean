# 真正停时后的实际新标记

完整τ(N)=Θ(N²)主定理尚未完成。本阶段新增3模块、39条定理、44个命名声明，统一验收为2026-10-21T05:39:35.916899+08:00。当前分析2321条定理、171源，加核心8源共179份正式源。

| 模块 | 定理 / 全命名声明 | 已证明内容 |
|---|---:|---|
| [UnrevealedMarkInvariance](analysis/MathResearchAnalysis/UnrevealedMarkInvariance.lean) | 9 / 12 | 未到时identity的标记替换保持原历史、真正停时及停止历史；单坐标fair flip可测、互逆且保持实际无限product measure |
| [StoppedMarkSlices](analysis/MathResearchAnalysis/StoppedMarkSlices.lean) | 12 / 13 | 真正停时后第一site-ring候选互斥；flip同时保持候选、停时、F_R事件和实际wait；真实两Bool切片等质量，各为总事件质量的一半 |
| [StoppedFreshMark](analysis/MathResearchAnalysis/StoppedFreshMark.lean) | 18 / 19 | 实际Nat.find下一identity的mark可测，真实AE候选覆盖与可数互斥分解，fair限制law、F_R独立及jointwaiting尾，实际boundedExit三实例 |

令R为原到时/已揭示标记历史的停时，R几乎处处有限；固定site v。候选k要求R严格早于第k次到时，所有j<k已在R以前到时。若不存在未来到时，nextMark定义为false；可测fiber公式明确保留该回退分支，随后用同一个全测集上的实际clock cofinality与R有限性排除它，允许R依赖已揭示marks。

下一标记B的完整限制law为 μ.restrict(E)推前B = μ(E) • fair，E属于F_R。因此B为公平硬币且与停止σ独立。此结论不需要R非负；nonnegative只在Exp residual law中使用。若R非负，W为实际单site残余wait，则任意u≥0、b∈Bool：

μ(E ∩ {u<W} ∩ {B=b}) = exp(-u) · μ(E) · fair{b}。

这里先直接证明G=E∩{u<W}的flip不变性，再将每个候选的half因子相加，最后接已验收的Exp(1)等待law；没有从两个边缘独立结论误推联合独立。严格未揭示条件R<arrival不可改成≤，等号时mark已被历史揭示。

实际保护退出在ENNReal先cap有限T，∞cap=T，再转Real，finite/nonnegative/stopping均由既有证明提供；本阶段真实实例化nextMark的fair law、停止历史独立和jointwaiting尾，不把原退出有限当核心输入。

实际统一build0、标准Lean --trust=0逐定理审计0，全部44named另专项审计通过，仅标准三公理，零新Lean warning。核心125theorem+1model旧审计沿用且8源hash重核，未冒称重编。

[专项1](audit/unrevealed-mark-stage-declarations-validation.json) · [专项2](audit/stopped-mark-slices-stage-declarations-validation.json) · [专项3](audit/stopped-fresh-mark-stage-declarations-validation.json) · [统一审计](audit/analysis-validation.json) · [方法账本](../research/followup/METHOD_LEDGER_2026-10-21.md)。独立AI审查不等于人类专家认证。

范围：已完成固定单site实际新mark及联合threshold identity，尚未单独声明任意Borel wait/Bool pair完整推前law，也未证明多site残余向量、完整未来mark字段、Poisson计数补偿或Dynkin。有限率代数、面积有界可积不能替代真实物理补偿；masked恒漂移2捷径仍无效，自含CMST/FSS核心尾与二次主定理仍缺。

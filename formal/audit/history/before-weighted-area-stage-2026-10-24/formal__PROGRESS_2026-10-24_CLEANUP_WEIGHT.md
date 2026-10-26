# 实际概率、清理总预算与零权出生层

原无限二维同步主定理τ(N)=Θ(N²)仍未完成。本阶段只对原时钟law下的真实辅助过程给出新的可用关系，不偷换同步时间或原exact-N量词。

## 已经真正闭合

PhysicalAreaTail：L≥40时，实际早退出事件包含于A_T≥L²/1600，因此P(exit≤T)≤E[A_T]/(L²/1600)。A是真实首次失保护后冻结的D内缺失面积，非负可积已证明；E[A_T]可代入真实clipped生成元时间积分。原clock灭绝CDF沿已有比较方向也不超过此界。没有输入面积矩界、退出有限性或核心恢复界；不是同步过程的尾界。

CumulativeCleanupBudget：每次严格前态仍有保护时才支付cleanup loss，所以包括首次导致失守的事件。真实逐事件周长预算、strict word前态、原identity标记重编号和真正可预测补偿给出∫₀ᵀ E[1保护·cleanupRate(U_{u−})]du≤perimeter(S)/2。实际clipped初态D的边界为8L+4，故对每个有限T，真实累计cleanup率积分≤4L+2。没有以补偿或预算为前提。

CleanupAreaTail：先证样本与时间均值可积，再拆真实Dynkin积分，得到E[A_T]≤∫₀ᵀE[冻结masked rawRate]du+4L+2，及相应早退出概率界。masked raw仍包含正的禁birth修正；没有丢正项或套常漂移2。

ForbiddenBirthControl：对任意S⊆实际clippedDomain，域外若有至少两个黑邻居，则该点必有norm1=L+2。w_L(x)=L+2−|x₁|−|x₂|在域内≥1，在这些域外可能birth点恰为0。精确加权质量和raw率代数因此给出实际masked与centered-square expanded weighted raw率严格相等。该结论不假设Shape或欲证率界，也不说明普通面积禁birth修正为0。

## 实际核验

分析201个证明模块、2653条辅助定理、202份分析源；核心125条定理及1模型、8源未变。合计210份正式源、2778条辅助定理与1个模型，完整公理输出2779项。最新分析统一构建和标准Lean --trust=0逐定理公理审计均退出0（2026-10-24T23:50:49.999919+08:00）；仅Classical.choice、Quot.sound、propext，无占位或自定义公理。核心沿用既有验收，8源指纹重新核对，本次未重编核心。

4新模块58theorem、72named，分别12、44、16项专项审计均actualbuild0/stdtrust0审计0，仅三个标准公理、零新Leanwarning。全部原工具链/依赖缓存沿用；独立AI只做AI复核，完整主定理与人类认证均不在此次范围。

[最终独立语义审查](../../physical-area-tail-independent-combined-review.md) · [统一验证JSON](../../analysis-validation.json) · [可复现有限计数](../../forbidden-birth-source-check.py)。原论文定义对照及五个有限例在[源核对](../../forbidden-birth-source-comparison.json)；它们不构成对原Theorem2的否定或全L计数的Lean证明。

## 下一阶段仍须实际证明

加权缺失面积的物理Dynkin和加权cleanup预算正在草稿中，失守时加权缺失至少Ω(L³)的真实阈值也正在草稿中；均不算本210正式源验收。核心候选是用四条单调轮廓的凸凹转角配对，证明weighted raw≤O(L)，配合上述已证零修正与cleanup预算，在T=cL²时得到真实小概率界。该weighted raw整体界尚未证明，不能作为最终输入。

另一路同步原过程二次上界、自含CMST/FSS剩余核心、两向时间比较和最终exact-N常数仍待闭合。
